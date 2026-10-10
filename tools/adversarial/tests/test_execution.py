"""Exercise actual native-code loading, not just forbidden source spellings."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from test_check import gate, VALID, fixture_cache


class CompilerExecutionTests(unittest.TestCase):
    backend = "wasi"

    @classmethod
    def setUpClass(cls):
        gate.ensure_built(cls.backend)
        cls.temporary = tempfile.TemporaryDirectory(prefix="coqcp-execution-tests-")
        cls.root = Path(cls.temporary.name)
        cls.runtime = gate.toolchain(cls.backend)
        # Independent checking includes the imported tactic-library closure.
        cls.sandbox = gate.make_sandbox(dict(gate.DEFAULT_LIMITS, cpu_seconds=600,
                                        wall_seconds=1200, memory_mib=4096,
                                        fuel=2_000_000_000_000), cls.backend,
                                        runtime=cls.runtime, cache_directory=fixture_cache(cls.root))
        cls.bundle = cls.root / "bundle"
        cls.spec_id = gate.prepare(gate.REPO / "verification/increment/spec/Spec.v",
                                  cls.bundle, cls.runtime, cls.sandbox, [])
        if cls.backend == "wasi":
            return
        cls.plugins = cls.root / "plugins"
        attack = cls.plugins / "coqcp_attack"
        attack.mkdir(parents=True)
        (attack / "payload.ml").write_text('''let () =
  let out = open_out "/work/plugin-executed" in
  output_string out "arbitrary native payload";
  close_out out
''')
        (attack / "META").write_text('''version = "test"
description = "Regression payload, never approved for submission compilation"
plugin(native) = "payload.cmxs"
''')
        cls.build_env = dict(os.environ,
            PATH=str(gate.TOOLCHAIN / "bin") + ":/usr/bin:/bin",
            OCAMLPATH=str(gate.TOOLCHAIN / "lib"),
            OCAMLFIND_CONF=str(gate.TOOLCHAIN / "lib/findlib.conf"))
        cls.build(["-shared", "-o", str(attack / "payload.cmxs"), "payload.ml"], attack)

        # Test the irreversible OS filter independently of Mltop. A native
        # loader or external command must remain blocked if it bypasses Mltop.
        probe = cls.root / "probe"
        probe.mkdir()
        shutil.copyfile(gate.TOOLS / "compile_lockdown.c", probe / "compile_lockdown.c")
        # Keep the C object separate from the one ocamlopt emits for probe.ml.
        (probe / "probe_stubs.c").write_text(r'''
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <sys/mman.h>
#include <unistd.h>
#include <caml/mlvalues.h>
CAMLprim value test_executable_memory(value unit) {
  (void)unit;
  void *mem = mmap(NULL, 4096, PROT_READ | PROT_WRITE,
                  MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if (mem == MAP_FAILED) return Val_false;
  int result = mprotect(mem, 4096, PROT_READ | PROT_EXEC);
  int denied = result == -1 && errno == EPERM;
  munmap(mem, 4096);
  mem = mmap(NULL, 4096, PROT_READ | PROT_EXEC,
             MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  denied &= mem == MAP_FAILED && errno == EPERM;
  if (mem != MAP_FAILED) munmap(mem, 4096);
  return Val_bool(denied);
}
CAMLprim value test_execveat(value unit) {
  (void)unit;
  int fd = open("/usr/bin/true", O_RDONLY);
  if (fd < 0) return Val_false;
  char *argv[] = {"true", NULL};
  char *env[] = {NULL};
  int result = execveat(fd, "", argv, env, AT_EMPTY_PATH);
  int denied = result == -1 && errno == EPERM;
  close(fd);
  return Val_bool(denied);
}
''')
        (probe / "probe.ml").write_text('''
external lockdown : unit -> unit = "coqcp_compile_lockdown"
external executable_memory_blocked : unit -> bool = "test_executable_memory"
external execveat_blocked : unit -> bool = "test_execveat"
let () =
  (* A thread started before lockdown must also receive the filter. *)
  let ready = ref false in
  let thread = Thread.create (fun () ->
    while not !ready do Thread.delay 0.01 done;
    assert (executable_memory_blocked ());
    assert (execveat_blocked ())) () in
  lockdown ();
  ready := true;
  Thread.join thread;
  assert (executable_memory_blocked ());
  assert (execveat_blocked ());
  (try Unix.execv "/usr/bin/true" [|"true"|]; assert false
   with Unix.Unix_error (Unix.EPERM, _, _) -> ());
  (try Dynlink.loadfile "/plugins/coqcp_attack/payload.cmxs"; assert false
   with Dynlink.Error _ -> ());
  assert (not (Sys.file_exists "/work/plugin-executed"));
  print_endline "locked"
''')
        cls.build(["-c", "compile_lockdown.c"], probe)
        cls.build(["-c", "probe_stubs.c"], probe)
        cls.build(["-thread", "-linkpkg", "-package", "dynlink,unix,threads",
                   "-o", "probe", "compile_lockdown.o", "probe_stubs.o", "probe.ml",
                   "-cclib", "-lseccomp"], probe)
        cls.probe = probe / "probe"

    @classmethod
    def build(cls, flags, directory):
        result = subprocess.run([gate.command("ocamlfind"), "ocamlopt", *flags],
                                cwd=directory, env=cls.build_env, capture_output=True)
        if result.returncode:
            raise RuntimeError("Native regression fixture build failed:\n" +
                               result.stderr.decode("utf-8", errors="replace"))

    @classmethod
    def tearDownClass(cls):
        if hasattr(cls.sandbox, "close"):
            cls.sandbox.close()
        cls.temporary.cleanup()

    def evaluate(self, source, extra=None, *, accepted=False,
                 reason="Disabled in the submission compiler: dynamic ML plugin"):
        with tempfile.TemporaryDirectory(dir=self.root) as temporary:
            root = Path(temporary)
            submission = root / "submission"
            submission.mkdir()
            (submission / "Candidate.v").write_text(source)
            for name, data in (extra or {}).items():
                (submission / name).write_text(data)
            report = gate.evaluate(self.bundle, self.spec_id, submission, root / "result",
                                   self.runtime, self.sandbox)
            self.assertEqual(report["status"], "accepted" if accepted else "rejected", report)
            if not accepted:
                self.assertEqual(report["stage"], "compilation", report)
                self.assertIn(reason, report["reason"])
            return report

    def test_direct_unapproved_plugin(self):
        self.evaluate('Declare ML Module "rocq-runtime.plugins.extraction".\n' + VALID)

    def test_plugin_loaded_by_require(self):
        self.evaluate("From Corelib Require Import extraction.Extraction.\n" + VALID,
                      reason="Unable to locate library" if self.backend == "wasi" else
                      "Disabled in the submission compiler: dynamic ML plugin")

    def test_plugin_in_loaded_source(self):
        self.evaluate('Load "/inputs/Payload.v".\n' + VALID,
                      {"Payload.v": 'Declare ML Module "rocq-runtime.plugins.extraction".\n'})

    def test_comments_and_command_wrappers_do_not_bypass_loader(self):
        self.evaluate('Time Declare (* nested (* comment *) *) ML Module\n'
                      '"rocq-runtime.plugins.extraction".\n' + VALID)

    def test_expected_failure_cannot_run_plugin(self):
        self.evaluate('Fail Declare ML Module "rocq-runtime.plugins.extraction".\n' + VALID,
                      accepted=True)

    def test_approved_static_tactics_and_vm_compute(self):
        self.evaluate('From Stdlib Require Import Lia.\n'
                      'Declare ML Module "rocq-runtime.plugins.micromega".\n'
                      'Goal 2 + 2 = 4. vm_compute. reflexivity. Qed.\n'
                      'Goal forall n : nat, n + 1 > n. intros. lia. Qed.\n' + VALID,
                      accepted=True)

    def test_real_native_payload_runs_in_stock_compiler_and_is_blocked_in_safe_compiler(self):
        if self.backend != "bubblewrap":
            self.skipTest("Native executable payload fixture")
        with tempfile.TemporaryDirectory(dir=self.root) as temporary:
            inputs = Path(temporary)
            (inputs / "Candidate.v").write_text('Declare ML Module "coqcp_attack".\n')
            driver = r'''
import json, pathlib, subprocess
prefix = ['/tool/sandbox-exec', '60', '2048', '64']
flags = ['-coqlib', COQLIB, '-q', '-native-compiler', 'no', '-async-proofs', 'off',
         '-I', '/plugins', '-o', '/work/Candidate.vo', '/inputs/Candidate.v']
marker = pathlib.Path('/work/plugin-executed')
stock = subprocess.run(prefix + [ROCQ, 'compile'] + flags, capture_output=True)
assert stock.returncode == 0, stock.stderr
assert marker.read_text() == 'arbitrary native payload'
marker.unlink()
safe = subprocess.run(prefix + ['/tool/compile-safe'] + flags, capture_output=True)
assert safe.returncode != 0
assert b'Disabled in the submission compiler: dynamic ML plugin coqcp_attack' in safe.stderr, safe.stderr
assert not marker.exists()
print('payload-blocked')
'''.replace("COQLIB", repr(self.runtime["coqlib"])).replace("ROCQ", repr(self.runtime["rocq"]))
            result = self.sandbox.run(["/usr/bin/python3", "-I", "-c", driver],
                                     [(inputs, "/inputs"), (self.plugins, "/plugins")],
                                     compiler_worker=True)
            self.assertEqual(result, b"payload-blocked\n")

    def test_lockdown_blocks_exec_and_executable_memory_in_all_threads(self):
        if self.backend != "bubblewrap":
            self.skipTest("Native executable memory and OS thread restrictions")
        result = self.sandbox.run(["/probe"],
                                 [(self.probe, "/probe"), (self.plugins, "/plugins")])
        self.assertEqual(result, b"locked\n")


@unittest.skipUnless(os.environ.get("COQCP_TEST_BUBBLEWRAP") == "1",
                     "Optional native backend; set COQCP_TEST_BUBBLEWRAP=1 to test")
class NativeCompilerExecutionTests(CompilerExecutionTests):
    backend = "bubblewrap"


if __name__ == "__main__":
    unittest.main()
