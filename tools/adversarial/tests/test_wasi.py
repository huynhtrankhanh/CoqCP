"""WASI capability, resource, and cache-taint regressions."""
import errno
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import check as gate
from wasi_cache import Cache, key
from wasi_fs import Filesystem


class PortableArithmeticTests(unittest.TestCase):
    def test_solver_arithmetic_matches_native_zarith(self):
        import wasi_c_runtime
        if not wasi_c_runtime.SDK.is_dir():
            self.skipTest("Install the pinned WASI SDK first")
        program = r'''
let z n = Z.of_int n
let show xs = print_endline (String.concat "," (List.map Z.to_string xs))
let ration q =
 show [Q.num q; Q.den q];
 print_endline (Q.to_string q);
 Printf.printf "%Lx\n" (Int64.bits_of_float (Q.to_float q))
let () =
 for a = -30 to 30 do for b = -15 to 15 do
  let x,y = z a,z b in
  show [Z.(x land y); Z.(x lor y); Z.(x lxor y)];
  List.iter (fun spec -> print_endline (Z.format spec x)) ["%d";"%x";"%#x"];
  if b <> 0 then begin
   let q,r = Z.div_rem x y and e,s = Z.ediv_rem x y in
   show [q;r;e;s;Z.fdiv x y;Z.cdiv x y;Z.gcd x y;Z.lcm x y];
   let u=Q.make x y and v=Q.make (Z.succ y) (Z.succ (Z.abs x)) in
   List.iter ration [u;Q.add u v;Q.sub u v;Q.mul u v];
   if a <> 0 then ration (Q.inv u);
   if b <> -1 then ration (Q.div u v);
   show [Q.to_bigint u]
  end
 done done;
 List.iter (fun f -> ration (Q.of_float f))
  [0.;-0.;0.1;-0.1;1e100;-1e-100;Float.min_float;Float.next_after 0. 1.];
 let a=Z.of_string "12345678901234567890123456789012345678901234567890" in
 let b=Z.add (Z.pow (z 2) 89) (z 11) in
 show [Z.pow a 5;Z.(a asr 97);Z.((neg a) asr 97)];
 List.iter (fun a -> List.iter (fun b ->
  let q,r=Z.div_rem a b and e,s=Z.ediv_rem a b in
  show [q;r;e;s;Z.fdiv a b;Z.cdiv a b;Z.gcd a b;Z.lcm a b];
  ration (Q.make a b)) [b;Z.neg b]) [a;Z.neg a];
 List.iter (fun text -> show [Z.of_string text])
  ["0xff";"-0x80";"0b111_000";"0o123";"+123_456";"001";
   "0x1234abcd12345fffffffffffffffffffffffff"]
'''
        env = dict(os.environ, PATH=str(gate.TOOLCHAIN / "bin") + ":/usr/bin:/bin",
                   OCAMLPATH=str(gate.TOOLCHAIN / "lib"),
                   CAML_LD_LIBRARY_PATH=str(gate.TOOLCHAIN / "lib/stublibs"))
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "probe.ml").write_text(program)
            subprocess.run([gate.command("ocamlfind"), "ocamlc", "-package", "zarith", "-linkpkg",
                            "probe.ml", "-o", "native.bc"], env=env, cwd=root, check=True, capture_output=True)
            expected = subprocess.check_output([gate.command("ocamlrun"), str(root / "native.bc")], env=env)
            (root / "z.ml").write_bytes((gate.TOOLS / "wasi_z.ml").read_bytes())
            (root / "q.ml").write_bytes((gate.TOOLS / "wasi_q.ml").read_bytes())
            subprocess.run([gate.command("ocamlfind"), "ocamlc", "-compat-32", "-package", "num", "-linkpkg",
                            "z.ml", "q.ml", "probe.ml", "-o", "portable.bc"],
                           env=env, cwd=root, check=True, capture_output=True)
            wasi_c_runtime.compile_bytecode(gate, root / "portable.bc", root / "probe.wasm", env)
            with patch.object(gate, "WASI_BIN", root):
                limits = dict(gate.DEFAULT_LIMITS, fuel=5_000_000_000)
                sandbox = gate.make_sandbox(limits, runtime={"backend": "wasi", "fingerprint": "arithmetic-test"})
                try:
                    actual = sandbox.invoke("probe", ["probe"], {},
                                            time.monotonic() + limits["wall_seconds"])
                    self.assertEqual(actual["stdout"], expected)
                finally:
                    sandbox.close()


class FilesystemTests(unittest.TestCase):
    def test_readonly_authority_cannot_be_changed_by_rename(self):
        fs = Filesystem({"/input/secret": b"trusted"}, 1024, 1024)
        with self.assertRaises(OSError) as raised:
            fs.open("/input/secret", 0, 1 << 6, 0)
        self.assertEqual(raised.exception.errno, errno.EROFS)
        with self.assertRaises(OSError):
            fs.rename("/input/secret", "/work/secret")
        self.assertEqual(fs.nodes["/input/secret"].data, b"trusted")

    def test_unlinked_open_files_still_count_against_quota(self):
        fs = Filesystem({}, 100, 100)
        first = fs.open("/work/a", 1, 1 << 6, 0)
        fs.resize(fs.descriptors[first][0], 80)
        fs.unlink("/work/a")
        second = fs.open("/work/b", 1, 1 << 6, 0)
        with self.assertRaises(OSError) as raised:
            fs.resize(fs.descriptors[second][0], 30)
        self.assertEqual(raised.exception.errno, errno.ENOSPC)
        del fs.descriptors[first]
        fs.resize(fs.descriptors[second][0], 30)

    def test_directory_descriptor_cannot_escape_capability(self):
        fs = Filesystem({"/input/secret": b"trusted"}, 100, 100)
        fd = fs.open("/work", 2, 0, 0)
        for path in ["../input/secret", "/input/secret", "a/../../input/secret"]:
            with self.subTest(path=path), self.assertRaises(OSError):
                fs.path(fd, path)

    def test_immutable_bytes_are_shared_but_guest_nodes_are_fresh(self):
        original = bytes(bytearray(b"trusted"))
        a = Filesystem({"/input/a": original}, 100, 100)
        b = Filesystem({"/input/a": original}, 100, 100)
        self.assertIs(a.nodes["/input/a"].data, b.nodes["/input/a"].data)
        a.open("/work/taint", 1, 1 << 6, 0)
        self.assertNotIn("/work/taint", b.nodes)


class CacheTaintTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.cache = Cache(self.temporary.name, gate.read_regular, gate.encoded, gate.decoded, 1024)
        self.base = key({"source": "same", "toolchain": "same", "policy": "same"})

    def tearDown(self):
        self.temporary.cleanup()

    def test_changed_dependency_invalidates_subtree_but_unrelated_change_does_not(self):
        files = {"/work/A.vo": b"first", "/work/Unrelated.vo": b"other"}
        self.cache.put("compile", self.base, b"compiled", ["/work/A.vo"], files)
        self.assertEqual(self.cache.get("compile", self.base, files), b"compiled")
        unrelated = files | {"/work/Unrelated.vo": b"changed"}
        self.assertEqual(self.cache.get("compile", self.base, unrelated), b"compiled")
        self.assertIsNone(self.cache.get("compile", self.base, files | {"/work/A.vo": b"tainted"}))
        self.assertIsNone(self.cache.get("compile", self.base, {}))

    def test_newly_available_dependency_and_directory_membership_invalidate(self):
        for observation in ["/work/Optional.vo", "/work/"]:
            with self.subTest(observation=observation):
                self.cache.put("compile", self.base, b"compiled", [observation], {})
                self.assertIsNone(self.cache.get("compile", self.base, {"/work/Optional.vo": b"new"}))

    def test_toolchain_policy_limits_and_contract_are_separate_cache_domains(self):
        self.cache.put("kernel", self.base, b"checked")
        self.assertEqual(self.cache.get("kernel", self.base), b"checked")
        for changed in ["toolchain", "policy", "limits", "contract", "artifacts"]:
            self.assertIsNone(self.cache.get("kernel", key({changed: "changed"})))
        self.assertIsNone(self.cache.get("compile", self.base))

    def test_directory_entry_type_changes_invalidate(self):
        files = {"/work/A": b"file"}
        self.cache.put("compile", self.base, b"compiled", ["/work/"], files)
        self.assertIsNone(self.cache.get("compile", self.base, {"/work/A": None}))

    def test_metadata_observations_bind_type_size_and_existence(self):
        files = {"/inputs/A.v": b"one"}
        self.cache.put("compile", self.base, b"compiled", ["stat:/inputs/A.v"], files)
        self.assertEqual(self.cache.get("compile", self.base, {"/inputs/A.v": b"two"}), b"compiled")
        for changed in [{}, {"/inputs/A.v": None}, {"/inputs/A.v": b"longer"}]:
            self.assertIsNone(self.cache.get("compile", self.base, changed))

    def test_corrupted_or_duplicate_field_cache_entry_is_a_miss(self):
        self.cache.put("compile", self.base, b"compiled", [], {})
        path = next(Path(self.temporary.name).rglob("*.json"))
        data = json.loads(path.read_bytes())
        data["sha256"] = "wrong"
        path.write_bytes(gate.encoded(data))
        self.assertIsNone(self.cache.get("compile", self.base, {}))
        path.write_bytes(b'{"format":1,"format":1}')
        self.assertIsNone(self.cache.get("compile", self.base, {}))


class WasiHostTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.module_patch = patch.object(gate, "WASI_BIN", self.root)
        self.module_patch.start()
        self.limits = dict(gate.DEFAULT_LIMITS)
        self.sandbox = gate.make_sandbox(self.limits,
                                        runtime={"version": gate.VERSION, "fingerprint": "test", "backend": "wasi"})

    def tearDown(self):
        self.sandbox.close()
        self.module_patch.stop()
        self.temporary.cleanup()

    def execute(self, wat, files=None):
        (self.root / "probe.wasm").write_text(wat)
        return self.sandbox.invoke("probe", ["probe"], files or {},
                                   time.monotonic() + self.limits["wall_seconds"])

    def test_no_network_process_or_unknown_host_imports(self):
        for namespace, name in [("wasi_snapshot_preview1", "sock_open"),
                                ("env", "exec"), ("wasi_snapshot_preview1", "path_symlink")]:
            with self.subTest(name=name), self.assertRaisesRegex(gate.Rejected, "Unapproved guest import"):
                self.execute(f'(module (import "{namespace}" "{name}" (func)) '
                             '(memory (export "memory") 1) (func (export "_start")))')

    def test_fuel_exhaustion(self):
        self.limits["fuel"] = 1000
        with self.assertRaisesRegex(gate.Rejected, "fuel"):
            self.execute('(module (memory (export "memory") 1) '
                         '(func (export "_start") (loop $again (br $again))))')

    def test_wall_limit_kills_host(self):
        self.limits["wall_seconds"] = 1
        self.limits["fuel"] = 1_000_000_000_000
        with self.assertRaisesRegex(gate.Rejected, "wall time"):
            self.execute('(module (memory (export "memory") 1) '
                         '(func (export "_start") (loop $again (br $again))))')
        self.assertIsNone(self.sandbox.process)

    def test_linear_memory_limit(self):
        self.limits["memory_mib"] = 256
        result = self.execute('(module (memory (export "memory") 1) '
                              '(func (export "_start") '
                              '(if (i32.ne (memory.grow (i32.const 8192)) (i32.const -1)) '
                              '(then unreachable))))')
        self.assertEqual(result["stdout"], b"")

    def test_original_ocaml_gc_reclaims_cycles_with_retained_data(self):
        import wasi_c_runtime
        program = self.root / "gc_probe.ml"
        program.write_text('''type node = { mutable next : node option }
let () =
 let keep = Array.init 2 (fun _ -> Array.make 4000000 7) in
 for _ = 1 to 1000000 do
  let n = { next=None } in n.next <- Some n
 done;
 Gc.full_major ();
 assert (Array.length keep = 2 && keep.(1).(3999999) = 7);
 print_endline "gc-ok"
''')
        env = dict(os.environ, PATH=str(gate.TOOLCHAIN / "bin") + ":/usr/bin:/bin",
                   OCAMLPATH=str(gate.TOOLCHAIN / "lib"))
        bytecode = self.root / "gc_probe.bc"
        subprocess.run([gate.command("ocamlc"), "-compat-32", "-o", str(bytecode),
                        str(program)], env=env, check=True, capture_output=True)
        wasi_c_runtime.compile_bytecode(gate, bytecode, self.root / "probe.wasm", env)
        self.limits.update(memory_mib=256, fuel=10_000_000_000)
        result = self.sandbox.invoke("probe", ["probe"], {}, time.monotonic() + 120)
        self.assertEqual(result["stdout"], b"gc-ok\n")

    def test_readonly_input_through_wasi_import(self):
        wat = '''(module
          (import "wasi_snapshot_preview1" "path_open"
            (func $open (param i32 i32 i32 i32 i32 i64 i64 i32 i32) (result i32)))
          (import "wasi_snapshot_preview1" "fd_write" (func $write (param i32 i32 i32 i32) (result i32)))
          (memory (export "memory") 1)
          (data (i32.const 0) "\\40\\00\\00\\00\\01\\00\\00\\00")
          (data (i32.const 16) "input/secret")
          (func (export "_start")
            (i32.store8 (i32.const 64)
              (call $open (i32.const 3) (i32.const 0) (i32.const 16) (i32.const 12)
                (i32.const 0) (i64.const 64) (i64.const 0) (i32.const 0) (i32.const 80)))
            (drop (call $write (i32.const 1) (i32.const 0) (i32.const 1) (i32.const 96)))))'''
        result = self.execute(wat, {"/input/secret": b"trusted"})
        self.assertEqual(result["stdout"], bytes([69]))
        self.assertIn("stat:/input/secret", result["observed"])
        self.assertNotIn("/input/secret", result["observed"])

    def test_file_reads_record_contents_as_well_as_metadata(self):
        wat = '''(module
          (import "wasi_snapshot_preview1" "path_open"
            (func $open (param i32 i32 i32 i32 i32 i64 i64 i32 i32) (result i32)))
          (import "wasi_snapshot_preview1" "fd_read" (func $read (param i32 i32 i32 i32) (result i32)))
          (import "wasi_snapshot_preview1" "fd_write" (func $write (param i32 i32 i32 i32) (result i32)))
          (memory (export "memory") 1)
          (data (i32.const 0) "\\80\\00\\00\\00\\03\\00\\00\\00")
          (data (i32.const 16) "input/A")
          (func (export "_start")
            (drop (call $open (i32.const 3) (i32.const 0) (i32.const 16) (i32.const 7)
              (i32.const 0) (i64.const 2) (i64.const 0) (i32.const 0) (i32.const 100)))
            (drop (call $read (i32.load (i32.const 100)) (i32.const 0) (i32.const 1) (i32.const 104)))
            (drop (call $write (i32.const 1) (i32.const 0) (i32.const 1) (i32.const 104)))))'''
        result = self.execute(wat, {"/input/A": b"one"})
        self.assertEqual(result["stdout"], b"one")
        self.assertIn("stat:/input/A", result["observed"])
        self.assertIn("/input/A", result["observed"])

    def test_fresh_guest_heap_in_reused_host(self):
        wat = '''(module
          (import "wasi_snapshot_preview1" "fd_write" (func $write (param i32 i32 i32 i32) (result i32)))
          (memory (export "memory") 1)
          (data (i32.const 0) "\\10\\00\\00\\00\\01\\00\\00\\00")
          (func (export "_start")
            (i32.store8 (i32.const 16) (i32.add (i32.load8_u (i32.const 16)) (i32.const 1)))
            (drop (call $write (i32.const 1) (i32.const 0) (i32.const 1) (i32.const 32)))))'''
        first = self.execute(wat)["stdout"]
        second = self.execute(wat)["stdout"]
        self.assertEqual(first, b"\x01")
        self.assertEqual(second, b"\x01")

    def test_positional_read_records_taint_and_preserves_offset(self):
        wat = r'''(module
          (import "wasi_snapshot_preview1" "path_open"
            (func $open (param i32 i32 i32 i32 i32 i64 i64 i32 i32) (result i32)))
          (import "wasi_snapshot_preview1" "fd_pread"
            (func $pread (param i32 i32 i32 i64 i32) (result i32)))
          (import "wasi_snapshot_preview1" "fd_read"
            (func $read (param i32 i32 i32 i32) (result i32)))
          (import "wasi_snapshot_preview1" "fd_tell" (func $tell (param i32 i32) (result i32)))
          (import "wasi_snapshot_preview1" "fd_write" (func $write (param i32 i32 i32 i32) (result i32)))
          (memory (export "memory") 1)
          (data (i32.const 0) "\80\00\00\00\03\00\00\00\84\00\00\00\03\00\00\00")
          (data (i32.const 16) "input/A")
          (func (export "_start") (local $fd i32)
            (drop (call $open (i32.const 3) (i32.const 0) (i32.const 16) (i32.const 7)
              (i32.const 0) (i64.const 6) (i64.const 0) (i32.const 0) (i32.const 100)))
            (local.set $fd (i32.load (i32.const 100)))
            (drop (call $pread (local.get $fd) (i32.const 0) (i32.const 1) (i64.const 4) (i32.const 104)))
            (drop (call $tell (local.get $fd) (i32.const 108)))
            (if (i64.ne (i64.load (i32.const 108)) (i64.const 0)) (then unreachable))
            (drop (call $read (local.get $fd) (i32.const 8) (i32.const 1) (i32.const 104)))
            (drop (call $write (i32.const 1) (i32.const 0) (i32.const 2) (i32.const 104)))))'''
        result = self.execute(wat, {"/input/A": b"one two"})
        self.assertEqual(result["stdout"], b"twoone")
        self.assertIn("/input/A", result["observed"])
        self.assertIn("stat:/input/A", result["observed"])

    def test_readlink_and_poll_do_not_grant_authority(self):
        wat = r'''(module
          (import "wasi_snapshot_preview1" "path_readlink"
            (func $link (param i32 i32 i32 i32 i32 i32) (result i32)))
          (import "wasi_snapshot_preview1" "poll_oneoff"
            (func $poll (param i32 i32 i32 i32) (result i32)))
          (memory (export "memory") 1)
          (data (i32.const 16) "input/A")
          (func (export "_start")
            (if (i32.ne (call $link (i32.const 3) (i32.const 16) (i32.const 7)
              (i32.const 64) (i32.const 8) (i32.const 96)) (i32.const 28)) (then unreachable))
            (if (i32.ne (call $poll (i32.const 64) (i32.const 80)
              (i32.const 1) (i32.const 96)) (i32.const 52)) (then unreachable))))'''
        result = self.execute(wat, {"/input/A": b"trusted"})
        self.assertIn("stat:/input/A", result["observed"])
        self.assertNotIn("/input/A", result["observed"])

    def test_missing_host_fails_closed(self):
        self.sandbox.host = self.root / "missing-host"
        with self.assertRaisesRegex(gate.Rejected, "No safe condition"):
            self.execute('(module (memory (export "memory") 1) (func (export "_start")))')

    def test_output_limit(self):
        # Two writes of 600 KiB exceed the 1 MiB output quota.
        wat = '''(module
          (import "wasi_snapshot_preview1" "fd_write" (func $write (param i32 i32 i32 i32) (result i32)))
          (memory (export "memory") 16)
          (data (i32.const 0) "\\10\\00\\00\\00\\00\\60\\09\\00")
          (func (export "_start")
            (drop (call $write (i32.const 1) (i32.const 0) (i32.const 1) (i32.const 8)))
            (drop (call $write (i32.const 1) (i32.const 0) (i32.const 1) (i32.const 8)))))'''
        with self.assertRaisesRegex(gate.Rejected, "output limit"):
            self.execute(wat)


class MarshalSharingTests(unittest.TestCase):
    def test_cycles_identity_and_large_shared_graph_interoperate_with_native(self):
        import wasi_c_runtime
        if not wasi_c_runtime.SDK.is_dir():
            self.skipTest("Install the pinned WASI SDK first")
        program = '''
type node = { value : int; mutable next : node option }
let () =
  let leaf = [|1; 2|] in
  let distinct = Array.copy leaf in
  let cycle = { value = 7; next = None } in
  cycle.next <- Some cycle;
  let graph = Array.init 20000 (fun i -> { value = i; next = Some cycle }) in
  let equal_nodes = Array.init 10000 (fun _ -> Array.copy leaf) in
  (try ignore (Marshal.to_buffer (Bytes.create 24) 0 24 (leaf, graph) []);
       assert false with Failure _ -> ());
  assert (leaf.(0) = 1 && Array.length leaf = 2);
  assert (Obj.tag (Obj.repr leaf) = 0 && Obj.tag (Obj.repr graph) = 0);
  (try ignore (Marshal.to_buffer (Bytes.create 24) 0 24 (leaf, graph) []);
       assert false with Failure _ -> ());
  assert (leaf.(0) = 1 && graph.(0).value = 0);
  assert (Obj.tag (Obj.repr leaf) = 0 && Obj.tag (Obj.repr graph.(0)) = 0);
  let bytes = if Array.length Sys.argv = 1 then
    Marshal.to_string (leaf, leaf, distinct, cycle, graph, equal_nodes) []
    else if Sys.argv.(1) = "-" then In_channel.input_all stdin
    else In_channel.with_open_bin Sys.argv.(1) In_channel.input_all in
  assert (Obj.tag (Obj.repr leaf) = 0 && Obj.tag (Obj.repr cycle) = 0);
  let a, b, c, d, e, f = Marshal.from_string bytes 0 in
  assert (a == b && a != c && a = c);
  assert (match d.next with Some n -> n == d | None -> false);
  Array.iteri (fun i n -> assert (n.value = i && n != d);
    assert (match n.next with Some m -> m == d | None -> false)) e;
  Array.iteri (fun i n -> assert (n = a && n != a);
    if i > 0 then assert (n != f.(i-1))) f;
  print_string (if Array.length Sys.argv = 1 then bytes else "sharing-ok\\n")
'''
        env = dict(os.environ, PATH=str(gate.TOOLCHAIN / "bin") + ":/usr/bin:/bin",
                   OCAMLPATH=str(gate.TOOLCHAIN / "lib"))
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "probe.ml").write_text(program)
            subprocess.run([gate.command("ocamlc"), "-compat-32", "-o", str(root / "probe.bc"),
                            str(root / "probe.ml")], env=env, check=True, capture_output=True)
            expected = subprocess.check_output([gate.command("ocamlrun"),
                                                str(root / "probe.bc")], env=env)
            wasi_c_runtime.compile_bytecode(gate, root / "probe.bc", root / "probe.wasm", env)
            with patch.object(gate, "WASI_BIN", root):
                limits = dict(gate.DEFAULT_LIMITS, fuel=1_000_000_000)
                sandbox = gate.make_sandbox(limits, runtime={"backend": "wasi", "fingerprint": "sharing-test"})
                try:
                    actual = sandbox.invoke("probe", ["probe"], {},
                                            time.monotonic() + limits["wall_seconds"])
                    decoded = subprocess.run([gate.command("ocamlrun"), str(root / "probe.bc"), "-"],
                                             env=env, input=actual["stdout"], check=True, capture_output=True)
                    self.assertEqual(decoded.stdout, b"sharing-ok\n")
                    decoded = sandbox.invoke("probe", ["probe", "/input/native"],
                                             {"/input/native": expected},
                                             time.monotonic() + limits["wall_seconds"])
                    self.assertEqual(decoded["stdout"], b"sharing-ok\n")
                finally:
                    sandbox.close()


if __name__ == "__main__":
    unittest.main()
