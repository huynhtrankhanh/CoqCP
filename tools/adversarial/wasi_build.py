"""Build Rocq's portable OCaml implementation for WASI, outside the native switch."""
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile


def replace(path, old, new):
    text = path.read_text()
    if old not in text:
        raise RuntimeError(f"Pinned Rocq source changed: {path}")
    path.write_text(text.replace(old, new))


def build(gate):
    fingerprints = gate.build_fingerprints("wasi")
    tools, chain = gate.TOOLS, gate.TOOLCHAIN
    portable = Path("/opt/rocq/wasi/rocq-source")
    source = chain / ".opam-switch/sources/rocq-runtime.9.3.0"
    if not source.is_dir():
        raise RuntimeError("Pinned Rocq sources missing; run tools/install-wasi.sh")
    # Dune retains its build cache across changes to evaluator entry points.
    if not portable.is_dir():
        shutil.copytree(source, portable)
    dune = portable / "kernel/dune"
    if "%{ocaml-config:int_size}" in dune.read_text():
        replace(dune, "uint63_%{ocaml-config:int_size}.ml", "uint63_31.ml")
        replace(dune, "float64_%{ocaml-config:int_size}.ml", "float64_31.ml")
    uint = portable / "kernel/uint63_31.ml"
    if "let _ = assert (Sys.word_size = 32)" in uint.read_text():
        replace(uint, "let _ = assert (Sys.word_size = 32)",
                "(* Host compilation; runtime arithmetic uses 31-bit OCaml ints. *)")
    for name in ["float64_31.ml", "float64_common.ml"]:
        shutil.copyfile(source / "kernel" / name, portable / "kernel" / name)
    # These unsigned hash masks are target-machine ints. Runtime conversion
    # retains the upstream 32-bit bit pattern without a 64-bit DATA literal.
    for name in ["plugins/ltac/tacentries.ml", "plugins/micromega/persistent_cache.ml"]:
        path = portable / name
        path.write_text((source / name).read_text().replace(
            "0x7FFFFFFF", "(Int32.to_int Int32.max_int)"))
    root_dune = portable / "dune"
    root_dune.write_text((source / "dune").read_text().replace(
        "(release (flags :standard -g)",
        "(release (flags :standard -g) (ocamlc_flags :standard -compat-32)"))
    arithmetic = portable / "coqcp_wasi_arithmetic"
    arithmetic.mkdir(exist_ok=True)
    (arithmetic / "dune").write_text('(library (name coqcp_wasi_arithmetic) '
                                    '(public_name rocq-runtime.wasi_arithmetic) (wrapped false) '
                                    '(libraries num))\n')
    shutil.copyfile(tools / "wasi_z.ml", arithmetic / "z.ml")
    shutil.copyfile(tools / "wasi_q.ml", arithmetic / "q.ml")
    (arithmetic / "big_int_Z.ml").write_text('include Big_int\n')
    for path in portable.rglob("dune"):
        if "_build" not in path.parts:
            path.write_text(re.sub(r'\bzarith\b', 'coqcp_wasi_arithmetic', path.read_text()))
    # All approved plugins are linked into this executable. Resolve declarations
    # from that fixed set, without consulting native findlib archives or Dynlink.
    mltop = portable / "vernac/mltop.ml"
    original = (source / "vernac/mltop.ml").read_text()
    start, end = original.index("  let add_deps plugins ="), original.index("  let pp = function", original.index("  let add_deps plugins ="))
    static = '''  let add_deps plugins =
    List.iter (fun ({lib} as plugin) ->
      if not (is_loaded plugin) then
        CErrors.user_err Pp.(str ("Disabled in the submission compiler: dynamic ML plugin " ^ lib))) plugins;
    List.map (fun plugin -> false, plugin) plugins

  (* The coordinator binds every .vo to the complete executable fingerprint.
     These digests track declaration names; no native archive is consulted. *)
  let digest {lib} = [Digest.string lib]

'''
    mltop.write_text(original[:start] + static + original[end:])
    # -dyndep no affects printing, but upstream still resolves each declaration
    # through native findlib first. The portable compiler has a fixed plugin
    # set, so its dependency scanner must omit archive expansion entirely.
    makefile = portable / "tools/coqdep/lib/makefile.ml"
    original = (source / "tools/coqdep/lib/makefile.ml").read_text()
    start = original.index("let declare_ml_to_file ")
    end = original.index("let print_dep ", start)
    makefile.write_text(original[:start] +
        'let declare_ml_to_file _file (_decl : string) = ([], [])\n\n' + original[end:])
    entry = portable / "coqcp_wasi_gate"
    entry.mkdir(exist_ok=True)
    for name in ["spec_check.ml", "compile_wasi.ml", "dep_wasi.ml"]:
        shutil.copyfile(tools / name, entry / name)
    import wasi_checker_cache
    wasi_checker_cache.install(tools, source, portable)
    (entry / "ci_policy.ml").write_text("let allowed_axioms = [" +
        "; ".join(json.dumps(name) for name in gate.trusted_axioms()) + "]\n" +
        "let indices_not_mattering = [" +
        "; ".join(json.dumps(name) for name in gate.trusted_inductives()) + "]\n")
    (entry / "wasi_plugins.ml").write_text("let allowed = [" +
        "; ".join(json.dumps(name) for name in gate.compiler_plugins()) + "]\n")
    (entry / "dune").write_text(
        '(executable (name spec_check) (modules spec_check ci_policy) (modes byte) '
        '(libraries rocq-runtime.checklib))\n'
        '(executable (name compile_wasi) (modules compile_wasi wasi_plugins) (modes byte) '
        '(link_flags -linkall) (libraries rocq-runtime.toplevel ' +
        ' '.join(gate.compiler_plugins()) + '))\n'
        '(executable (name dep_wasi) (modules dep_wasi) (modes byte) '
        '(libraries rocq-runtime.coqdeplib))\n')
    env = dict(os.environ, PATH=str(chain / "bin") + ":/usr/bin:/bin",
               OCAMLPATH=str(chain / "lib"), OCAMLFIND_CONF=str(chain / "lib/findlib.conf"),
               CAML_LD_LIBRARY_PATH=str(chain / "lib/stublibs"))
    subprocess.run([str(chain / "bin/dune"), "exec", "--root", str(portable),
                    "--profile=release", "--", "tools/configure/configure.exe", "-quiet",
                    "-relocatable", "-bytecode-compiler", "yes", "-native-compiler", "no"],
                   env=env, cwd=portable, check=True)
    config = portable / "config/coq_config.ml"
    config.chmod(0o644)
    config.write_text(re.sub(r"let gc_ramp_up f = .*", "let gc_ramp_up f = f ()", config.read_text()))
    if "let bytecode_compiler = true" not in config.read_text():
        raise RuntimeError("The WASI runtime requires Rocq VM support")
    targets = ["coqcp_wasi_gate/" + name + ".bc" for name in
               ["spec_check", "compile_wasi", "dep_wasi"]]
    subprocess.run([str(chain / "bin/dune"), "build", "--root", str(portable),
                    "--profile=release", "-j2", *targets], env=env, cwd=portable, check=True)
    gate.WASI_BIN.mkdir(parents=True, exist_ok=True)
    import wasi_c_runtime
    with tempfile.TemporaryDirectory(prefix="wasi-build-", dir=gate.WASI_BIN.parent) as temporary:
        work = Path(temporary)
        wasi_c_runtime.build(gate, portable, env, work)
        for binary in ["spec-check", "compile-safe", "rocq-dep"]:
            os.replace(work / (binary + ".wasm"), gate.WASI_BIN / (binary + ".wasm"))
            subprocess.run(["/opt/rocq/wasi/host/coqcp-wasi-host", "--precompile",
                            str(gate.WASI_BIN / (binary + ".wasm")),
                            str(work / (binary + ".cwasm"))], check=True)
            os.replace(work / (binary + ".cwasm"), gate.WASI_BIN / (binary + ".cwasm"))
    (gate.WASI_BIN / "sources.json").write_bytes(gate.encoded(fingerprints))
