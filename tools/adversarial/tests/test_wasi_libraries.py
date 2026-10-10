"""Trusted compilation cache behavior, with a small deterministic compiler."""
import contextlib
import io
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import check
from wasi_cache import Cache, hash_bytes, key
import wasi_libraries


class TrustedLibraryCacheTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        root = Path(self.temporary.name)
        self.coqlib = root / "toolchain/lib/coq"
        (self.coqlib / "user-contrib").mkdir(parents=True)
        self.boot = self.coqlib / "theories/Init/Prelude.v"
        self.source = root / "repo/theories/Example.v"
        for path, text in [(self.boot, "boot"), (self.source, "example")]:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        self.runtime = root / "runtime"
        self.runtime.mkdir()
        (self.runtime / "compile-safe.wasm").write_bytes(b"compiler")
        self.host = {"host": {"executable": "host"}, "wasi_host.py": "bindings",
                     "wasi_fs.py": "filesystem", "dep_wasi.ml": "scanner"}
        self.gate = SimpleNamespace(TOOLCHAIN=root / "toolchain", REPO=root / "repo",
            TOOLS=check.TOOLS, WASI_BIN=self.runtime, WASI_LIB=root / "libraries",
            DEFAULT_LIMITS=check.DEFAULT_LIMITS, Rejected=check.Rejected,
            read_regular=check.read_regular, digest=check.digest,
            encoded=check.encoded, decoded=check.decoded,
            command=lambda _: "rocq", compiler_plugins=lambda: [],
            project_layout=lambda: ([("theories", "CoqCP")], [Path("theories/Example.v")]),
            build_fingerprints=lambda _: self.host)
        self.compilations = []
        self.inherited = {}
        self.snapshots = []
        self.dependencies = {}
        self.core_dependencies = {}
        owner = self

        class Sandbox:
            process = None

            def __init__(self, gate, limits, **kwargs):
                self.cache = Cache(kwargs["cache_directory"], gate.read_regular,
                                   gate.encoded, gate.decoded, 1024)

            def invoke(self, _module, args, files, _deadline, _directories, inherited):
                source = args[-1]
                owner.compilations.append(source)
                owner.inherited[source] = {path for path in inherited if path.endswith(".vo")}
                owner.snapshots.append(dict(files))
                observed = [source, *inherited]
                payload = hash_bytes(b"".join((files | inherited)[name]
                                             for name in sorted(observed))).encode()
                return {"files": {args[args.index("-o") + 1]: payload}, "observed": observed}

            def close(self):
                pass

        def dependencies(args, **_kwargs):
            if "-where" in args:
                return str(self.coqlib).encode()
            sources = [arg for arg in args if arg.endswith(".v")]
            if "-sort" in args:
                return " ".join(sorted(sources)).encode()
            overrides = self.core_dependencies if args.count("-R") == 1 else self.dependencies
            return "\n".join(str(Path(name).with_suffix(".vo")) + ": " +
                             " ".join([name, *overrides.get(name, [])])
                             for name in sources).encode()

        self.compiler_patch = patch.object(wasi_libraries, "WasiSandbox", Sandbox)
        self.scanner_patch = patch.object(wasi_libraries.subprocess, "check_output", dependencies)
        self.compiler_patch.start()
        self.scanner_patch.start()
        self.addCleanup(self.compiler_patch.stop)
        self.addCleanup(self.scanner_patch.stop)

    def build(self):
        with contextlib.redirect_stdout(io.StringIO()):
            wasi_libraries.build(self.gate)

    def test_scanner_change_reuses_compilation_but_compiler_and_host_changes_do_not(self):
        self.build()
        self.assertEqual(len(self.compilations), 2)
        self.host["dep_wasi.ml"] = "different scanner"
        (self.runtime / "rocq-dep.wasm").write_bytes(b"different scanner image")
        self.build()
        self.assertEqual(len(self.compilations), 2)
        (self.runtime / "compile-safe.wasm").write_bytes(b"different compiler")
        self.build()
        self.assertEqual(len(self.compilations), 4)
        self.host["host"] = {"executable": "different host"}
        self.build()
        self.assertEqual(len(self.compilations), 6)

    def test_changed_boot_dependency_invalidates_its_consumer(self):
        self.build()
        self.boot.write_text("changed boot proof")
        self.build()
        self.assertEqual(self.compilations.count(str(self.boot)), 2)
        self.assertEqual(self.compilations.count(str(self.source)), 2)

    def test_modules_share_a_base_without_leaking_source_overlays(self):
        self.build()
        self.assertEqual(len(self.snapshots), 2)
        self.assertEqual(self.snapshots[0], self.snapshots[1])
        self.assertNotIn(str(self.boot), self.snapshots[0])
        self.assertNotIn(str(self.source), self.snapshots[1])
        self.assertNotIn(str(self.source.with_suffix(".vo")), self.inherited[str(self.boot)])

    def test_changed_project_source_reuses_boot_and_corruption_is_repaired(self):
        self.build()
        self.source.write_text("changed project proof")
        self.build()
        self.assertEqual(self.compilations.count(str(self.boot)), 1)
        self.assertEqual(self.compilations.count(str(self.source)), 2)
        artifact = self.gate.WASI_LIB / "project/theories/Example.vo"
        original = artifact.read_bytes()
        artifact.write_bytes(b"corruption")
        self.build()
        self.assertEqual(artifact.read_bytes(), original)
        self.assertEqual(len(self.compilations), 3)

    def test_legacy_domain_reuse_requires_a_recorded_matching_compiler(self):
        self.build()
        stamp = self.gate.WASI_LIB / "sources.json"
        manifest = check.decoded(stamp.read_bytes(), "manifest")
        legacy = "older-combined-runtime-domain"
        limits = dict(check.DEFAULT_LIMITS, wall_seconds=1200, cpu_seconds=600,
                      memory_mib=4096, fuel=500_000_000_000)
        # Simulate entries made before compilation and checker identities split.
        cache = self.gate.REPO / ".verification/wasi-cache/trusted-compile"
        for path in list(cache.glob("*/*.json")):
            entry = check.decoded(path.read_bytes(), "cache entry")
            source = next(name for name in entry["observed"] if name.endswith(".v"))
            base = key(dict(runtime=legacy, source=source,
                            sha256=hash_bytes(Path(source).read_bytes()), limits=limits))
            entry["base"] = base
            target = cache / base / path.name
            target.parent.mkdir()
            target.write_bytes(check.encoded(entry))
            path.unlink()
            path.parent.rmdir()
        manifest["runtime"] = legacy
        stamp.write_bytes(check.encoded(manifest))
        self.build()
        self.assertEqual(len(self.compilations), 2)
        manifest = check.decoded(stamp.read_bytes(), "manifest")
        del manifest["compiler_identity"]
        stamp.write_bytes(check.encoded(manifest))
        self.build()
        self.assertEqual(len(self.compilations), 4)

    def test_core_short_imports_do_not_acquire_foreign_alias_dependencies(self):
        foundation = self.coqlib / "theories/ssr/Foundation.v"
        foundation.parent.mkdir(parents=True)
        foundation.write_text("foundation")
        # A combined scan selects a foreign wrapper, creating a false cycle.
        self.dependencies[str(foundation)] = [str(self.source.with_suffix(".vo"))]
        self.dependencies[str(self.source)] = [str(foundation.with_suffix(".vo"))]
        self.core_dependencies[str(foundation)] = [str(self.boot.with_suffix(".vo"))]
        self.build()
        self.assertEqual(len(self.compilations), 3)
        self.assertNotIn(str(self.source.with_suffix(".vo")), self.inherited[str(foundation)])
        manifest = check.decoded((self.gate.WASI_LIB / "sources.json").read_bytes(), "manifest")
        self.assertNotIn(str(self.source.with_suffix(".vo")),
                         manifest["dependencies"][str(foundation.with_suffix(".vo"))])


if __name__ == "__main__":
    unittest.main()
