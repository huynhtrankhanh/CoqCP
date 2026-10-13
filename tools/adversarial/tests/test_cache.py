"""Cache invalidation, damage, provenance boundaries, and real warm runs."""
import base64
from concurrent.futures import ThreadPoolExecutor
import copy
import hashlib
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from test_check import gate, VALID
from result_cache import ResultCache


class CacheTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.inputs = self.root / "inputs"
        self.inputs.mkdir()
        (self.inputs / "Candidate.v").write_text(VALID)
        self.bundle = self.root / "bundle"
        (self.bundle / "spec").mkdir(parents=True)
        (self.bundle / "spec/Spec.vo").write_bytes(b"frozen specification")
        self.artifacts = self.root / "artifacts"
        self.artifacts.mkdir()
        self.runtime = {"fingerprint": "validated-runtime", "rocq": "/rocq", "coqlib": "/coqlib",
                        "sandbox_identity": {"image": "sha256:image", "files": {"runsc": "pinned"}}}
        self.cache = ResultCache(gate, self.root / "cache")
        self.sandbox = unittest.mock.Mock(limits=dict(gate.DEFAULT_LIMITS), cache=self.cache)
        self.calls = {"compile": 0, "kernel": 0}
        self.sandbox.run.side_effect = self.run_tool

    def run_tool(self, argv, mounts, *, compiler_worker=False):
        if compiler_worker:
            self.calls["compile"] += 1
            inputs = dict((target, host) for host, target in mounts)["/inputs"]
            config = json.loads((inputs / "build.json").read_text())
            return gate.encoded({"artifacts": {
                Path(name).with_suffix(".vo").name:
                    base64.b64encode((inputs / name).read_bytes()).decode()
                for name in config["sources"]}})
        self.calls["kernel"] += 1
        return gate.encoded({"status": "spec-checked" if "--spec-only" in argv else "accepted",
                             "rocq_version": gate.VERSION, "axioms": []})

    def compile(self, *, inputs=None, namespace="Submission", sources=None):
        return gate.compile_sources(inputs or self.inputs, sources or ["Candidate.v"], namespace,
                                    self.bundle, self.runtime, self.sandbox)

    def check(self, *, allowed=(), spec_only=False):
        return gate.kernel_check(self.bundle, None if spec_only else self.artifacts,
                                 self.runtime, self.sandbox, allowed, spec_only=spec_only)

    def test_warm_compilation_and_validation_restore_exact_artifacts(self):
        first = self.compile()
        for name, data in first.items():
            (self.artifacts / name).write_bytes(data)
        checked = self.check()
        self.assertEqual(self.compile(), first)
        self.assertEqual(self.check(), checked)
        self.assertEqual(self.calls, {"compile": 1, "kernel": 1})
        self.assertEqual(self.cache.statistics(), {
            "compile": {"hits": 1, "misses": 1}, "kernel": {"hits": 1, "misses": 1}})

    def test_full_runtime_identity_invalidates_both_domains(self):
        (self.artifacts / "Candidate.vo").write_bytes(b"proof")
        self.compile()
        self.check()
        for mutate in [lambda r: r.update(fingerprint="new-checker"),
                       lambda r: r["sandbox_identity"].update(image="sha256:new-image"),
                       lambda r: r["sandbox_identity"]["files"].update(runsc="new-runtime")]:
            original = copy.deepcopy(self.runtime)
            mutate(self.runtime)
            before = dict(self.calls)
            self.compile()
            self.check()
            self.assertEqual(self.calls, {kind: count + 1 for kind, count in before.items()})
            self.runtime = original

    def test_compilation_binds_sources_helpers_namespace_bundle_and_limits(self):
        self.compile()
        for change in [lambda: (self.inputs / "Candidate.v").write_text(VALID + "\n"),
                       lambda: (self.inputs / "Unused.v").write_text("Axiom cheat : False."),
                       lambda: (self.bundle / "spec/Spec.vo").write_bytes(b"new contract"),
                       lambda: self.sandbox.limits.update(cpu_seconds=61)]:
            before = self.calls["compile"]
            change()
            self.compile()
            self.assertEqual(self.calls["compile"], before + 1)
        self.compile(namespace="Trusted")
        self.assertEqual(self.calls["compile"], 6)

    def test_kernel_key_binds_all_artifacts_even_unused_helpers_policy_and_limits(self):
        (self.artifacts / "Candidate.vo").write_bytes(b"proof")
        self.check()
        for change in [lambda: (self.artifacts / "Unused.vo").write_bytes(b"unused"),
                       lambda: (self.artifacts / "Candidate.vo").write_bytes(b"changed proof"),
                       lambda: (self.bundle / "spec/Spec.vo").write_bytes(b"changed contract"),
                       lambda: self.sandbox.limits.update(memory_mib=4096)]:
            before = self.calls["kernel"]
            change()
            self.check()
            self.assertEqual(self.calls["kernel"], before + 1)
        self.check(allowed=gate.trusted_axioms())
        self.check(spec_only=True)
        self.assertEqual(self.calls["kernel"], 7)

    def test_damaged_blobs_and_entries_are_misses_and_are_repaired(self):
        original = self.compile()
        blob = next((self.cache.directory / "blobs").glob("*/*"))
        blob.write_bytes(b"truncated")
        self.assertEqual(self.compile(), original)
        self.assertEqual(self.calls["compile"], 2)
        entry = next((self.cache.directory / "compile").glob("*/*.json"))
        entry.write_bytes(b'{"format":1,"format":1}')
        self.assertEqual(self.compile(), original)
        self.assertEqual(self.calls["compile"], 3)

    def test_cached_report_still_requires_exact_schema_version_and_axiom_policy(self):
        self.check()
        entry = next((self.cache.directory / "kernel").glob("*/*.json"))
        for update in [{"extra": True}, {"rocq_version": "old"}, {"axioms": ["Unapproved.cheat"]}]:
            envelope = json.loads(entry.read_text())
            envelope["payload"].update(update)
            envelope["sha256"] = hashlib.sha256(gate.encoded(envelope["payload"])).hexdigest()
            entry.write_bytes(gate.encoded(envelope))
            before = self.calls["kernel"]
            self.assertEqual(self.check()["status"], "accepted")
            self.assertEqual(self.calls["kernel"], before + 1)

    def test_failures_and_malformed_successes_are_not_cached(self):
        self.sandbox.run.side_effect = gate.Rejected("Sandbox wall time limit exceeded")
        for _ in range(2):
            with self.assertRaises(gate.Rejected):
                self.compile()
            with self.assertRaises(gate.Rejected):
                self.check()
        self.assertFalse(list(self.cache.directory.glob("*/*/*.json")))
        self.sandbox.run.side_effect = None
        self.sandbox.run.return_value = b'{"status":"accepted"}'
        with self.assertRaises(gate.Rejected):
            self.check()
        self.assertFalse(list((self.cache.directory / "kernel").glob("*/*.json")))

    def test_disabled_cache_executes_every_operation(self):
        self.sandbox.cache = None
        for _ in range(2):
            self.compile()
            self.check()
        self.assertEqual(self.calls, {"compile": 2, "kernel": 2})

    def test_symlink_blob_is_a_miss_and_input_symlinks_are_rejected(self):
        self.compile()
        blob = next((self.cache.directory / "blobs").glob("*/*"))
        outside = self.root / "outside"
        outside.write_bytes(blob.read_bytes())
        blob.unlink()
        blob.symlink_to(outside)
        self.compile()
        self.assertEqual(self.calls["compile"], 2)
        self.assertFalse(blob.is_symlink())
        (self.inputs / "Hidden.v").symlink_to(outside)
        with self.assertRaisesRegex(gate.Rejected, "regular files"):
            self.compile()

    def test_cache_root_requires_private_ownership_and_rejects_symlinks(self):
        os.chmod(self.cache.directory, 0o777)
        with self.assertRaisesRegex(gate.Rejected, "private"):
            ResultCache(gate, self.cache.directory)
        link = self.root / "link"
        link.symlink_to(self.cache.directory, target_is_directory=True)
        with self.assertRaises(gate.Rejected):
            ResultCache(gate, link)

    def test_parallel_coordinators_publish_one_complete_compilation(self):
        def compile(index):
            inputs = self.root / str(index)
            inputs.mkdir()
            (inputs / "Candidate.v").write_text(VALID)
            return self.compile(inputs=inputs)
        with ThreadPoolExecutor(max_workers=4) as pool:
            results = list(pool.map(compile, range(4)))
        self.assertEqual(self.calls["compile"], 1)
        self.assertTrue(all(value == results[0] for value in results))


class CacheIntegrationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        gate.ensure_built()
        cls.runtime = gate.toolchain()

    def test_fresh_bundles_warm_cache_and_changed_proof_still_reaches_kernel(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            sandbox = gate.make_sandbox(dict(gate.DEFAULT_LIMITS), runtime=self.runtime,
                                        cache_directory=root / "cache")
            candidate = root / "candidate"
            candidate.mkdir()
            (candidate / "Candidate.v").write_text(VALID)
            try:
                first = gate.prepare(gate.REPO / "verification/increment/spec/Spec.v",
                                     root / "first", self.runtime, sandbox, [])
                cold = gate.evaluate(root / "first", first, candidate, root / "cold", self.runtime, sandbox)
                self.assertEqual(cold["status"], "accepted", cold)
                with patch.object(sandbox, "run", side_effect=AssertionError("warm operation executed")):
                    second = gate.prepare(gate.REPO / "verification/increment/spec/Spec.v",
                                          root / "second", self.runtime, sandbox, [])
                    warm = gate.evaluate(root / "second", second, candidate, root / "warm", self.runtime, sandbox)
                self.assertEqual(first, second)
                self.assertEqual(warm["artifacts"], cold["artifacts"])
                self.assertEqual(warm["status"], "accepted", warm)
                (candidate / "Candidate.v").write_text(VALID.replace(
                    "Proof. intro input. reflexivity. Qed.", "Admitted."))
                rejected = gate.evaluate(root / "second", second, candidate, root / "changed",
                                         self.runtime, sandbox)
                self.assertEqual(rejected["status"], "rejected", rejected)
                self.assertEqual(rejected["stage"], "kernel-and-contract")
                self.assertIn("Unapproved axiom", rejected["reason"])
            finally:
                sandbox.close()

    def test_editing_validation_sources_changes_the_actual_runtime_fingerprint(self):
        self.assertEqual(gate.toolchain()["fingerprint"], self.runtime["fingerprint"])
        for name in ["check.py", "result_cache.py", "worker.py", "gvisor_backend.py", "spec_check.ml"]:
            original = gate.digest
            with self.subTest(source=name), patch.object(gate, "digest", side_effect=lambda path:
                    "0" * 64 if Path(path) == gate.TOOLS / name else original(path)):
                self.assertNotEqual(gate.toolchain()["fingerprint"], self.runtime["fingerprint"])


if __name__ == "__main__":
    unittest.main()
