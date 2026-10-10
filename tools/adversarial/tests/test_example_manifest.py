"""Independent example configuration and fail-closed schema validation."""
import contextlib
import copy
import io
import json
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import check
import example_manifest
import examples


class ExampleManifestTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.path = Path(self.temporary.name) / "examples.json"
        self.manifest = json.loads(example_manifest.MANIFEST.read_bytes())

    def load(self, value=None):
        self.path.write_text(json.dumps(self.manifest if value is None else value))
        return example_manifest.load(self.path)

    def test_repository_manifest_has_existing_sources_and_complete_resource_profiles(self):
        manifest = example_manifest.load()
        self.assertEqual(len(manifest["examples"]), 8)
        for entry in manifest["examples"]:
            self.assertEqual(set(manifest["profiles"][entry["profile"]]), set(check.DEFAULT_LIMITS))
            self.assertTrue((check.REPO / entry["spec"]).is_file())
            self.assertTrue((check.REPO / entry["candidate"]).is_dir())

    def test_schema_rejects_invalid_types_fields_policy_paths_and_limits(self):
        mutations = [
            lambda m: m.update(format=True),
            lambda m: m.update(operation_attempts=True),
            lambda m: m.update(operation_attempts=0),
            lambda m: m.update(operation_attempts=4),
            lambda m: m.update(command="arbitrary host code"),
            lambda m: m["profiles"]["small"].update(cpu_seconds=True),
            lambda m: m["profiles"]["small"].update(cpu_seconds=0),
            lambda m: m["profiles"]["small"].update(fuel=1.5),
            lambda m: m["profiles"]["small"].update(network=True),
            lambda m: m["examples"][0].update(axiom_policy="arbitrary"),
            lambda m: m["examples"][0].update(spec="../private/Spec.v"),
            lambda m: m["examples"][0].update(candidate="/tmp/candidate"),
            lambda m: m.update(examples=[]),
            lambda m: m["profiles"].update({"../profile": m["profiles"]["small"]}),
        ]
        for i, mutate in enumerate(mutations):
            with self.subTest(case=i):
                manifest = copy.deepcopy(self.manifest)
                mutate(manifest)
                with self.assertRaises(ValueError):
                    self.load(manifest)

    def test_duplicate_names_unknown_profiles_and_missing_sources_are_rejected(self):
        duplicate = dict(self.manifest["examples"][0], axiom_policy="ci")
        self.manifest["examples"].append(duplicate)
        with self.assertRaisesRegex(ValueError, "Duplicate example name"):
            self.load()
        self.manifest["examples"].pop()
        self.manifest["examples"][0]["profile"] = "missing"
        with self.assertRaisesRegex(ValueError, "Unknown example resource profile"):
            self.load()
        self.manifest["examples"][0]["profile"] = "small"
        self.manifest["examples"][0]["spec"] = "verification/missing-example/spec/Spec.v"
        with self.assertRaisesRegex(ValueError, "Invalid example spec"):
            self.load()

    def test_duplicate_json_fields_are_rejected(self):
        self.path.write_text(json.dumps(self.manifest).replace('"format": 1', '"format": 1, "format": 1'))
        with self.assertRaises(check.Rejected):
            example_manifest.load(self.path)

    def test_schema_file_controls_constraints(self):
        schema = json.loads(example_manifest.SCHEMA.read_bytes())
        schema["$defs"]["positive"]["minimum"] = 100
        path = Path(self.temporary.name) / "schema.json"
        path.write_text(json.dumps(schema))
        with patch.object(example_manifest, "SCHEMA", path):
            with self.assertRaisesRegex(ValueError, "below minimum"):
                self.load()

    def test_remote_references_and_unsupported_schema_keywords_are_rejected(self):
        for schema in ({"$ref": "https://example.invalid/schema"},
                       {"type": "string", "execute": "code"}):
            with self.subTest(schema=schema), self.assertRaises(ValueError):
                example_manifest.validate("value", schema)

    def test_source_symlink_cannot_escape_repository(self):
        root = Path(self.temporary.name) / "repo"
        outside = Path(self.temporary.name) / "outside"
        outside.mkdir()
        (outside / "Spec.v").write_text("external")
        (root / "verification/increment").mkdir(parents=True)
        (root / "verification/increment/spec").symlink_to(outside, target_is_directory=True)
        self.manifest["examples"] = self.manifest["examples"][:1]
        with patch.object(check, "REPO", root), self.assertRaisesRegex(ValueError, "Invalid example spec"):
            self.load()

    def test_runner_uses_manifest_names_paths_policy_and_limits(self):
        entry = dict(self.manifest["examples"][0], name="renamed", axiom_policy="ci")
        limits = dict(self.manifest["profiles"]["small"], cpu_seconds=73)
        manifest = {"examples": [entry], "profiles": {entry["profile"]: limits},
                    "operation_attempts": 2}
        sandbox = SimpleNamespace(close=lambda: None)
        output = Path(self.temporary.name) / "results"
        with (patch.object(example_manifest, "load", return_value=manifest),
              patch.object(check, "ensure_built") as provision,
              patch.object(check, "toolchain", return_value={}) as runtime,
              patch.object(check, "trusted_axioms", return_value=["allowed"]),
              patch.object(check, "make_sandbox", return_value=sandbox) as make,
              patch.object(check, "prepare", return_value="spec-id") as prepare,
              patch.object(check, "evaluate", return_value={"status": "accepted"}) as evaluate,
              patch.object(sys, "argv", ["examples.py", "--only", "renamed", "--output", str(output)]),
              contextlib.redirect_stdout(io.StringIO())):
            self.assertEqual(examples.main(), 0)
        provision.assert_called_once_with("wasi")
        runtime.assert_called_once_with("wasi")
        self.assertEqual(make.call_args.args[0], limits)
        self.assertEqual(prepare.call_args.args[0], check.REPO / entry["spec"])
        self.assertEqual(prepare.call_args.args[-1], ["allowed"])
        self.assertEqual(evaluate.call_args.args[2], check.REPO / entry["candidate"])

    def run_attempts(self, reports, *, progress=True, cache=True, attempts=2):
        root = Path(self.temporary.name)
        output = root / "result"
        directory = root / "cache" if cache else None
        sandbox = SimpleNamespace(cache=SimpleNamespace(directory=directory))
        calls = []
        def evaluate(*args):
            calls.append(args)
            output.mkdir()
            report = reports[min(len(calls) - 1, len(reports) - 1)]
            (output / "report.json").write_text(json.dumps(report))
            if directory is not None and progress:
                category = "compile" if report.get("stage") == "compilation" else "checked-prefix"
                prefix = directory / category / "seed"
                prefix.mkdir(parents=True, exist_ok=True)
                (prefix / (str(len(calls)) + ".json")).write_text("completed fixture")
            return report
        with patch.object(check, "evaluate", side_effect=evaluate):
            result = examples.evaluate_with_checkpoints(root / "bundle", "spec-id",
                root / "candidate", output, {}, sandbox, attempts)
        return result, calls

    def test_kernel_resource_retry_preserves_failed_report_and_accepts_only_complete_result(self):
        failed = dict(status="rejected", stage="kernel-and-contract",
                      reason="Sandbox wall time limit exceeded")
        (report, attempts), calls = self.run_attempts([failed, {"status": "accepted"}])
        self.assertEqual((report["status"], attempts, len(calls)), ("accepted", 2, 2))
        root = Path(self.temporary.name)
        self.assertEqual(json.loads((root / "attempt-1/report.json").read_text()), failed)
        self.assertEqual(json.loads((root / "result/report.json").read_text()), report)

    def test_compile_resource_retry_requires_completed_module_progress(self):
        failed = dict(status="rejected", stage="compilation",
                      reason="Sandbox wall time limit exceeded")
        (report, attempts), calls = self.run_attempts([failed, {"status": "accepted"}])
        self.assertEqual((report["status"], attempts, len(calls)), ("accepted", 2, 2))

    def test_kernel_resource_retries_are_bounded(self):
        failed = dict(status="rejected", stage="kernel-and-contract",
                      reason="Sandbox CPU time limit exceeded")
        (report, attempts), calls = self.run_attempts([failed])
        self.assertEqual((report["status"], attempts, len(calls)), ("rejected", 2, 2))

    def test_no_retry_for_logical_or_compile_failures_missing_progress_or_disabled_cache(self):
        cases = [
            ("kernel-and-contract", "Signature mismatch", True, True),
            ("compilation", "Syntax error", True, True),
            ("compilation", "Sandbox wall time limit exceeded", False, True),
            ("kernel-and-contract", "Sandbox wall time limit exceeded", False, True),
            ("kernel-and-contract", "Sandbox wall time limit exceeded", True, False),
        ]
        for stage, reason, progress, cache in cases:
            with self.subTest(stage=stage, reason=reason, progress=progress, cache=cache):
                output = Path(self.temporary.name) / "result"
                if output.exists():
                    import shutil
                    shutil.rmtree(output)
                failed = dict(status="rejected", stage=stage, reason=reason)
                (report, attempts), calls = self.run_attempts(
                    [failed], progress=progress, cache=cache)
                self.assertEqual((report["status"], attempts, len(calls)), ("rejected", 1, 1))


if __name__ == "__main__":
    unittest.main()
