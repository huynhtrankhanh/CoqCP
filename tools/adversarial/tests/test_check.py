"""Acceptance and containment regressions; no third-party Python packages."""
import importlib.util
import json
import os
from pathlib import Path
import shutil
import sys
import tempfile
import unittest
from unittest.mock import patch

PATH = Path(__file__).resolve().parents[1] / "check.py"
sys.path.insert(0, str(PATH.parent))
SPEC = importlib.util.spec_from_file_location("adversarial_check", PATH)
gate = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(gate)
from context_policy import validate_context

HEADER = "From CoqCP Require Import Options.\nRequire Trusted.Spec.\n"
VALID = HEADER + """
Module Implementation.
  Definition program : nat -> nat := S.
  Lemma correct : Trusted.Spec.required program.
  Proof. intro input. reflexivity. Qed.
End Implementation.
"""


class ContextPolicyTests(unittest.TestCase):
    SUMMARY = """CONTEXT SUMMARY
===============
* Theory: Set is predicative
* Theory: Rewrite rules are not allowed
* Axioms: <none>
* Constants/Inductives relying on type-in-type: <none>
* Constants/Inductives relying on unsafe (co)fixpoints: <none>
* Inductives whose positivity is assumed: <none>
* Inductives relying on indices not mattering: <none>
"""

    def test_no_axioms(self):
        self.assertEqual(validate_context(self.SUMMARY)["axioms"], [])

    def test_ci_trusted_axioms(self):
        summary = self.SUMMARY.replace("* Axioms: <none>",
                                      "* Axioms:\n  " + "\n  ".join(gate.trusted_axioms()))
        self.assertEqual(validate_context(summary)["axioms"], gate.trusted_axioms())

    def test_untrusted_axiom(self):
        summary = self.SUMMARY.replace("* Axioms: <none>",
                                      "* Axioms:\n  Stdlib.Logic.Classical_Prop.classic")
        with self.assertRaisesRegex(ValueError, "outside CI policy"):
            validate_context(summary)

    def test_unsafe_theory(self):
        for old, new in [("Set is predicative", "Set is impredicative"),
                         ("Rewrite rules are not allowed", "Rewrite rules are allowed"),
                         ("type-in-type: <none>", "type-in-type: Submission.bad"),
                         ("unsafe (co)fixpoints: <none>", "unsafe (co)fixpoints: Submission.bad"),
                         ("positivity is assumed: <none>", "positivity is assumed: Submission.Bad")]:
            with self.subTest(new=new), self.assertRaises(ValueError):
                validate_context(self.SUMMARY.replace(old, new))

    def test_extra_output(self):
        with self.assertRaises(ValueError):
            validate_context("Fake compiler output\n" + self.SUMMARY)
        with self.assertRaises(ValueError):
            validate_context(self.SUMMARY + "{status:accepted}\n")

    def test_missing_or_duplicate_section(self):
        with self.assertRaises(ValueError):
            validate_context(self.SUMMARY.replace("* Axioms: <none>\n", ""))
        with self.assertRaises(ValueError):
            validate_context(self.SUMMARY + "* Axioms: <none>\n")


class ProtocolValidationTests(unittest.TestCase):
    class Sandbox:
        limits = dict(gate.DEFAULT_LIMITS)

        def __init__(self, response):
            self.response = response

        def run(self, _argv, _mounts, *, compiler_worker=False):
            return self.response

    def test_compiler_response_must_be_strict_json_with_exact_schema(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            inputs, bundle = root / "inputs", root / "bundle"
            inputs.mkdir()
            bundle.mkdir()
            runtime = {"rocq": "/rocq", "coqlib": "/coqlib"}
            invalid = [
                b'{"artifacts":{"Candidate.vo":""},"accepted":true}',
                b'{"artifacts":{"Candidate.vo":NaN}}',
                b'{"artifacts":{},"artifacts":{"Candidate.vo":""}}',
            ]
            for response in invalid:
                with self.subTest(response=response), self.assertRaises(gate.Rejected):
                    gate.compile_sources(inputs, ["Candidate.v"], "Submission", bundle,
                                         runtime, self.Sandbox(response))

    def test_checker_response_requires_version_axioms_and_exact_schema(self):
        allowed = gate.trusted_axioms()
        valid = gate.encoded({"status": "accepted", "rocq_version": gate.VERSION,
                              "axioms": allowed})
        invalid = [
            b'{"status":"accepted"}',
            valid[:-1] + b',"extra":true}',
            valid.replace(gate.VERSION.encode(), b"0.0.0"),
            b'{"status":"accepted","status":"rejected",'
            b'"rocq_version":"9.3.0","axioms":[]}',
        ]
        with tempfile.TemporaryDirectory() as temporary:
            bundle = Path(temporary)
            runtime = {"coqlib": "/coqlib"}
            for response in invalid:
                with self.subTest(response=response), self.assertRaises(gate.Rejected):
                    gate.kernel_check(bundle, None, runtime, self.Sandbox(response), allowed,
                                      spec_only=True)


class AcceptanceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        gate.ensure_built()
        cls.temporary = tempfile.TemporaryDirectory(prefix="coqcp-acceptance-tests-")
        cls.root = Path(cls.temporary.name)
        cls.runtime = gate.toolchain()
        cls.sandbox = gate.Sandbox(dict(gate.DEFAULT_LIMITS))
        cls.bundle = cls.root / "bundle"
        cls.spec_id = gate.prepare(gate.REPO / "verification/increment/spec/Spec.v",
                                  cls.bundle, cls.runtime, cls.sandbox, [])

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def evaluate(self, source, extra=None, *, accepted=False, reason=None):
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
            self.assertEqual(json.loads((root / "result/report.json").read_text()), report)
            if reason:
                self.assertIn(reason, report["reason"])
            if accepted:
                self.assertEqual(report["axioms"], [])
                self.assertIn("Candidate.vo", report["artifacts"])
            return report

    def test_valid_program(self):
        self.evaluate(VALID, accepted=True)

    def test_different_correct_implementation(self):
        self.evaluate(HEADER + """
Module Implementation.
  Definition program (n : nat) := n + 1.
  Lemma correct : Trusted.Spec.required program.
  Proof. unfold Trusted.Spec.required, program. intro n.
    induction n as [|n IH]; simpl; [reflexivity |]. now rewrite IH.
  Qed.
End Implementation.
""", accepted=True)

    def test_wrong_statement(self):
        self.evaluate(HEADER + """
Module Implementation.
  Definition program : nat -> nat := fun n => n.
  Lemma correct : True. Proof. exact I. Qed.
End Implementation.
""", reason="Signature mismatch")

    def test_notation_attack(self):
        self.evaluate(HEADER + """
Notation "'required' p" := True (at level 10).
Module Implementation.
  Definition program : nat -> nat := fun n => n.
  Lemma correct : required program. Proof. exact I. Qed.
End Implementation.
""", reason="Signature mismatch")

    def test_namespace_shadowing(self):
        self.evaluate(HEADER + """
Module Trusted.
  Module Spec.
    Definition required (p : nat -> nat) := True.
  End Spec.
End Trusted.
Module Implementation.
  Definition program : nat -> nat := fun n => n.
  Lemma correct : Submission.Candidate.Trusted.Spec.required program.
  Proof. exact I. Qed.
End Implementation.
""", reason="Signature mismatch")

    def test_additional_premise(self):
        self.evaluate(HEADER + """
Module Implementation.
  Definition program : nat -> nat := S.
  Lemma correct : False -> Trusted.Spec.required program.
  Proof. intros impossible. destruct impossible. Qed.
End Implementation.
""", reason="Signature mismatch")

    def test_missing_field(self):
        self.evaluate(HEADER + """
Module Implementation.
  Definition program : nat -> nat := S.
End Implementation.
""", reason="does not satisfy")

    def test_admitted_proof(self):
        self.evaluate(VALID.replace("Proof. intro input. reflexivity. Qed.", "Admitted."),
                      reason="Unapproved axiom")

    def test_unused_axiom_and_spoofed_output(self):
        self.evaluate(VALID.replace("Module Implementation.", "Axiom cheat : False.\nModule Implementation.")
                      .replace("intro input.", 'idtac "{status:accepted,axioms:[]}". intro input.'),
                      reason="Unapproved axiom")

    def test_unimported_helper_is_checked(self):
        self.evaluate(VALID, {"Unused.v": "From CoqCP Require Import Options.\nAxiom cheat : False.\n"},
                      reason="Unapproved axiom")

    def test_unused_functor_axiom_is_checked(self):
        hidden = """
Module Type EMPTY. End EMPTY.
Module Unused (X : EMPTY).
  Axiom cheat : False.
End Unused.
"""
        self.evaluate(VALID.replace("Module Implementation.", hidden + "Module Implementation."),
                      reason="Unapproved axiom")

    def test_unused_functor_unsafe_definition_is_checked(self):
        hidden = """
Module Type EMPTY. End EMPTY.
Module Unused (X : EMPTY).
  Unset Guard Checking.
  Fixpoint bad (n : nat) : False := bad n.
  Set Guard Checking.
End Unused.
"""
        self.evaluate(VALID.replace("Module Implementation.", hidden + "Module Implementation."),
                      reason="Unsafe typing flags")

    def test_functor_parameters_are_not_global_axioms(self):
        conditional = """
Module Type ARGUMENT.
  Parameter value : nat.
End ARGUMENT.
Module Conditional (X : ARGUMENT).
  Definition value := X.value.
End Conditional.
"""
        self.evaluate(VALID.replace("Module Implementation.", conditional + "Module Implementation."),
                      accepted=True)

    def test_helper_dependency_order(self):
        source = VALID.replace("Require Trusted.Spec.", "Require Trusted.Spec Submission.ZHelper.")
        source = source.replace("nat -> nat := S", "nat -> nat := Submission.ZHelper.successor")
        self.evaluate(source, {"ZHelper.v": "From CoqCP Require Import Options.\nDefinition successor := S.\n"},
                      accepted=True)

    def test_source_cannot_create_or_replace_compiler_artifacts(self):
        helper = "From CoqCP Require Import Options.\nDefinition successor := S.\n"
        source = VALID.replace("Require Trusted.Spec.",
                               "Require Trusted.Spec Submission.AHelper.")
        source = source.replace("Module Implementation.",
                                'Print Universes "/work/AHelper.vo".\nModule Implementation.')
        self.evaluate(source, {"AHelper.v": helper},
                      reason="Submission modified a compiler artifact")

        source = VALID.replace("Module Implementation.",
                               'Print Universes "/work/Candidate.vo".\nModule Implementation.')
        self.evaluate(source, reason="Submission created or removed a compiler artifact")

    def test_sealed_module(self):
        self.evaluate(VALID.replace("Module Implementation.",
                                    "Module Implementation : Trusted.Spec.SOLUTION."), accepted=True)

    def test_abstract_implementation_is_rejected(self):
        self.evaluate(HEADER + "Declare Module Implementation : Trusted.Spec.SOLUTION.\n",
                      reason="Unapproved axiom")

    def test_implementation_functor_is_rejected(self):
        source = VALID.replace("Module Implementation.",
                               "Module Type EMPTY. End EMPTY.\nModule Implementation (X : EMPTY).")
        self.evaluate(source, reason="unapplied functor")

    def test_allowlist_requires_explicit_evaluator_policy(self):
        source = VALID.replace("Require Trusted.Spec.",
                               "Require Trusted.Spec Stdlib.Logic.FunctionalExtensionality.")
        self.evaluate(source, reason="Unapproved axiom")
        with tempfile.TemporaryDirectory(dir=self.root) as temporary:
            root = Path(temporary)
            bundle = root / "bundle"
            allowed = gate.trusted_axioms()
            spec_id = gate.prepare(gate.REPO / "verification/increment/spec/Spec.v", bundle,
                                   self.runtime, self.sandbox, allowed)
            submission = root / "submission"
            submission.mkdir()
            (submission / "Candidate.v").write_text(source)
            report = gate.evaluate(bundle, spec_id, submission, root / "result",
                                   self.runtime, self.sandbox)
            self.assertEqual(report["status"], "accepted", report)
            self.assertEqual(report["axioms"], allowed)

    def test_arbitrary_axiom_name_is_never_approved(self):
        with self.assertRaisesRegex(gate.Rejected, "CI trust set"):
            gate.prepare(gate.REPO / "verification/increment/spec/Spec.v", self.root / "forbidden-policy",
                         self.runtime, self.sandbox, ["Stdlib.Logic.Classical_Prop.classic"])
        with self.assertRaisesRegex(gate.Rejected, "CI trust set"):
            gate.kernel_check(self.bundle, None, self.runtime, self.sandbox,
                              ["Trusted.Spec.cheat"], spec_only=True)

    def test_standalone_gate_rejects_non_ci_policy(self):
        with self.assertRaisesRegex(gate.Rejected, "outside the compiled CI trust policy"):
            self.sandbox.run(["/tool/spec-check", "--allow-axiom", "Stdlib.Logic.Classical_Prop.classic"], [])

    def test_toolchain_change_invalidates_bundle(self):
        runtime = dict(self.runtime, fingerprint="changed")
        with self.assertRaisesRegex(gate.Rejected, "Toolchain changed"):
            gate.validate_bundle(self.bundle, self.spec_id, runtime)

    def test_unsafe_guard_checking(self):
        unsafe = "Unset Guard Checking.\nFixpoint bad (n : nat) : False := bad n.\nSet Guard Checking.\n"
        self.evaluate(VALID.replace("Module Implementation.", unsafe + "Module Implementation."),
                      reason="Unsafe typing flags")

    def test_unsafe_universes(self):
        unsafe = "Unset Universe Checking.\nDefinition bad : Type := Type.\nSet Universe Checking.\n"
        self.evaluate(VALID.replace("Module Implementation.", unsafe + "Module Implementation."),
                      reason="Unsafe typing flags")

    def test_unsafe_positivity(self):
        unsafe = "Unset Positivity Checking.\nInductive Bad := mkBad : (Bad -> False) -> Bad.\nSet Positivity Checking.\n"
        self.evaluate(VALID.replace("Module Implementation.", unsafe + "Module Implementation."),
                      reason="Unsafe typing flags")

    def test_precompiled_submission_is_rejected(self):
        self.evaluate(VALID, {"Candidate.vo": "not a source"}, reason="only top-level .v")

    def test_symlink_submission_is_rejected(self):
        with tempfile.TemporaryDirectory(dir=self.root) as temporary:
            root = Path(temporary)
            submission = root / "submission"
            submission.mkdir()
            (root / "outside.v").write_text(VALID)
            (submission / "Candidate.v").symlink_to(root / "outside.v")
            report = gate.evaluate(self.bundle, self.spec_id, submission, root / "result",
                                   self.runtime, self.sandbox)
            self.assertEqual(report["status"], "rejected")

    def test_bundle_and_manifest_tampering(self):
        with tempfile.TemporaryDirectory(dir=self.root) as temporary:
            clone = Path(temporary) / "bundle"
            shutil.copytree(self.bundle, clone)
            with (clone / "spec/Spec.vo").open("ab") as stream:
                stream.write(b"tampered")
            with self.assertRaisesRegex(gate.Rejected, "was modified"):
                gate.validate_bundle(clone, self.spec_id, self.runtime)
            manifest = json.loads((clone / "manifest.json").read_bytes())
            manifest["files"] = gate.file_manifest(clone)
            (clone / "manifest.json").write_bytes(gate.encoded(manifest))
            with self.assertRaisesRegex(gate.Rejected, "ID mismatch"):
                gate.validate_bundle(clone, self.spec_id, self.runtime)

    def test_corrupted_vo_is_rejected(self):
        with tempfile.TemporaryDirectory(dir=self.root) as temporary:
            root = Path(temporary)
            inputs = root / "inputs"
            inputs.mkdir()
            (inputs / "Candidate.v").write_text(VALID)
            artifacts = gate.compile_sources(inputs, ["Candidate.v"], "Submission", self.bundle,
                                             self.runtime, self.sandbox)
            broken = root / "artifacts"
            broken.mkdir()
            (broken / "Candidate.vo").write_bytes(artifacts["Candidate.vo"][:100])
            with self.assertRaises(gate.Rejected):
                gate.kernel_check(self.bundle, broken, self.runtime, self.sandbox, [])


class SandboxTests(unittest.TestCase):
    def setUp(self):
        gate.ensure_built()
        self.limits = dict(gate.DEFAULT_LIMITS)

    def run_python(self, source, mounts=()):
        return gate.Sandbox(self.limits).run(["/usr/bin/python3", "-I", "-c", source], mounts)

    def test_filesystem_network_process_and_environment_isolation(self):
        with tempfile.TemporaryDirectory(prefix="coqcp-private-") as temporary:
            private = Path(temporary)
            (private / "secret").write_text("host-secret")
            visible = private / "visible"
            visible.mkdir()
            (visible / "immutable").write_text("trusted")
            source = f"""
import errno, os, pathlib, socket
assert not pathlib.Path({str(private / 'secret')!r}).exists()
assert not pathlib.Path('/etc/passwd').exists()
assert 'COQPATH' not in os.environ
for operation in [lambda: socket.socket(), os.fork,
                  lambda: pathlib.Path('/trusted/immutable').write_text('changed')]:
    try:
        operation()
    except OSError as error:
        assert error.errno in (errno.EPERM, errno.EROFS, errno.EACCES), error
    else:
        raise AssertionError('Sandbox operation unexpectedly permitted')
print('isolated')
"""
            self.assertEqual(self.run_python(source, [(visible, "/trusted")]), b"isolated\n")
            self.assertEqual((visible / "immutable").read_text(), "trusted")

    def test_wall_time_limit(self):
        self.limits["wall_seconds"] = 1
        with self.assertRaisesRegex(gate.Rejected, "wall time"):
            self.run_python("while True: pass")

    def test_cpu_limit(self):
        self.limits.update(cpu_seconds=1, wall_seconds=5)
        with self.assertRaisesRegex(gate.Rejected, "command failed"):
            self.run_python("while True: pass")

    def test_memory_limit(self):
        self.limits["memory_mib"] = 64
        with self.assertRaisesRegex(gate.Rejected, "command failed"):
            self.run_python("data = bytearray(400 * 1024 * 1024)")

    def test_output_limit(self):
        with self.assertRaisesRegex(gate.Rejected, "output limit"):
            self.run_python("import sys; sys.stdout.write('x' * (2 * 1024 * 1024))")

    def test_work_filesystem_quota(self):
        self.limits["work_mib"] = 4
        source = """
import errno, pathlib
try:
    for n in range(128):
        pathlib.Path('/work/' + str(n)).write_bytes(b'x' * (128 * 1024))
except OSError as error:
    assert error.errno == errno.ENOSPC, error
    print('bounded')
else:
    raise AssertionError('Filesystem quota not enforced')
"""
        self.assertEqual(self.run_python(source), b"bounded\n")

    def test_file_size_limit(self):
        self.limits["artifact_mib"] = 1
        with self.assertRaises(gate.Rejected):
            self.run_python("open('/work/large', 'wb').write(b'x' * (2 * 1024 * 1024))")

    def test_missing_sandbox_has_no_fallback(self):
        sandbox = gate.Sandbox(self.limits)
        sandbox.bwrap = "/nonexistent-bubblewrap"
        with self.assertRaisesRegex(gate.Rejected, "No safe condition for sandbox"):
            sandbox.run(["/usr/bin/true"], [])

    def test_root_execution_is_rejected(self):
        with patch.object(gate.os, "getuid", return_value=0):
            with self.assertRaisesRegex(gate.Rejected, "non-root"):
                gate.Sandbox(self.limits)


class InteractiveContractTests(unittest.TestCase):
    """A decoder theorem or unobserved I/O theorem is not a full certificate."""

    @classmethod
    def setUpClass(cls):
        gate.ensure_built()
        cls.temporary = tempfile.TemporaryDirectory(prefix="coqcp-interactive-contract-")
        cls.root = Path(cls.temporary.name)
        cls.runtime = gate.toolchain()
        cls.sandbox = gate.Sandbox(dict(gate.DEFAULT_LIMITS,
                                      wall_seconds=600, cpu_seconds=180, memory_mib=4096))
        cls.bundle = cls.root / "bundle"
        cls.spec_id = gate.prepare(
            gate.REPO / "verification/permuted-binary-strings/spec/Spec.v",
            cls.bundle, cls.runtime, cls.sandbox, gate.trusted_axioms())

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def evaluate(self, source):
        with tempfile.TemporaryDirectory(dir=self.root) as temporary:
            root = Path(temporary)
            submission = root / "submission"
            submission.mkdir()
            (submission / "Candidate.v").write_text(source)
            helpers = gate.REPO / "verification/permuted-binary-strings/candidate"
            for helper in helpers.glob("*.v"):
                if helper.name != "Candidate.v":
                    shutil.copyfile(helper, submission / helper.name)
            return gate.evaluate(self.bundle, self.spec_id, submission, root / "result",
                                 self.runtime, self.sandbox)

    def test_full_generated_certificate(self):
        source = (gate.REPO / "verification/permuted-binary-strings/candidate/Candidate.v").read_text()
        report = self.evaluate(source)
        self.assertEqual(report["status"], "accepted", report)
        self.assertEqual(report["axioms"], gate.trusted_axioms())

    def test_decoder_certificate_is_insufficient(self):
        report = self.evaluate(r"""From CoqCP Require Import Options.
From Submission Require Import PermutedBinaryStrings PermutedBinaryStringsProtocol.
Require Trusted.Spec.
Module Implementation.
  Definition program : Trusted.Spec.Program := Trusted.Spec.program.
  Lemma correct : forall n a, valid n a -> solve a = a.
  Proof. intros n a h. exact (proj1 (solve_correct n a h)). Qed.
End Implementation.
""")
        self.assertEqual(report["status"], "rejected", report)
        self.assertIn("Signature mismatch", report["reason"])

    def test_unobserved_execution_is_insufficient(self):
        report = self.evaluate(r"""From CoqCP Require Import Options Execution InteractiveExecution.
From Submission Require Import PermutedBinaryStrings PermutedBinaryStringsProtocol PermutedBinaryStringsEndToEnd.
From Generated Require Import PermutedBinaryStrings.
From stdpp Require Import numbers list.
Require Trusted.Spec.
Module Implementation.
  Definition program : Trusted.Spec.Program := Trusted.Spec.program.
  Lemma correct : forall n a, valid n a -> exists final,
    exec program (initial a) = Some (tt, final) /\
    stdout final = outputBytes a /\ stdin final = nil.
  Proof. intros n a h. exact (endToEnd_erases program (initial a) (outputBytes a)
    (flushes a) (generated_end_to_end n a h)). Qed.
End Implementation.
""")
        self.assertEqual(report["status"], "rejected", report)
        self.assertIn("Signature mismatch", report["reason"])


if __name__ == "__main__":
    unittest.main()
