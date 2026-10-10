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
sys.modules[SPEC.name] = gate
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


def fixture_cache(root):
    """CI reuses evaluator-owned work; cache mutation tests keep private roots."""
    shared = os.environ.get("COQCP_TEST_CACHE")
    return Path(shared).resolve() if shared else root / "cache"


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
    backend = "wasi"
    network_isolation = "auto"

    @classmethod
    def setUpClass(cls):
        gate.ensure_built(cls.backend)
        cls.temporary = tempfile.TemporaryDirectory(prefix="coqcp-acceptance-tests-")
        cls.root = Path(cls.temporary.name)
        cls.runtime = gate.toolchain(cls.backend)
        cls.sandbox = gate.make_sandbox(dict(gate.DEFAULT_LIMITS), cls.backend,
                                        cls.network_isolation, runtime=cls.runtime,
                                        cache_directory=fixture_cache(cls.root))
        cls.bundle = cls.root / "bundle"
        cls.spec_id = gate.prepare(gate.REPO / "verification/increment/spec/Spec.v",
                                  cls.bundle, cls.runtime, cls.sandbox, [])

    @classmethod
    def tearDownClass(cls):
        if hasattr(cls.sandbox, "close"):
            cls.sandbox.close()
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

    def test_checker_change_invalidates_acceptance_but_preserves_compiler_identity(self):
        if self.backend != "wasi":
            self.skipTest("WASI compiler identity")
        before = gate.toolchain(self.backend)
        original_digest = gate.digest
        checker = gate.WASI_BIN / "spec-check.wasm"
        with patch.object(gate, "digest", side_effect=lambda path:
                          "0" * 64 if Path(path) == checker else original_digest(path)):
            changed = gate.toolchain(self.backend)
        self.assertNotEqual(before["fingerprint"], changed["fingerprint"])
        self.assertEqual(before["compiler_fingerprint"], changed["compiler_fingerprint"])

    def test_vm_large_unary_computation_and_kernel_recheck(self):
        computations = "Definition vm_n0 := 1.\n" + "\n".join(
            f"Definition vm_n{i} := vm_n{i-1} + vm_n{i-1}." for i in range(1, 18))
        self.evaluate(VALID + computations + """
Fixpoint vm_collapse (n : nat) := match n with O => O | S n => vm_collapse n end.
Definition vm_zero := Eval vm_compute in vm_collapse vm_n17.
Example vm_checked : vm_collapse vm_n17 = 0.
Proof. vm_compute. reflexivity. Qed.
Example vm_result_checked : vm_zero = 0.
Proof. reflexivity. Qed.
""", accepted=True)

    def test_vm_false_equality_is_rejected(self):
        self.evaluate(VALID + """
Example vm_false : 1 = 0.
Proof. vm_compute. reflexivity. Qed.
""", reason="Unable to unify")

    def test_vm_original_uint63_and_float_primitives_compile_under_strict_axiom_policy(self):
        # Kernel primitives are bodyless constants in upstream's assumption
        # report. Keep this fixture's empty axiom policy: require successful
        # VM compilation, then rejection during the independent policy audit.
        report = self.evaluate(VALID + """
From Corelib Require Import PrimInt63 PrimFloat.
Example vm_int_limb_boundary :
  PrimInt63.add 4611686018427387903%uint63 1%uint63 = 4611686018427387904%uint63.
Proof. vm_compute. reflexivity. Qed.
Example vm_int_wrap :
  PrimInt63.add 9223372036854775807%uint63 1%uint63 = 0%uint63.
Proof. vm_compute. reflexivity. Qed.
Example vm_float_add : PrimFloat.add 1.5%float 2.25%float = 3.75%float.
Proof. vm_compute. reflexivity. Qed.
Example vm_float_sqrt : PrimFloat.sqrt 4%float = 2%float.
Proof. vm_compute. reflexivity. Qed.
Example vm_float_nan :
  PrimFloat.eqb (PrimFloat.div 0%float 0%float) (PrimFloat.div 0%float 0%float) = false.
Proof. vm_compute. reflexivity. Qed.
""", reason="Unapproved axiom")
        self.assertEqual(report["stage"], "kernel-and-contract")
        self.assertIn("Candidate.vo", report["artifacts"])

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

    def test_source_load_dependency(self):
        source = VALID.replace("Module Implementation.", 'Load "/inputs/ZHelper.v".\nModule Implementation.')
        source = source.replace("nat -> nat := S", "nat -> nat := successor")
        self.evaluate(source, {"ZHelper.v": "Definition successor := S.\n"}, accepted=True)

    def test_wasi_subtree_cache_tracks_actual_helper_dependencies(self):
        if self.runtime.get("backend") != "wasi":
            self.skipTest("WASI subtree cache")
        with tempfile.TemporaryDirectory(dir=self.root) as temporary:
            root = Path(temporary)
            inputs = root / "inputs"
            inputs.mkdir()
            (inputs / "Candidate.v").write_text(
                VALID.replace("Require Trusted.Spec.", "Require Trusted.Spec Submission.ZHelper.")
                     .replace("nat -> nat := S", "nat -> nat := Submission.ZHelper.successor"))
            (inputs / "ZHelper.v").write_text("Definition successor := S.\n")
            (inputs / "Unrelated.v").write_text("Definition unused := 1.\n")
            sandbox = gate.make_sandbox(dict(gate.DEFAULT_LIMITS), runtime=self.runtime,
                                        cache_directory=root / "cache")
            try:
                def compile_batch():
                    return gate.compile_sources(inputs, ["Candidate.v", "ZHelper.v", "Unrelated.v"],
                                                "Submission", self.bundle, self.runtime, sandbox)
                with patch.object(sandbox, "_exchange", wraps=sandbox._exchange) as exchange:
                    first = compile_batch()
                requests = [call.args[0] for call in exchange.call_args_list
                            if "compile-safe." in call.args[0]["module"]]
                self.assertEqual(len(requests), 3)
                self.assertEqual(sum("files" in request for request in requests), 1)
                self.assertFalse(any(path.startswith("/inputs/")
                                     for path in requests[0]["files"]))
                overlays = {request["args"][-1]: set(request["overlay"]) for request in requests}
                self.assertEqual(overlays["/inputs/Unrelated.v"], {"/inputs/Unrelated.v"})
                self.assertEqual(overlays["/inputs/ZHelper.v"], {"/inputs/ZHelper.v"})
                self.assertEqual(overlays["/inputs/Candidate.v"],
                                 {"/inputs/Candidate.v", "/inputs/ZHelper.v", "/work/ZHelper.vo"})
                self.assertEqual(sandbox.cache.misses, 3)
                self.assertEqual(compile_batch(), first)
                self.assertEqual(sandbox.cache.hits, 3)
                (inputs / "Unrelated.v").write_text("Definition unused := 2.\n")
                compile_batch()
                self.assertEqual((sandbox.cache.hits, sandbox.cache.misses), (5, 4))
                (inputs / "ZHelper.v").write_text("Definition successor (n : nat) := 1 + n.\n")
                compile_batch()
                self.assertEqual((sandbox.cache.hits, sandbox.cache.misses), (6, 6))
            finally:
                sandbox.close()

    def test_lazy_library_preserves_frozen_contract_and_axiom_policy(self):
        if self.runtime.get("backend") != "wasi":
            self.skipTest("WASI library provisioning")
        source = VALID.replace("Module Implementation.", r'''
From Stdlib Require Import Classical_Prop.
Lemma extra_classical (P : Prop) : P \/ ~ P.
Proof. exact (classic P). Qed.
Module Implementation.''')
        # Cold independent checking includes the classical library's entire
        # proof closure, even though the submission itself is tiny.
        limits = self.sandbox.limits
        sandbox = self.sandbox
        self.sandbox = gate.make_sandbox(dict(limits, cpu_seconds=600,
            wall_seconds=1200, memory_mib=4096, fuel=2_000_000_000_000),
            self.backend, runtime=self.runtime, cache_directory=fixture_cache(self.root))
        try:
            self.evaluate(source, reason="Unapproved axiom")
        finally:
            self.sandbox.close()
            self.sandbox = sandbox
        self.assertEqual(gate.toolchain(), self.runtime)
        self.evaluate(VALID, accepted=True)

    def test_wasi_example_retry_resumes_completed_prefixes_in_fresh_stores(self):
        if self.runtime.get("backend") != "wasi":
            self.skipTest("WASI checked-prefix retry")
        import examples
        with tempfile.TemporaryDirectory(dir=self.root) as temporary:
            root = Path(temporary)
            candidate = root / "candidate"
            candidate.mkdir()
            (candidate / "Candidate.v").write_text(VALID)
            sandbox = gate.make_sandbox(dict(gate.DEFAULT_LIMITS), runtime=self.runtime,
                                        cache_directory=root / "cache")
            original = sandbox.invoke
            checkpoint = False
            failed = False
            def resource_failure_after_progress(module, argv, *args, **kwargs):
                nonlocal checkpoint, failed
                if module == "spec-check":
                    if checkpoint and not failed:
                        failed = True
                        sandbox.close()
                        raise gate.Rejected("Sandbox wall time limit exceeded")
                    argv = [*argv[:-1], "0.5"]
                result = original(module, argv, *args, **kwargs)
                if module == "spec-check" and b'"prefix-checked"' in result["stdout"]:
                    checkpoint = True
                return result
            try:
                with patch.object(examples, "check", gate), patch.object(
                        sandbox, "invoke", side_effect=resource_failure_after_progress):
                    report, attempts = examples.evaluate_with_checkpoints(
                        self.bundle, self.spec_id, candidate, root / "result",
                        self.runtime, sandbox, 2)
                self.assertTrue(failed)
                self.assertEqual((report["status"], attempts), ("accepted", 2), report)
                self.assertEqual(report["axioms"], [])
                rejected = json.loads((root / "attempt-1/report.json").read_bytes())
                self.assertEqual(rejected["status"], "rejected")
                self.assertEqual(rejected["stage"], "kernel-and-contract")
                self.assertIn("Candidate.vo", rejected["artifacts"])
            finally:
                sandbox.close()

    def test_wasi_example_retry_resumes_completed_compiler_modules(self):
        if self.runtime.get("backend") != "wasi":
            self.skipTest("WASI compiler progress retry")
        import examples
        with tempfile.TemporaryDirectory(dir=self.root) as temporary:
            root = Path(temporary)
            candidate = root / "candidate"
            candidate.mkdir()
            (candidate / "Helper.v").write_text("Definition helper := 0.\n")
            (candidate / "Candidate.v").write_text(
                "From Submission Require Import Helper.\n" + VALID)
            sandbox = gate.make_sandbox(dict(gate.DEFAULT_LIMITS), runtime=self.runtime,
                                        cache_directory=root / "cache")
            original = sandbox.invoke
            compiled = 0
            failed = False
            def resource_failure_after_module(module, argv, *args, **kwargs):
                nonlocal compiled, failed
                if module == "compile-safe" and compiled and not failed:
                    failed = True
                    sandbox.close()
                    raise gate.Rejected("Sandbox wall time limit exceeded")
                result = original(module, argv, *args, **kwargs)
                if module == "compile-safe":
                    compiled += 1
                return result
            try:
                with patch.object(examples, "check", gate), patch.object(
                        sandbox, "invoke", side_effect=resource_failure_after_module):
                    report, attempts = examples.evaluate_with_checkpoints(
                        self.bundle, self.spec_id, candidate, root / "result",
                        self.runtime, sandbox, 2)
                self.assertTrue(failed)
                self.assertEqual((report["status"], attempts, compiled),
                                 ("accepted", 2, 2), report)
                self.assertEqual(report["axioms"], [])
                rejected = json.loads((root / "attempt-1/report.json").read_bytes())
                self.assertEqual(rejected["stage"], "compilation")
            finally:
                sandbox.close()

    def test_wasi_checked_prefix_reuse_and_hidden_axiom_invalidation(self):
        if self.runtime.get("backend") != "wasi":
            self.skipTest("WASI checked prefixes")
        with tempfile.TemporaryDirectory(dir=self.root) as temporary:
            root = Path(temporary)
            sandbox = gate.make_sandbox(dict(gate.DEFAULT_LIMITS), runtime=self.runtime,
                                        cache_directory=root / "cache")
            previous = self.sandbox
            self.sandbox = sandbox
            try:
                original_invoke = sandbox.invoke
                checkpoints = []
                def short_checkpoints(module, argv, *args, **kwargs):
                    argv = [*argv[:-1], "0.5"]
                    result = original_invoke(module, argv, *args, **kwargs)
                    if b'"prefix-checked"' in result["stdout"]:
                        checkpoints.append(result)
                    return result
                with patch.object(sandbox, "invoke", side_effect=short_checkpoints) as invoke:
                    gate.kernel_check(self.bundle, None, self.runtime, sandbox, [], spec_only=True)
                first = invoke.call_args
                self.assertIn("--checked-prefix", first.args[1])
                self.assertTrue(checkpoints)
                self.assertTrue(list((root / "cache/checked-prefix").rglob("*.json")))
                shutil.rmtree(root / "cache/kernel")
                with patch.object(sandbox, "_exchange", wraps=sandbox._exchange) as exchange, \
                        patch.object(sandbox, "invoke", wraps=sandbox.invoke) as invoke:
                    gate.kernel_check(self.bundle, None, self.runtime, sandbox, [], spec_only=True)
                request = exchange.call_args.args[0]
                self.assertIn(request["snapshot"], sandbox.snapshots)
                self.assertTrue(any(path.startswith("/checked-prefix/") for path in invoke.call_args.args[2]))
                # Sealing hides an implementation's body. Reusing the checked
                # prefix must retain its opaque dependency map for the audit.
                sealed = '''
Module Type SEALED. Parameter value : nat. End SEALED.
Module Hidden : SEALED. Definition value := 0. End Hidden.
'''
                self.evaluate(VALID + sealed, accepted=True)
                self.evaluate(VALID + sealed.replace("Definition value := 0.",
                    "Axiom secret : nat. Definition value := secret."),
                    reason="Unapproved axiom")
                self.evaluate(VALID + sealed, accepted=True)
                # Damage is a miss, including certificates already restored
                # from a previous successful invocation.
                for path in (root / "cache/checked-prefix").rglob("*.json"):
                    path.write_bytes(b"damaged")
                shutil.rmtree(root / "cache/kernel")
                gate.kernel_check(self.bundle, None, self.runtime, sandbox, [], spec_only=True)
            finally:
                sandbox.close()
                self.sandbox = previous

    def test_source_cannot_create_or_replace_compiler_artifacts(self):
        helper = "From CoqCP Require Import Options.\nDefinition successor := S.\n"
        source = VALID.replace("Require Trusted.Spec.",
                               "Require Trusted.Spec Submission.AHelper.")
        source = source.replace("Module Implementation.",
                                'Print Universes "/work/AHelper.vo".\nModule Implementation.')
        self.evaluate(source, {"AHelper.v": helper},
                      reason="Sandbox command failed")

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


@unittest.skipUnless(os.environ.get("COQCP_TEST_BUBBLEWRAP") == "1",
                     "Optional native backend; set COQCP_TEST_BUBBLEWRAP=1 to test")
class SandboxTests(unittest.TestCase):
    def setUp(self):
        gate.ensure_built("bubblewrap")
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
        cls.sandbox = gate.make_sandbox(dict(gate.DEFAULT_LIMITS,
                                      wall_seconds=1200, cpu_seconds=600, memory_mib=4096,
                                      fuel=2_000_000_000_000),
                                      runtime=cls.runtime, cache_directory=fixture_cache(cls.root))
        cls.bundle = cls.root / "bundle"
        cls.spec_id = gate.prepare(
            gate.REPO / "verification/permuted-binary-strings/spec/Spec.v",
            cls.bundle, cls.runtime, cls.sandbox, gate.trusted_axioms())

    @classmethod
    def tearDownClass(cls):
        cls.sandbox.close()
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
