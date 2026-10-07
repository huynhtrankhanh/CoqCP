"""Freeze the IO specification, accept the end-to-end proof, and reject insufficient proofs."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import re

ROOT = Path(__file__).resolve().parents[4]
CHECKER = ROOT / "tools/adversarial/check.py"
SPEC = ROOT / "verification/koxia-and-bracket/spec/Spec.v"


def invoke(arguments):
    result = subprocess.run(arguments, cwd=ROOT, capture_output=True, text=True)
    try:
        report = json.loads(result.stdout)
    except json.JSONDecodeError as error:
        raise RuntimeError(result.stdout + result.stderr) from error
    return result.returncode, report


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True,
                        help="A fresh directory for the frozen specification and reports")
    parser.add_argument("--network-isolation", choices=["auto", "namespace", "seccomp"], default="auto")
    parser.add_argument("--cpu-seconds", type=int, default=180,
                        help="Per-process CPU budget for the complete proof dependency chain")
    parser.add_argument("--wall-seconds", type=int, default=1800)
    parser.add_argument("--memory-mib", type=int, default=4096)
    args = parser.parse_args()
    resources = ["--cpu-seconds", str(args.cpu_seconds),
                 "--wall-seconds", str(args.wall_seconds),
                 "--memory-mib", str(args.memory_mib)]
    directory = args.output.resolve()
    directory.mkdir(parents=True, exist_ok=False)
    code, prepared = invoke([
        "python3", str(CHECKER), "prepare", "--spec", str(SPEC),
        "--bundle", str(directory / "bundle"), "--axiom-policy", "ci",
        "--network-isolation", args.network_isolation,
        *resources,
    ])
    if code:
        raise RuntimeError(prepared)
    spec_id = prepared["spec_id"]
    (directory / "expected-spec-id.txt").write_text(spec_id + "\n")
    # Record the ID before submitting any source, and always use this value.
    (directory / "preparation.json").write_text(json.dumps(prepared, indent=2) + "\n")
    print("Frozen full end-to-end contract:", spec_id, flush=True)

    properties = ROOT / "verification/koxia-and-bracket/candidate"
    # All proof helpers are submitted and independently audited by the gate.
    submission = properties
    code, positive = invoke([
        "python3", str(CHECKER), "check", "--bundle", str(directory / "bundle"),
        "--spec-id", spec_id, "--submission", str(submission),
        "--output", str(directory / "solution-result"),
        "--network-isolation", args.network_isolation,
        *resources,
    ])
    if code or positive.get("status") != "accepted" or positive.get("stage") != "complete":
        raise AssertionError(("end-to-end solution", code, positive))
    print("End-to-end generated solver: accepted by the kernel and frozen contract gate", flush=True)

    header = """From CoqCP Require Import Options Imperative Execution.

From Stdlib Require Import ZArith.ZArith.
From Generated Require Import KoxiaAndBracket.
Require Trusted.Spec.
Module Implementation.
Definition program : Trusted.Spec.Program :=
  funcdef_0__main (fun _ => false) (fun _ => 0%Z).
"""
    attacks = {
        "missing-correct": header + "End Implementation.\n",
        "true-instead-of-contract": header +
            "Lemma correct : True. Proof. exact I. Qed.\nEnd Implementation.\n",
        "extra-premise": header + "Lemma correct : False -> Trusted.Spec.required program.\n"
            "Proof. intros impossible. destruct impossible. Qed.\nEnd Implementation.\n",
        "admitted": header + "Lemma correct : Trusted.Spec.required program.\n"
            "Admitted.\nEnd Implementation.\n",
        "notation-shadowing": header +
            "Notation \"'required' p\" := True (at level 10).\n"
            "Lemma correct : required program. Proof. exact I. Qed.\nEnd Implementation.\n",
        "conditional-failing-execution": """From CoqCP Require Import Options Imperative Execution.

From Stdlib Require Import ZArith.ZArith.
From Generated Require Import KoxiaAndBracket.
Require Trusted.Spec.
Module Implementation.
Definition program : Trusted.Spec.Program :=
  Dispatch _ _ _ (DoBasicEffect _ _ Trap) (fun _ => Done _ _ _ tt).
Lemma correct : forall state final, exec program state = Some (tt, final) ->
  stdout final = nil.
Proof. intros state final impossible. discriminate impossible. Qed.
End Implementation.
""",
        "abstract-algorithm-proof": """From CoqCP Require Import Options.
From Submission Require Import KoxiaPolynomial.
From Stdlib Require Import ZArith.ZArith.
From Generated Require Import KoxiaAndBracket.
Require Trusted.Spec.
Module Implementation.
Definition program : Trusted.Spec.Program :=
  funcdef_0__main (fun _ => false) (fun _ => 0%Z).
Lemma correct : forall tree p, accelerated tree p = run (treeEvents tree) p.
Proof. exact accelerated_correct. Qed.
End Implementation.
""",
        "abstract-problem-proof": """From CoqCP Require Import Options.

From Stdlib Require Import ZArith.ZArith.
From Generated Require Import KoxiaAndBracket.
Require Trusted.Spec Submission.MinimumScan Submission.FullCounting.
Module Implementation.
Definition program : Trusted.Spec.Program :=
  funcdef_0__main (fun _ => false) (fun _ => 0%Z).
Lemma correct : forall s,
  Submission.FullCounting.abstractAnswer
    (List.firstn (Submission.MinimumScan.minimumIndex s) s)
    (List.skipn (Submission.MinimumScan.minimumIndex s) s) =
  Z.of_nat (Trusted.Spec.answer s).
Proof. exact Submission.MinimumScan.computed_abstract_solver_correct. Qed.
End Implementation.
""",
    }
    reports = {}
    for name, source in attacks.items():
        submission = directory / (name + "-submission")
        submission.mkdir()
        (submission / "Candidate.v").write_text(source)
        # Assemble only the repo-owned helpers needed by each deliberately weak
        # theorem, including transitive imports in the Submission namespace.
        pending = [source]
        copied = set()
        while pending:
            text = pending.pop()
            names = set(re.findall(r"Submission\.([A-Za-z][A-Za-z0-9_]*)", text))
            for imports in re.findall(r"From Submission Require (?:Import|Export)\s+(.*?)\.",
                                      text, re.DOTALL):
                names.update(imports.split())
            for helper in sorted(names - copied):
                copied.add(helper)
                helper_source = (properties / (helper + ".v")).read_text()
                (submission / (helper + ".v")).write_text(helper_source)
                pending.append(helper_source)
        code, report = invoke([
            "python3", str(CHECKER), "check", "--bundle", str(directory / "bundle"),
            "--spec-id", spec_id, "--submission", str(submission),
            "--output", str(directory / (name + "-result")),
            "--network-isolation", args.network_isolation,
            *resources,
        ])
        if code == 0 or report.get("status") != "rejected":
            raise AssertionError((name, code, report))
        # Rejections must reach the module/axiom checker, not merely fail to
        # compile the deliberately weak theorem.
        if report.get("stage") != "kernel-and-contract":
            raise AssertionError((name, "did not reach the kernel gate", report))
        expected_reason = {
            "missing-correct": "Implementation does not satisfy Trusted.Spec.SOLUTION",
            "admitted": "Unapproved axiom: Submission.Candidate.Implementation.correct",
        }.get(name, "Signature mismatch for field correct")
        if expected_reason not in report.get("reason", ""):
            raise AssertionError((name, "unexpected rejection reason", report))
        reports[name] = report
        print(name + ": rejected by the kernel gate", flush=True)
    summary = {
        "solver_certified": True,
        "positive_submission": positive,
        "spec_id": spec_id,
        "spec_source_sha256": hashlib.sha256(SPEC.read_bytes()).hexdigest(),
        "spec_properties_checked": True,
        "abstract_polynomial_proofs_checked": True,
        "path_count_proofs_checked": True,
        "abstract_problem_correctness_checked": True,
        "modular_arithmetic_proofs_checked": True,
        "generated_power_execution_checked": True,
        "generated_input_execution_checked": True,
        "generated_ntt_execution_checked": True,
        "generated_table_initialization_checked": True,
        "generated_convolution_execution_checked": True,
        "generated_convolution_coefficients_checked": True,
        "generated_leaf_dp_checked": True,
        "generated_frame_transitions_checked": True,
        "generated_traversal_execution_checked": True,
        "generated_preprocessing_execution_checked": True,
        "generated_solve_execution_checked": True,
        "generated_main_execution_checked": True,
        "abstract_stack_schedule_checked": True,
        "storage_bounds_checked": True,
        "generated_printer_execution_checked": True,
        "review_sources_sha256": {
            path.name: hashlib.sha256(path.read_bytes()).hexdigest()
            for path in sorted(properties.glob("*.v"))
        },
        "rejected_submissions": list(reports),
        "negative_submissions": reports,
    }
    (directory / "validation-summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
