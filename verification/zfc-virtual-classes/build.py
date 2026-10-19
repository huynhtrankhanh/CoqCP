#!/usr/bin/env python3
"""Build and independently recheck the existing partial development.

This is a development build, not acceptance against SOLUTION: unconditional
consistency remains required by the frozen specification and is not proved.
"""
import argparse
import json
from pathlib import Path
import shutil
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--rocq", default="/opt/rocq/9.3.0/bin/rocq")
    args = parser.parse_args()
    task = Path(__file__).resolve().parent
    repo = task.parents[1]
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    trusted, submitted, theories = (out / name for name in ["Trusted", "Submission", "CoqCP"])
    for directory in [trusted, submitted, theories]:
        directory.mkdir()
    flags = ["-q", "-Q", str(theories), "CoqCP", "-Q", str(trusted), "Trusted",
             "-Q", str(submitted), "Submission"]

    def compile_file(source):
        subprocess.run([args.rocq, "compile", *flags, str(source)], cwd=out, check=True)

    target = theories / "Options.v"
    shutil.copy2(repo / "theories" / target.name, target)
    compile_file(target)
    # The object theory is evaluator-owned specification material, not a
    # shared CoqCP library or a candidate-provided proof development.
    for name in ["SetTheory", "VirtualClasses"]:
        target = trusted / f"{name}.v"
        shutil.copy2(task / "spec" / target.name, target)
        compile_file(target)
    shutil.copy2(task / "spec/Spec.v", trusted / "Spec.v")
    compile_file(trusted / "Spec.v")
    for name in ["Elimination", "Checker", "Regression", "Semantics", "StableSets",
                 "InnerModels", "Constructibility", "ConstructibleModel", "Model", "ClassNames", "Arena", "NamedSessions", "Candidate"]:
        target = submitted / f"{name}.v"
        shutil.copy2(task / "candidate" / target.name, target)
        compile_file(target)
    subprocess.run([args.rocq, "check", "-silent", "-o", *flags[1:], "Submission.Candidate"],
                   cwd=out, check=True)
    audit = out / "Audit.v"
    audit.write_text("From CoqCP Require Import Options.\n"
                     "From Submission Require Import Candidate Model InnerModels Constructibility ConstructibleModel ClassNames Arena NamedSessions.\n"
                     "Print Assumptions NamedSessions.bounded_session_safe.\n"
                     "Print Assumptions NamedSessions.named_set_certificate_is_a_theorem.\n"
                     "Print Assumptions NamedSessions.nested_iteration_budget.\n"
                     "Print Assumptions Arena.intern_correct.\n"
                     "Print Assumptions Arena.modus_ponens_sound.\n"
                     "Print Assumptions Arena.generalize_sound.\n"
                     "Print Assumptions Arena.modus_ponens_on_ids.\n"
                     "Print Assumptions Arena.generalize_on_ids.\n"
                     "Print Assumptions ClassNames.step_safe.\n"
                     "Print Assumptions ClassNames.set_variables_are_sets.\n"
                     "Print Assumptions ClassNames.bounded_classes_are_sets.\n"
                     "Print Assumptions Implementation.correct_steps.\n"
                     "Print Assumptions Implementation.correct_sessions.\n"
                     "Print Assumptions Implementation.complete.\n"
                     "Print Assumptions Implementation.classes_conservative.\n"
                     "Print Assumptions Implementation.full_contract_obligation.\n"
                     "Print Assumptions TreeModel.validates_separation.\n"
                     "Print Assumptions TreeModel.validates_infinity.\n"
                     "Print Assumptions TreeModel.consistency_if_remaining_axioms.\n"
                     "Print Assumptions InnerModels.interpretation.\n"
                     "Print Assumptions InnerModels.consistency_from_inner_model.\n"
                     "Print Assumptions Constructibility.defined_subset_membership.\n"
                     "Print Assumptions Constructibility.hierarchy_transitive.\n"
                     "Print Assumptions Constructibility.empty_constructible.\n"
                     "Print Assumptions Constructibility.pair_constructible.\n"
                     "Print Assumptions Constructibility.union_constructible.\n"
                     "Print Assumptions ConstructibleModel.validates_extensionality.\n"
                     "Print Assumptions ConstructibleModel.validates_foundation.\n"
                     "Print Assumptions ConstructibleModel.validates_pairing.\n"
                     "Print Assumptions ConstructibleModel.validates_union.\n")
    compile_file(audit)
    gate = out / "FullContract.v"
    gate.write_text("From CoqCP Require Import Options.\n"
                    "Require Import Trusted.Spec Submission.Candidate.\n"
                    "Module Checked : Trusted.Spec.SOLUTION := Implementation.\n")
    result = subprocess.run([args.rocq, "compile", *flags, str(gate)], cwd=out,
                            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (out / "full-contract-rejection.log").write_text(result.stdout)
    if result.returncode == 0 or "correct" not in result.stdout or "missing" not in result.stdout:
        raise RuntimeError("Expected the full contract to reject the missing consistency proof: "
                           + result.stdout)
    (out / "development-status.json").write_text(json.dumps({
        "status": "incomplete",
        "local_kernel_recheck": "passed",
        "full_contract": "rejected_missing_correct",
        "missing_obligation": "SetTheory.consistent",
        "adversarial_sandbox_acceptance": False,
    }, indent=2) + "\n")
    shutil.copy2(task / "Extract.v", out / "Extract.v")
    compile_file(out / "Extract.v")
    shutil.copy2(task / "main.ml", out / "main.ml")
    subprocess.run(["ocamlfind", "ocamlopt", "-package", "zarith", "-linkpkg",
                    "-O2", "-o", "zfc-checker", "checker.mli", "checker.ml", "main.ml"],
                   cwd=out, check=True)
    print("INCOMPLETE: unconditional consistency is unproved; full contract rejected.")
    print(out / "zfc-checker")


if __name__ == "__main__":
    main()
