#!/usr/bin/env python3
"""Build the derivation-checking reference and check its full scoped contract."""
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

    for name in ["Options", "Imperative", "Execution", "InteractiveExecution", "DecimalEncoding"]:
        target = theories / f"{name}.v"
        shutil.copy2(repo / "theories" / target.name, target)
        compile_file(target)
    # The object theory is evaluator-owned specification material, not a
    # shared CoqCP library or a candidate-provided proof development.
    for name in ["SetTheory", "VirtualClasses"]:
        target = trusted / f"{name}.v"
        shutil.copy2(task / "spec" / target.name, target)
        compile_file(target)
    shutil.copy2(task / "spec/Reference.v", trusted / "Reference.v")
    compile_file(trusted / "Reference.v")
    modules = ["Elimination", "Checker", "Regression", "ClassNames", "Arena", "NamedSessions", "SchemataSoundness", "Candidate"]
    for name in ["Schemata", "Protocol", "Spec"]:
        target = trusted / f"{name}.v"
        shutil.copy2(task / "spec" / target.name, target)
        compile_file(target)
    for name in modules:
        target = submitted / f"{name}.v"
        shutil.copy2(task / "candidate" / target.name, target)
        compile_file(target)
    audited = ["Implementation.correct", "Implementation.classes_conservative",
               "ClassNames.step_safe", "NamedSessions.run_safe", "SchemataSoundness.instance_sound"]
    audit = out / "Audit.v"
    audit.write_text("From CoqCP Require Import Options.\n"
                     "From Trusted Require Import Schemata.\n"
                     "From Submission Require Import Candidate ClassNames NamedSessions SchemataSoundness.\n" +
                     "".join(f"Print Assumptions {name}.\n" for name in audited))
    result = subprocess.run([args.rocq, "compile", *flags, str(audit)], cwd=out,
                            check=True, text=True, capture_output=True)
    (out / "assumptions.log").write_text(result.stdout + result.stderr)
    if result.stdout.count("Closed under the global context") != len(audited) or "Axioms:" in result.stdout:
        raise RuntimeError("Unexpected global assumptions")
    subprocess.run([args.rocq, "check", "-silent", *flags[1:], "Submission.Candidate", "Submission.SchemataSoundness", "Trusted.Protocol"],
                   cwd=out, check=True)
    (out / "development-status.json").write_text(json.dumps({
        "reference_contract": "passed", "local_kernel_recheck": "passed",
        "native_end_to_end_refinement": "incomplete",
        "adversarial_sandbox_acceptance": False,
    }, indent=2) + "\n")
    shutil.copy2(task / "Extract.v", out / "Extract.v")
    compile_file(out / "Extract.v")
    shutil.copy2(task / "main.ml", out / "main.ml")
    subprocess.run(["ocamlfind", "ocamlopt", "-package", "zarith", "-linkpkg",
                    "-O2", "-o", "zfc-checker", "checker.mli", "checker.ml", "main.ml"],
                   cwd=out, check=True)
    print("Reference derivation contract passed; native end-to-end refinement remains open.")
    print(out / "zfc-checker")


if __name__ == "__main__":
    main()
