#!/usr/bin/env python3
"""Stage the native proof closure in the adversarial Submission namespace.

The generated checker itself is supplied separately by the evaluator as
Trusted.ProofChecker; this script never selects or generates the program.
"""
import argparse
from pathlib import Path
import re


PROOF = Path(__file__).resolve().parent / "proof"
IMPORT = re.compile(r"From NativeProof Require (Import|Export) ([^.]+)\.")
CODE = re.compile(r"From ImperativeZFC Require (Import|Export) ([^.]+)\.")


def stage(output):
    output.mkdir(parents=True, exist_ok=False)
    pending = ["AdversarialCapacityBridge"]
    seen = set()
    while pending:
        name = pending.pop()
        if name in seen:
            continue
        if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", name) is None:
            raise ValueError("Invalid proof module name")
        text = (PROOF / (name + ".v")).read_text()
        seen.add(name)
        for _, names in IMPORT.findall(text):
            pending.extend(names.split())
        text = IMPORT.sub(lambda m: "From Submission Require " + m[1] + " " + m[2] + ".", text)
        def code_import(match):
            names = match[2].split()
            if set(names) - {"ProofChecker", "NativeContract"}:
                raise ValueError("Unexpected generated-code dependency")
            return "\n".join("From " + ("Trusted" if n == "ProofChecker" else "Submission") +
                             " Require " + match[1] + " " + n + "." for n in names)
        text = CODE.sub(code_import, text)
        (output / (name + ".v")).write_text(text)
    (output / "NativeContract.v").write_text(
        "From CoqCP Require Import Options Imperative Execution.\n"
        "From Trusted Require Import Spec ProofChecker.\n"
        "Definition native_contract capacity := Trusted.Spec.required\n"
        "  (funcdef_0__main (fun x => match x with end) (fun x => match x with end))\n"
        "  (arrays _ environment1) capacity.\n")
    (output / "Candidate.v").write_text(
        "From CoqCP Require Import Options Imperative Execution.\n"
        "From Trusted Require Import Spec Capacity ProofChecker.\n"
        "From Submission Require Import AdversarialCapacityBridge.\n"
        "Module Implementation.\n"
        "Definition program := funcdef_0__main (fun x => match x with end) "
        "(fun x => match x with end).\n"
        "Theorem correct : Trusted.Spec.required program (arrays _ environment1) "
        "Trusted.Capacity.within_capacity.\n"
        "Proof. exact AdversarialCapacityBridge.native_required. Qed.\n"
        "End Implementation.\n")
    return len(seen)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    print(f"Staged {stage(args.output)} native proof modules")
