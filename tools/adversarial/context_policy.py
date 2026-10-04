#!/usr/bin/env python3
"""Apply the shared CI policy to a trusted coqchk --output-context summary.

This is for project CI output, not candidate-generated compiler diagnostics.
The submission gate instead audits kernel declarations directly.
"""
import json
import sys

from ci_policy import trusted_axioms

SAFE_THEORY = {
    "* Theory: Set is predicative",
    "* Theory: Rewrite rules are not allowed",
    "* Constants/Inductives relying on type-in-type: <none>",
    "* Constants/Inductives relying on unsafe (co)fixpoints: <none>",
    "* Inductives whose positivity is assumed: <none>",
}


def validate_context(summary):
    lines = [line.strip() for line in summary.splitlines() if line.strip()]
    if lines[:2] != ["CONTEXT SUMMARY", "==============="]:
        raise ValueError("Expected a standalone coqchk context summary")
    seen, axioms = set(), []
    in_axioms, axiom_section = False, False
    for line in lines[2:]:
        if line in SAFE_THEORY:
            if line in seen:
                raise ValueError("Duplicate context section")
            seen.add(line)
            in_axioms = False
        elif line in ["* Axioms:", "* Axioms: <none>"]:
            if axiom_section:
                raise ValueError("Duplicate axiom section")
            axiom_section = True
            in_axioms = line == "* Axioms:"
        elif in_axioms and not line.startswith("*"):
            axioms.append(line)
        else:
            raise ValueError("Unsafe or unrecognized context line: " + line)
    if seen != SAFE_THEORY or not axiom_section:
        raise ValueError("Incomplete context summary")
    untrusted = set(axioms) - set(trusted_axioms())
    if untrusted:
        raise ValueError("Axioms outside CI policy: " + ", ".join(sorted(untrusted)))
    return {"status": "accepted", "policy": "ci", "axioms": sorted(set(axioms))}


if __name__ == "__main__":
    try:
        print(json.dumps(validate_context(sys.stdin.read())))
    except ValueError as error:
        print(json.dumps({"status": "rejected", "reason": str(error)}))
        sys.exit(1)
