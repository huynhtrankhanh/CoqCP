#!/usr/bin/env python3
"""Apply the shared CI policy to a trusted rocq check --output-context summary.

This is for project CI output, not candidate-generated compiler diagnostics.
The submission gate instead audits kernel declarations directly.
"""
import json
import sys

from ci_policy import trusted_axioms, trusted_inductives

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
        raise ValueError("Expected a standalone Rocq context summary")
    seen = set()
    sections = {"Axioms": [], "Inductives relying on indices not mattering": []}
    section_seen, active = set(), None
    for line in lines[2:]:
        if line in SAFE_THEORY:
            if line in seen:
                raise ValueError("Duplicate context section")
            seen.add(line)
            active = None
        elif any(line in ["* " + name + ":", "* " + name + ": <none>"] for name in sections):
            name = next(name for name in sections if line.startswith("* " + name + ":"))
            if name in section_seen:
                raise ValueError("Duplicate context section")
            section_seen.add(name)
            active = name if line == "* " + name + ":" else None
        elif active and not line.startswith("*"):
            sections[active].append(line)
        else:
            raise ValueError("Unsafe or unrecognized context line: " + line)
    if seen != SAFE_THEORY or section_seen != set(sections):
        raise ValueError("Incomplete context summary")
    axioms = sections["Axioms"]
    inductives = sections["Inductives relying on indices not mattering"]
    untrusted = set(axioms) - set(trusted_axioms())
    if untrusted:
        raise ValueError("Axioms outside CI policy: " + ", ".join(sorted(untrusted)))
    untrusted = set(inductives) - set(trusted_inductives())
    if untrusted:
        raise ValueError("Inductives outside CI policy: " + ", ".join(sorted(untrusted)))
    return {"status": "accepted", "policy": "ci", "axioms": sorted(set(axioms)),
            "indices_not_mattering": sorted(set(inductives))}


if __name__ == "__main__":
    try:
        print(json.dumps(validate_context(sys.stdin.read())))
    except ValueError as error:
        print(json.dumps({"status": "rejected", "reason": str(error)}))
        sys.exit(1)
