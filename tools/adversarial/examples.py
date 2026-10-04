#!/usr/bin/env python3
"""Check the shipped contracts and retain their specification/result artifacts."""
import argparse
import json
from pathlib import Path
import sys

import check


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True, help="New output directory")
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    check.ensure_built()
    runtime = check.toolchain()
    sandbox = check.Sandbox(dict(check.DEFAULT_LIMITS))
    for spec, example, allowed in [
        ("Increment", "increment", []),
        ("Knapsack", "knapsack", []),
        ("KnapsackIO", "knapsack-io", check.trusted_axioms()),
    ]:
        bundle = args.output / example / "bundle"
        spec_id = check.prepare(check.REPO / "verification/specs" / (spec + ".v"),
                                bundle, runtime, sandbox, allowed)
        report = check.evaluate(bundle, spec_id, check.REPO / "verification/examples" / example,
                                args.output / example / "result", runtime, sandbox)
        print(json.dumps(dict(example=example, **report)), flush=True)
        if report["status"] != "accepted":
            return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
