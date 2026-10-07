#!/usr/bin/env python3
"""Check each problem's spec/candidate pair and retain its audited artifacts."""
import argparse
import json
from pathlib import Path
import sys

import check


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True, help="New output directory")
    parser.add_argument("--only", action="append", choices=[
        "increment", "knapsack", "disjoint-set-union", "kth-highest-score",
        "permuted-binary-strings", "koxia-and-bracket", "watermelon",
        "restore-three-numbers"], help="Check only these problems (repeatable)")
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    check.ensure_built()
    runtime = check.toolchain()
    for example, allowed in [
        ("increment", []),
        ("watermelon", []),
        ("restore-three-numbers", []),
        ("knapsack", check.trusted_axioms()),
        ("disjoint-set-union", check.trusted_axioms()),
        ("kth-highest-score", check.trusted_axioms()),
        ("permuted-binary-strings", check.trusted_axioms()),
        ("koxia-and-bracket", check.trusted_axioms()),
    ]:
        if args.only and example not in args.only:
            continue
        # The complete Koxia submission includes its former project proof chain.
        limits = dict(check.DEFAULT_LIMITS)
        if example != "increment":
            limits.update(wall_seconds=600, cpu_seconds=180, memory_mib=4096)
        if example == "koxia-and-bracket":
            limits.update(wall_seconds=1800, cpu_seconds=180, memory_mib=4096)
        sandbox = check.Sandbox(limits)
        problem = check.REPO / "verification" / example
        bundle = args.output / example / "bundle"
        spec_id = check.prepare(problem / "spec/Spec.v",
                                bundle, runtime, sandbox, allowed)
        report = check.evaluate(bundle, spec_id, problem / "candidate",
                                args.output / example / "result", runtime, sandbox)
        print(json.dumps(dict(example=example, **report)), flush=True)
        if report["status"] != "accepted":
            return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
