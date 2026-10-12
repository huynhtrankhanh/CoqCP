#!/usr/bin/env python3
"""Check each problem's spec/candidate pair and retain its audited artifacts."""
import argparse
import json
from pathlib import Path
import sys

import check
import example_manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    try:
        manifest = example_manifest.load()
    except (ValueError, OSError, check.Rejected) as error:
        parser.error(str(error))
    parser.add_argument("--output", type=Path, required=True, help="New output directory")
    parser.add_argument("--only", action="append",
                        choices=[entry["name"] for entry in manifest["examples"]],
                        help="Check only these problems (repeatable)")
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    check.ensure_built()
    runtime = check.toolchain()
    for entry in manifest["examples"]:
        example = entry["name"]
        if args.only and example not in args.only:
            continue
        allowed = check.trusted_axioms() if entry["axiom_policy"] == "ci" else []
        limits = dict(manifest["profiles"][entry["profile"]])
        sandbox = check.make_sandbox(limits, runtime=runtime)
        bundle = args.output / example / "bundle"
        try:
            spec_id = check.prepare(check.REPO / entry["spec"],
                                    bundle, runtime, sandbox, allowed)
            report = check.evaluate(
                bundle, spec_id, check.REPO / entry["candidate"],
                args.output / example / "result", runtime, sandbox)
        finally:
            sandbox.close()
        print(json.dumps(dict(example=example, **report)), flush=True)
        if report["status"] != "accepted":
            return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
