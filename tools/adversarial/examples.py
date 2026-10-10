#!/usr/bin/env python3
"""Check each problem's spec/candidate pair and retain its audited artifacts."""
import argparse
import json
from pathlib import Path
import sys

import check
import example_manifest


def completed_cache_files(sandbox, stage):
    cache = getattr(sandbox, "cache", None)
    if cache is None or cache.directory is None:
        return set()
    category = "compile" if stage == "compilation" else "checked-prefix"
    return set((cache.directory / category).glob("**/*.json"))


def evaluate_with_checkpoints(bundle, spec_id, candidate, output, runtime, sandbox, attempts):
    """Retry bounded operations only after completed compiler/checker progress."""
    for attempt in range(1, attempts + 1):
        before = {stage: completed_cache_files(sandbox, stage)
                  for stage in ("compilation", "kernel-and-contract")}
        report = check.evaluate(bundle, spec_id, candidate, output, runtime, sandbox)
        reason = report.get("reason", "")
        stage = report.get("stage")
        resource_failure = reason in ("Sandbox wall time limit exceeded",
                                      "Sandbox CPU time limit exceeded") or (
            "wasm trap: all fuel consumed by WebAssembly" in reason)
        if (report["status"] == "accepted" or attempt == attempts or
                stage not in before or not resource_failure or
                not completed_cache_files(sandbox, stage) - before[stage]):
            return report, attempt
        # Keep the failed report/artifacts for review, and give the next bounded
        # operation a fresh result directory. Cached declarations still undergo
        # the final contract and axiom audit before acceptance.
        output.rename(output.with_name("attempt-" + str(attempt)))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    try:
        manifest = example_manifest.load()
    except (ValueError, OSError, check.Rejected) as error:
        parser.error(str(error))
    parser.add_argument("--output", type=Path, required=True, help="New output directory")
    parser.add_argument("--backend", choices=["wasi", "bubblewrap"], default="wasi")
    parser.add_argument("--cache", type=Path, default=check.REPO / ".verification/wasi-cache")
    parser.add_argument("--no-cache", action="store_true")
    parser.add_argument("--only", action="append",
                        choices=[entry["name"] for entry in manifest["examples"]],
                        help="Check only these problems (repeatable)")
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    check.ensure_built(args.backend)
    runtime = check.toolchain(args.backend)
    for entry in manifest["examples"]:
        example = entry["name"]
        if args.only and example not in args.only:
            continue
        allowed = check.trusted_axioms() if entry["axiom_policy"] == "ci" else []
        limits = dict(manifest["profiles"][entry["profile"]])
        sandbox = check.make_sandbox(limits, args.backend, runtime=runtime,
                                     cache_directory=None if args.no_cache else args.cache)
        bundle = args.output / example / "bundle"
        try:
            spec_id = check.prepare(check.REPO / entry["spec"],
                                    bundle, runtime, sandbox, allowed)
            report, attempts = evaluate_with_checkpoints(
                bundle, spec_id, check.REPO / entry["candidate"],
                args.output / example / "result", runtime, sandbox, manifest["operation_attempts"])
        finally:
            if hasattr(sandbox, "close"):
                sandbox.close()
        print(json.dumps(dict(example=example, attempts=attempts, **report)), flush=True)
        if report["status"] != "accepted":
            return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
