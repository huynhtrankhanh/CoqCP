#!/usr/bin/env python3
"""Check each problem's spec/candidate pair and retain its audited artifacts."""
import argparse
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile

import check
import example_manifest


def prepare_example(entry, bundle, runtime, sandbox, allowed):
    spec = check.REPO / entry["spec"]
    dependencies = [spec.parent / name for name in entry.get("spec_dependencies", [])]
    if "generated_program" not in entry:
        return check.prepare(spec, bundle, runtime, sandbox, allowed,
                             spec_dependencies=dependencies)
    # The generator, input program and helper are evaluator-selected. The
    # candidate never supplies code for this frozen specification dependency.
    if (entry["generated_program"] != "zfc-proofchecker" or
            entry["spec"] != "verification/zfc-virtual-classes/spec/Spec.v"):
        raise check.Rejected("Unknown generated program")
    sources = check.specification_sources(spec, dependencies)
    if "ProofChecker.v" in sources:
        raise check.Rejected("Generated specification dependency conflicts with source")
    # This evaluator-owned signature fixes both the generated entry point and
    # the pure capacity predicate. The ordinary Spec.v stays independent of
    # generated program build order.
    interface = spec.parent / "AdversarialInterface.inc"
    sources["Spec.v"] += b"\n" + check.read_regular(interface, 1024 * 1024)
    with tempfile.TemporaryDirectory(prefix="zfc-trusted-spec-") as temporary:
        directory = Path(temporary)
        for name, data in sources.items():
            (directory / name).write_bytes(data)
        generated = directory / "ProofChecker.v"
        subprocess.run(["node", str(check.REPO / "compiler/dist/cli.js"), str(generated),
                        str(directory / "checker.cpp"),
                        str(check.REPO / "programs/ZFCProofChecker.js"),
                        str(check.REPO / "programs/IO/PrintInt64.js")],
                       cwd=check.REPO, check=True)
        return check.prepare(directory / "Spec.v", bundle, runtime, sandbox, allowed,
                             spec_dependencies=[directory / name for name in sources if name != "Spec.v"] + [generated])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    try:
        manifest = example_manifest.load()
    except (ValueError, OSError, check.Rejected) as error:
        parser.error(str(error))
    parser.add_argument("--output", type=Path, required=True, help="New output directory")
    parser.add_argument("--cache", type=Path, default=check.DEFAULT_CACHE,
                        help="Evaluator-owned compilation and validation cache")
    parser.add_argument("--no-cache", action="store_true", help="Recompile and recheck every input")
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
        sandbox = check.make_sandbox(limits, runtime=runtime,
                                     cache_directory=None if args.no_cache else args.cache)
        bundle = args.output / example / "bundle"
        try:
            spec_id = prepare_example(entry, bundle, runtime, sandbox, allowed)
            with tempfile.TemporaryDirectory(prefix="adversarial-submission-") as temporary:
                candidate = check.REPO / entry["candidate"]
                if entry.get("candidate_layout") == "zfc-native-proof":
                    path = check.REPO / "verification/zfc-virtual-classes/imperative/prepare_adversarial.py"
                    module_spec = importlib.util.spec_from_file_location("zfc_adversarial_staging", path)
                    module = importlib.util.module_from_spec(module_spec)
                    module_spec.loader.exec_module(module)
                    candidate = Path(temporary) / "candidate"
                    module.stage(candidate)
                report = check.evaluate(bundle, spec_id, candidate,
                                        args.output / example / "result", runtime, sandbox)
        finally:
            sandbox.close()
        print(json.dumps(dict(example=example, **report)), flush=True)
        if report["status"] != "accepted":
            return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
