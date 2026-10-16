#!/usr/bin/env python3
"""Compile in a fresh output directory; leave spec/candidate source only."""
import argparse
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
    trusted = out / "Trusted"
    submitted = out / "Submission"
    trusted.mkdir()
    submitted.mkdir()
    shutil.copy2(task / "spec/Spec.v", trusted / "Spec.v")
    flags = [args.rocq, "compile", "-q", "-R", str(repo / "theories"), "CoqCP",
             "-Q", str(trusted), "Trusted", "-Q", str(submitted), "Submission"]

    def compile_file(source):
        subprocess.run([*flags, str(source)], cwd=out, check=True)

    compile_file(trusted / "Spec.v")
    for name in ["Bits", "Tree", "Threshold", "Simulation", "Search", "Algorithm",
                 "ByteIO", "MainIO", "Candidate"]:
        target = submitted / f"{name}.v"
        shutil.copy2(task / "candidate" / target.name, target)
        compile_file(target)
    shutil.copy2(task / "Extract.v", out / "Extract.v")
    compile_file(out / "Extract.v")
    shutil.copy2(task / "main.ml", out / "main.ml")
    subprocess.run(["ocamlfind", "ocamlopt", "-package", "zarith", "-linkpkg",
                    "-O3", "-o", "sorting-subarrays", "solver.mli",
                    "solver.ml", "main.ml"], cwd=out, check=True)
    print(out / "sorting-subarrays")


if __name__ == "__main__":
    main()
