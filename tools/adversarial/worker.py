"""Trusted build worker, run only inside Bubblewrap's bounded tmpfs.

Compiler diagnostics go to stderr. Stdout transports artifacts, never a verdict.
Every compiler/parser process gets its own limits and seccomp filter.
"""
import base64
import ctypes
import json
import os
from pathlib import Path
import secrets
import shutil
import stat
import subprocess
import sys


WORK = Path("/work")


def read_artifact(path, limit):
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    with os.fdopen(fd, "rb") as stream:
        info = os.fstat(stream.fileno())
        if not stat.S_ISREG(info.st_mode) or info.st_size > limit:
            raise RuntimeError("Compiler output is not a bounded regular file")
        data = stream.read(info.st_size + 1)
        if len(data) != info.st_size:
            raise RuntimeError("Compiler output changed while it was captured")
        return data


def vo_paths():
    return {str(path.relative_to(WORK)): path for path in WORK.rglob("*.vo")}


def verify_artifacts(captured, transient=None):
    expected = set(captured)
    if transient is not None:
        expected.add(str(transient.relative_to(WORK)))
    actual = vo_paths()
    if set(actual) != expected:
        raise RuntimeError("Submission created or removed a compiler artifact")
    for name, data in captured.items():
        try:
            current = read_artifact(actual[name], len(data))
        except (OSError, RuntimeError) as error:
            raise RuntimeError("Submission modified a compiler artifact") from error
        if current != data:
            raise RuntimeError("Submission modified a compiler artifact")


def main():
    # Prevent compiler children from opening this process's /proc/.../fd or mem.
    if ctypes.CDLL(None).prctl(4, 0, 0, 0, 0) != 0:  # PR_SET_DUMPABLE
        raise RuntimeError("Cannot protect the build worker")
    config = json.loads(Path("/inputs/build.json").read_text())
    flags = [part for root in config["roots"] for part in ["-Q", *root]]
    sources = ["/inputs/" + name for name in config["sources"]]
    flags += ["-Q", "/inputs", config["namespace"], "-Q", "/work", config["namespace"]]
    prefix = ["/tool/sandbox-exec", str(config["cpu_seconds"]),
              str(config["memory_mib"]), str(config["artifact_mib"])]
    # Sort only submitted sources. Mapping compiled-only trusted libraries
    # here makes rocq dep -sort try to recursively open their absent .v files.
    order = subprocess.run(prefix + [config["rocq"], "dep", "-sort", "-Q", "/inputs",
                                    config["namespace"], *sources],
                           stdout=subprocess.PIPE, stderr=sys.stderr, check=True).stdout.decode().split()
    if len(order) != len(sources) or set(order) != set(sources):
        raise RuntimeError("rocq dep returned an unexpected build order")
    artifacts = {}
    total = 0
    artifact_limit = config["artifact_mib"] * 1024 * 1024
    for source in order:
        verify_artifacts(artifacts)
        name = Path(source).with_suffix(".vo").name
        # The source knows its eventual library name, so do not let it share
        # that path with the compiler.  Coqc writes into a fresh unpredictable
        # directory; the trusted worker captures the result and publishes it
        # under its library name only after the compiler exits successfully.
        output_dir = WORK / (".coqcp-output-" + secrets.token_hex(16))
        output_dir.mkdir(mode=0o700)
        output = output_dir / name
        subprocess.run(prefix + ["/tool/compile-safe", "-coqlib", config["coqlib"],
                                 "-q", "-native-compiler", "no",
                                 "-async-proofs", "off", *flags,
                                 "-Q", str(output_dir), config["namespace"],
                                 "-o", str(output), source],
                       stdout=sys.stderr, stderr=sys.stderr, check=True)
        verify_artifacts(artifacts, output)
        data = read_artifact(output, artifact_limit - total)
        total += len(data)
        if total > artifact_limit:
            raise RuntimeError("Compiled artifacts exceed the size limit")
        destination = WORK / name
        os.replace(output, destination)
        shutil.rmtree(output_dir)
        artifacts[name] = data
        verify_artifacts(artifacts)
    json.dump({"artifacts": {name: base64.b64encode(artifacts[name]).decode("ascii")
                             for name in sorted(artifacts)}}, sys.stdout)


if __name__ == "__main__":
    try:
        main()
    except Exception as error:
        print("Build failed: " + str(error), file=sys.stderr)
        sys.exit(1)
