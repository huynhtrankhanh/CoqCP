"""Trusted build worker, run only inside Bubblewrap's bounded tmpfs.

Compiler diagnostics go to stderr. Stdout transports artifacts, never a verdict.
Every compiler/parser process gets its own limits and seccomp filter.
"""
import base64
import ctypes
import json
import os
from pathlib import Path
import stat
import subprocess
import sys


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
    for source in order:
        output = "/work/" + Path(source).with_suffix(".vo").name
        subprocess.run(prefix + ["/tool/compile-safe", "-coqlib", config["coqlib"],
                                 "-q", "-native-compiler", "no",
                                 "-async-proofs", "off", *flags, "-o", output, source],
                       stdout=sys.stderr, stderr=sys.stderr, check=True)
    artifacts = {}
    total = 0
    for source in sources:
        name = Path(source).with_suffix(".vo").name
        fd = os.open("/work/" + name, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
        with os.fdopen(fd, "rb") as stream:
            info = os.fstat(stream.fileno())
            if not stat.S_ISREG(info.st_mode):
                raise RuntimeError("Compiler output is not a regular file")
            total += info.st_size
            if total > config["artifact_mib"] * 1024 * 1024:
                raise RuntimeError("Compiled artifacts exceed the size limit")
            artifacts[name] = base64.b64encode(stream.read(info.st_size + 1)).decode("ascii")
    json.dump({"artifacts": artifacts}, sys.stdout)


if __name__ == "__main__":
    try:
        main()
    except Exception as error:
        print("Build failed: " + str(error), file=sys.stderr)
        sys.exit(1)
