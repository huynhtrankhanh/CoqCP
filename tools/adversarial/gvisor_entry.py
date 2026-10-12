"""Evaluator-owned entry point: verify gVisor before executing any input."""
import os
from pathlib import Path
import sys


def main():
    if not Path("/proc/gvisor/kernel_is_gvisor").is_file():
        raise RuntimeError("No safe condition for sandbox: gVisor marker missing")
    if os.getuid() == 0 or os.geteuid() == 0:
        raise RuntimeError("No safe condition for sandbox: guest must be non-root")
    # The Docker image and guest environment are evaluator-owned. No host
    # environment variables, startup files, or writable host mounts are used.
    os.execv(sys.argv[1], sys.argv[1:])


if __name__ == "__main__":
    main()
