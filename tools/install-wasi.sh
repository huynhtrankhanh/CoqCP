#!/usr/bin/env bash
# Install compiler dependencies and export a standalone host from Docker.
set -euo pipefail
task_repo=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
task_build_host=yes
if [[ ${1:-} == --no-host ]]; then task_build_host=no; fi
if [[ -n ${1:-} && ${1:-} != --no-host ]]; then
  echo 'Usage: tools/install-wasi.sh [--no-host]' >&2
  exit 1
fi
mkdir -p /opt/rocq/wasi
if [[ ! -x /opt/rocq/wasi/wasi-sdk-34.0-x86_64-linux/bin/clang ]]; then
  python3 "$task_repo/tools/adversarial/install_wasi_assets.py" wasi-sdk /opt/rocq/wasi
fi
opam install --root=/opt/rocq --switch=9.3.0 --yes --jobs=2 --assume-depexts num.1.6
if [[ "$task_build_host" == yes ]]; then
  bash "$task_repo/tools/build-wasi-host.sh"
  mkdir -p /opt/rocq/wasi/host
  cp -a "$task_repo/.verification/wasi-host/host/." /opt/rocq/wasi/host/
fi
