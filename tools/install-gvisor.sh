#!/usr/bin/env bash
# Install a pinned gVisor runtime and its sidecars, then build the trusted image.
set -euo pipefail
task_repo=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
task_install=/opt/rocq/gvisor
task_release=release-20261005.0
case "$(uname -m)" in
  x86_64) task_archive=gvisor-x86_64.tar.bz2
    task_sha=bd4eb2ca0ee74f0fbbb5f5273ba011e79c56a29fbb047393b88b981cd3230ede ;;
  aarch64) task_archive=gvisor-aarch64.tar.bz2
    task_sha=d0387aa061248756a201f716db25b02bf9376a278543cb96c1855644ab815a8d ;;
  *) echo 'gVisor installation supports Linux x86-64 and ARM64.' >&2; exit 1 ;;
esac
task_sudo=
if [ "$(id -u)" != 0 ]; then task_sudo=sudo; fi
task_tmp=$(mktemp -d)
trap 'rm -rf "$task_tmp"' EXIT
curl -fsSL "https://github.com/google/gvisor/releases/download/$task_release/$task_archive" \
  -o "$task_tmp/$task_archive"
echo "$task_sha  $task_tmp/$task_archive" | sha256sum --check --status
tar -xjf "$task_tmp/$task_archive" -C "$task_tmp"
$task_sudo install -d -m 755 "$task_install"
$task_sudo cp -a "$task_tmp/runsc" "$task_tmp/containerd-shim-runsc-v1" \
  "$task_tmp/gvisor-bin" "$task_install/"
$task_sudo chmod -R a+rX "$task_install"
# Preserve other daemon settings; this installs a separately named runtime.
$task_sudo "$task_install/runsc" install --runtime=coqcp-gvisor -- \
  --platform=systrap --network=none --gvisor-marker-file=true
$task_sudo systemctl restart docker
# The calling evaluator user needs access to its local Docker daemon (as on
# GitHub-hosted Ubuntu runners). The socket is never passed into the sandbox.
docker --host=unix:///var/run/docker.sock build \
  -f "$task_repo/tools/adversarial/Dockerfile.gvisor" \
  -t coqcp-gvisor:rocq-9.3.0 "$task_repo/tools/adversarial"
