#!/usr/bin/env bash
set -euo pipefail
task_repo=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
task_output=${1:-"$task_repo/.verification/wasi-host"}
docker buildx build --platform linux/amd64 \
  --file "$task_repo/tools/adversarial/Dockerfile.wasi-host" \
  --output "type=local,dest=$task_output" "$task_repo/tools/adversarial"
