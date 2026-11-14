#!/usr/bin/env bash
# Install the current Rocq master and compatible libraries outside the repository.
set -euo pipefail
task_repo=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
export OPAMROOT=/opt/rocq
task_switch=master
unset OPAMSWITCH OCAMLFIND_CONF
if [[ ! -d "$OPAMROOT" || ! -w "$OPAMROOT" ]]; then
  echo 'Create /opt/rocq with write access for the installing user first.' >&2
  exit 1
fi
if [[ ! -f "$OPAMROOT/config" ]]; then
  opam init --bare --no-setup --yes default https://opam.ocaml.org
fi
if [[ ! -d "$OPAMROOT/$task_switch/.opam-switch" ]]; then
  opam switch create "$task_switch" ocaml-base-compiler.5.4.0 --yes --jobs=4
fi
if ! opam repository list --all --short | awk '$0 == "rocq-core-dev" {found=1} END {exit !found}'; then
  opam repository add rocq-core-dev https://rocq-prover.org/opam/core-dev --dont-select --yes
fi
if ! opam repository list --all --short | awk '$0 == "rocq-extra-dev" {found=1} END {exit !found}'; then
  opam repository add rocq-extra-dev https://rocq-prover.org/opam/extra-dev --dont-select --yes
fi
if ! opam repository list --all --short | awk '$0 == "rocq-released" {found=1} END {exit !found}'; then
  opam repository add rocq-released https://rocq-prover.org/opam/released --dont-select --yes
fi
opam repository set-repos rocq-core-dev rocq-extra-dev rocq-released default --switch="$task_switch" --yes
opam update --switch="$task_switch"
# Remove pins left by older versions of this installer.
for task_package in rocq-core rocq-runtime; do
  if opam pin list --switch="$task_switch" --short | grep -Fxq "$task_package"; then
    opam pin remove "$task_package" --switch="$task_switch" --no-action --yes
  fi
done
# The development repository can lag master. Override only its source URL;
# retain upstream's package metadata and follow the branch, without opam pins.
task_overlay="$OPAMROOT/rocq-master-overlay"
mkdir -p "$task_overlay/packages"
printf 'opam-version: "2.0"\n' > "$task_overlay/repo"
for task_package in rocq-runtime rocq-core; do
  task_dir="$task_overlay/packages/$task_package/$task_package.dev"
  mkdir -p "$task_dir"
  opam show "$task_package.dev" --switch="$task_switch" --raw > "$task_dir/opam"
  python3 - "$task_dir/opam" <<'PY'
import pathlib, re, sys
path = pathlib.Path(sys.argv[1])
content = path.read_text()
content, count = re.subn(r'url\s*\{[^}]*\}', 'url { src: "git+https://github.com/rocq-prover/rocq.git#master" }', content, count=1, flags=re.S)
if count != 1:
    raise SystemExit('Upstream package has no source URL')
path.write_text(content)
PY
done
if ! opam repository list --all --short | grep -Fxq rocq-master-overlay; then
  opam repository add rocq-master-overlay "$task_overlay" --dont-select --yes
fi
opam repository set-repos rocq-master-overlay rocq-core-dev rocq-extra-dev rocq-released default --switch="$task_switch" --yes
opam update rocq-master-overlay --switch="$task_switch"
task_commit=$(git ls-remote https://github.com/rocq-prover/rocq.git refs/heads/master | cut -f1)
[[ "$task_commit" =~ ^[0-9a-f]{40}$ ]]
# A failed or interrupted update must never leave a valid-looking identity.
rm -f "$OPAMROOT/$task_switch/rocq-master-commit"
export OCAMLPATH="$OPAMROOT/$task_switch/lib"
opam install "$task_repo/coqcp-toolchain.opam" --switch="$task_switch" --deps-only --yes --jobs=4
opam reinstall rocq-runtime.dev rocq-core.dev --switch="$task_switch" --yes --jobs=4
task_after=$(git ls-remote https://github.com/rocq-prover/rocq.git refs/heads/master | cut -f1)
for task_package in rocq-runtime rocq-core; do
  task_installed=$(git -C "$OPAMROOT/$task_switch/.opam-switch/sources/$task_package.dev" rev-parse HEAD)
  if [[ "$task_after" != "$task_commit" || "$task_installed" != "$task_commit" ]]; then
    echo 'Rocq master or the installed source changed during installation; rerun the installer.' >&2
    exit 1
  fi
done
printf '%s\n' "$task_commit" > "$OPAMROOT/$task_switch/rocq-master-commit"
echo 'Toolchain installed. Use: export PATH=/opt/rocq/master/bin:$PATH'
