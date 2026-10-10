#!/usr/bin/env bash
# Install trusted dependencies outside the repository and the user's home.
set -euo pipefail
task_repo=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
export OPAMROOT=/opt/rocq
task_switch=9.3.0
unset OPAMSWITCH OCAMLFIND_CONF
if [[ ! -d "$OPAMROOT" || ! -w "$OPAMROOT" ]]; then
  echo 'Create /opt/rocq with write access for the installing user first.' >&2
  exit 1
fi
if [[ ! -f "$OPAMROOT/config" ]]; then
  opam init --bare --no-setup --yes default https://opam.ocaml.org
fi
if ! opam repository list --all --short | awk '$0 == "rocq-released" {found=1} END {exit !found}'; then
  opam repository add rocq-released https://rocq-prover.org/opam/released --dont-select --yes
fi
if [[ ! -d "$OPAMROOT/$task_switch/.opam-switch" ]]; then
  opam switch create "$task_switch" ocaml-base-compiler.5.4.0 --yes --jobs=2
fi
opam repository set-repos rocq-released default --switch="$task_switch" --yes
# Prefer the switch's libraries over libraries from an older system Coq.
export OCAMLPATH="$OPAMROOT/$task_switch/lib"
opam install "$task_repo/coqcp-toolchain.opam" --switch="$task_switch" --deps-only --yes --jobs=2
echo 'Toolchain installed. Use: export PATH=/opt/rocq/9.3.0/bin:$PATH'
