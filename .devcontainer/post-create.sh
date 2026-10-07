#!/usr/bin/env bash
# post-create.sh -- build the verifier artifacts the notebooks use.
#
# Both are BUILD artifacts and are gitignored: `lib/eye.pvm` is a SWI-Prolog
# image and `rocq/build/oo-horn-rocq` is a linked OCaml binary. Building them
# here means a fresh devcontainer is usable without a manual step, and it keeps
# the binaries out of git -- the same split open-ontologies uses for its Lean
# `oo-cert`, which the Try It page fetches as a pinned release asset.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

if command -v swipl >/dev/null 2>&1; then
  echo "== eye: building the EYE reasoner image =="
  (cd "$root/eye" && bash build_eye.sh)
else
  echo "!! swipl not found; skipping eye.pvm (install swi-prolog-nox)" >&2
fi

if command -v rocq >/dev/null 2>&1; then
  echo "== rocq: proving, auditing and extracting oo-horn-rocq =="
  (cd "$root/rocq" && bash build.sh)
else
  echo "!! rocq not found; skipping oo-horn-rocq (install coq + ocaml)" >&2
fi

echo "done. Start JupyterLab with: jupyter lab --ip=0.0.0.0 --port=8888"
