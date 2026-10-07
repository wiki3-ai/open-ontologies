#!/usr/bin/env bash
# build_eye.sh -- build the EYE reasoner image (lib/eye.pvm) from EYE's own MIT
# source, using SWI-Prolog.  This is what removes the npm dependency: the npm
# package `eyereasoner` is SWI-Prolog compiled to WebAssembly with this same EYE
# image embedded, so the native image is the same reasoner without the Node
# toolchain.  SWI-Prolog is an ordinary system package (`swi-prolog-nox`).
#
# The source is fetched at a pinned tag, the way web/try/build.sh fetches the
# pinned engine release, rather than vendored: EYE is a separate project and a
# copy of it in this tree would drift from the tag the page names.
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SWIPL="${SWIPL:-swipl}"
TAG="${EYE_TAG:-v11.24.8}"

command -v "$SWIPL" >/dev/null 2>&1 || {
  echo "SWI-Prolog not found; install it (e.g. apt-get install swi-prolog-nox) or set SWIPL." >&2
  exit 1
}

src="$here/build/eye-$TAG"
mkdir -p "$here/build" "$here/lib"
if [ ! -f "$src/eye.pl" ]; then
  url="https://github.com/eyereasoner/eye/archive/refs/tags/${TAG}.tar.gz"
  echo "fetching $url"
  tmp="$(mktemp -d)"
  trap 'rm -rf "$tmp"' EXIT
  curl -fsSL "$url" -o "$tmp/eye.tar.gz"
  tar -xzf "$tmp/eye.tar.gz" -C "$tmp"
  rm -rf "$src"
  mv "$tmp"/eye-* "$src"
fi

"$SWIPL" -q -f "$src/eye.pl" -g main -- --quiet --image "$here/lib/eye.pvm"
"$SWIPL" -x "$here/lib/eye.pvm" -- --version
echo "built $here/lib/eye.pvm"
