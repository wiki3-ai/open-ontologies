# Devcontainer for the open-ontologies verifier work: EYE (N3) + Rocq.
#
# Base: Debian `forky` (testing) by necessity, not preference.
#   * The Rocq binary (`/usr/bin/rocq`) is provided by the `coq` package from
#     version 9.2 onward. Debian **stable** (trixie) still ships coq 8.20.1,
#     which has only `coqc` and no `rocq`, so a trixie base fails at
#     `rocq --version`. That is the build error this replaces.
#   * `rocq/rocq-prover:9.2` (the official image) is **amd64-only**, so it would
#     run emulated on an Apple Silicon Mac. `debian:forky-slim` is multi-arch.
#   * `forky` is a moving target; if a rebuild ever fails, re-check the toolchain
#     print at the bottom of this file before suspecting the notebook.
FROM debian:forky-slim

ENV DEBIAN_FRONTEND=noninteractive

# The two verifiers the notebooks drive, built from source inside the container:
#   EYE  -- SWI-Prolog builds `eye/lib/eye.pvm` from eyereasoner/eye (MIT).
#   Rocq -- `coq` provides /usr/bin/rocq; OCaml + findlib link the extracted
#           checker `rocq/build/oo-horn-rocq`.
RUN apt-get update && apt-get install -y --no-install-recommends \
      python3 python3-venv python3-pip \
      swi-prolog-nox \
      coq libcoq-stdlib \
      ocaml ocaml-findlib \
      build-essential make curl git ca-certificates jq sudo \
    && rm -rf /var/lib/apt/lists/*

# JupyterLab, so the notebook runs here the way it runs on a laptop.
RUN pip install --no-cache-dir --break-system-packages jupyterlab nbformat nbclient

# A non-root user, which is what the Dev Containers tooling expects.
RUN useradd -m -s /bin/bash vscode \
 && echo 'vscode ALL=(ALL) NOPASSWD:ALL' > /etc/sudoers.d/vscode \
 && chmod 0440 /etc/sudoers.d/vscode

# Print the toolchain at build time, so a drifted base shows up in the log
# rather than at proof time. `rocq --version` here is the regression test for
# the exact failure this Dockerfile was rewritten to fix.
RUN swipl --version && rocq --version && ocaml -version && jupyter --version >/dev/null && echo 'toolchain OK'

USER vscode
WORKDIR /home/vscode
