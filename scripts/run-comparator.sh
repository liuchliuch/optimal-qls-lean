#!/usr/bin/env bash
# Pin Comparator and its exporter/checker through the upstream lockfile.
set -euo pipefail
cd "$(dirname "$0")/.."
mode="${1:-}"
if [[ "$mode" != "" && "$mode" != "--development" ]]; then
  echo "Usage: $0 [--development]" >&2
  exit 2
fi
revision=e6831abb2f76b7ce6f2fb28e6410a0df878e6e4b
tooldir="$PWD/.lake/tools/comparator"
if [[ ! -d "$tooldir/.git" ]]; then
  mkdir -p "$(dirname "$tooldir")"
  git clone https://github.com/leanprover/comparator.git "$tooldir"
  git -C "$tooldir" checkout --detach "$revision"
fi
if [[ "$(git -C "$tooldir" rev-parse HEAD)" != "$revision" ]]; then
  echo "Comparator revision mismatch: expected $revision" >&2
  exit 1
fi
if [[ -n "$(git -C "$tooldir" status --porcelain --untracked-files=no)" ]]; then
  echo "Comparator checkout contains modified tracked files" >&2
  exit 1
fi
cmp lean-toolchain "$tooldir/lean-toolchain"
lake -d "$tooldir" build comparator lean4export
export PATH="$tooldir/.lake/packages/lean4export/.lake/build/bin:$PATH"
if [[ "$mode" == "--development" ]]; then
  echo "Comparator development mode: statement comparison, axiom checks and kernel replay; NO sandbox." >&2
  mkdir -p .lake/tools/comparator-dev-bin
  ln -sf "$PWD/scripts/comparator-dev-runner.sh" .lake/tools/comparator-dev-bin/landrun
  export PATH="$PWD/.lake/tools/comparator-dev-bin:$PATH"
  lake env "$tooldir/.lake/build/bin/comparator" Verification/comparator.json
else
  if [[ "$(uname -s)" != Linux ]]; then
    echo "Sandbox verification requires Linux and landrun; use --development for trusted local sources." >&2
    exit 2
  fi
  command -v landrun >/dev/null
  command -v systemd-run >/dev/null
  # Address-family restriction follows current upstream guidance for landrun.
  systemd-run --user --wait --pipe --collect --property=RestrictAddressFamilies=~AF_UNIX \
    -E "PATH=$PATH" --working-directory="$PWD" \
    lake env "$tooldir/.lake/build/bin/comparator" Verification/comparator.json
fi
