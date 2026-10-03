#!/usr/bin/env bash
# Run from any working directory. All generated evidence stays under .lake.
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/check_source.py
lake build
lake env lean -Dbackward.isDefEq.respectTransparency=false Verification/Audit.lean
python3 scripts/check_source.py --check-audit
