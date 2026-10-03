#!/usr/bin/env bash
# Development-only replacement for landrun. THIS DOES NOT SANDBOX COMMANDS.
# Used only when run-comparator.sh is explicitly given --development.
set -euo pipefail
while (($#)); do
  case "$1" in
    --best-effort|-ldd|-add-exec) shift ;;
    --ro|--rw|--rwx|--rox|--env) shift 2 ;;
    lake|lean4export) exec "$@" ;;
    *) echo "Unsupported Comparator development-runner argument: $1" >&2; exit 2 ;;
  esac
done
exit 2
