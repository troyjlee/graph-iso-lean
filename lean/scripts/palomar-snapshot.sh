#!/usr/bin/env bash
# palomar-snapshot.sh — write, check and build the Palomar submission snapshot (PLAN-19.md §7).
#
#   scripts/palomar-snapshot.sh [--draft] [--build] OUT
#
# `scripts/palomar-snapshot.py` writes OUT and checks it (see there; `--draft` accepts the draft
# metadata). With `--build`, OUT/lean then gets a copy of this repository's `.lake` (a
# copy-on-write clone where the filesystem allows) and is built: `lake build --wfail GraphIso
# Solution`, then `lake build Challenge`, whose only warnings must be the deliberate `sorry` of
# each advertised theorem. Run the build under `scripts/guard.sh`.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
lean=$(dirname "$here")
# the helper's arguments; never empty, since Bash 3.2 (macOS) rejects an empty "${a[@]}" under -u
args=() build=0 out=
for a in "$@"; do
  case $a in
    --draft) args+=(--draft) ;;
    --build) build=1 ;;
    *) out=$a ;;
  esac
done
[ -n "$out" ] || { echo "usage: $0 [--draft] [--build] OUT" >&2; exit 2; }
args+=("$out")

python3 "$here/palomar-snapshot.py" "${args[@]}"
[ "$build" = 1 ] || exit 0

cd "$out/lean"
cp -cRp "$lean/.lake" .lake 2>/dev/null || cp -Rp --reflink=auto "$lean/.lake" .lake
lake build --wfail GraphIso Solution
log=$(mktemp)
lake build Challenge 2>&1 | tee "$log"
theorems=$(python3 -c \
  'import json; print(len(json.load(open("comparator.json"))["theorem_names"]))')
sorries=$(grep -c '^warning: Challenge.lean:[0-9]*:[0-9]*: declaration uses .sorry.$' "$log" \
  || true)
warnings=$(grep -c '^warning' "$log" || true)
rm -f "$log"
if [ "$sorries" != "$theorems" ] || [ "$warnings" != "$theorems" ]; then
  echo "palomar-snapshot: Challenge has $warnings warning(s), $sorries deliberate sorry;" \
    "expected exactly $theorems" >&2
  exit 1
fi
echo "palomar-snapshot: built; Challenge's only warnings are its $theorems deliberate sorry"
