#!/bin/bash
# build-seq.sh — the project build, with the check modules built one at a time.
#
#   scripts/build-seq.sh [lake build options...]      e.g. scripts/build-seq.sh --wfail
#
# `lake build` builds independent modules in parallel, and a few check modules need 20–40 GB
# each in the kernel (Align, Case2b, Case3, CertProg, Giant; docs/status.md, stage 19b): built
# together they exceed the machine's memory. This script builds the library `GraphIso` with
# Lake's parallelism, then every `GraphIsoChecks` module on its own, dependencies first (from
# the modules' `import` lines), then the default targets. Already built modules cost about a
# second each. The options are passed to every `lake build`. Run it under scripts/guard.sh.

set -eu
cd "$(dirname "$0")/.."

lake build "$@" GraphIso

# the `GraphIsoChecks` imports of a file: `[public] [meta] import [all] M` (Lean's module system,
# PLAN-19.md §4)
imports_re='s/^(public )?(meta )?import (all )?(GraphIsoChecks[A-Za-z0-9_.]*).*/\4/p'

seen=" "
order=""
# Depth-first over the `GraphIsoChecks` imports: dependencies before dependents.
visit() {
  local m=$1
  case "$seen" in *" $m "*) return ;; esac
  seen="$seen$m "
  local f="${m//.//}.lean"
  local d
  for d in $(sed -nE "$imports_re" "$f" | sort -u); do
    visit "$d"
  done
  order="$order $m"
}
for f in $(find GraphIsoChecks -name '*.lean' | sort); do
  m=${f%.lean}
  visit "${m//\//.}"
done
visit GraphIsoChecks

for m in $order; do
  echo "build-seq: $m" >&2
  lake build "$@" "$m"
done

lake build "$@"
