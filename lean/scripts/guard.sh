#!/bin/bash
# guard.sh — run one heavy Lean command at a time, under a memory cap and a time limit.
#
#   scripts/guard.sh [-m MEM_MB] [-t TIME_S] [-l LABEL] -- command args...
#
# * A global lock (an atomic `mkdir`) serializes guarded runs across shells, agents and the gate,
#   so two heavy builds or checks never run at once. A lock whose owner has died is broken.
# * Every second the total resident memory of the command's process tree is sampled; the tree is
#   killed when it exceeds MEM_MB (default 16000) or runs longer than TIME_S (default 3600).
# * One line per run is appended to the log (time, label, exit status, peak memory, elapsed
#   seconds, command), so measurements keep raw records.
#
# Environment: LEAN_GUARD_LOCK (lock directory), LEAN_GUARD_LOG (log file).
# Exit status: the command's, or 137 when the guard killed it.

set -u
MEM_MB=16000
TIME_S=3600
LABEL=""
LOCK=${LEAN_GUARD_LOCK:-$HOME/.cache/graphiso-lean-guard/lock}
LOG=${LEAN_GUARD_LOG:-$HOME/.cache/graphiso-lean-guard/runs.log}

usage() {
  echo "usage: $0 [-m MEM_MB] [-t TIME_S] [-l LABEL] -- command args..." >&2
  exit 2
}

while getopts "m:t:l:" opt; do
  case $opt in
    m) MEM_MB=$OPTARG ;;
    t) TIME_S=$OPTARG ;;
    l) LABEL=$OPTARG ;;
    *) usage ;;
  esac
done
shift $((OPTIND - 1))
[ "${1:-}" = "--" ] && shift
[ $# -ge 1 ] || usage
[ -n "$LABEL" ] || LABEL=$(basename "$1")

mkdir -p "$(dirname "$LOCK")" "$(dirname "$LOG")"

# Acquire the global lock.
waited=0
while ! mkdir "$LOCK" 2>/dev/null; do
  owner=$(cat "$LOCK/pid" 2>/dev/null || true)
  if [ -n "$owner" ] && ! kill -0 "$owner" 2>/dev/null; then
    rm -rf "$LOCK"
    continue
  fi
  if [ $waited -eq 0 ]; then echo "guard: waiting for the lock held by pid ${owner:-?}" >&2; fi
  waited=1
  sleep 2
done
echo $$ > "$LOCK/pid"
trap 'rm -rf "$LOCK"' EXIT

# All descendants of a pid, the pid included.
tree() {
  local p=$1
  echo "$p"
  for c in $(pgrep -P "$p" 2>/dev/null); do tree "$c"; done
}

start=$(date +%s)
"$@" &
child=$!
peak=0
killed=""
while kill -0 "$child" 2>/dev/null; do
  pids=$(tree "$child" | paste -sd, -)
  rss=$(ps -o rss= -p "$pids" 2>/dev/null | awk '{s += $1} END {print int(s / 1024)}')
  rss=${rss:-0}
  [ "$rss" -gt "$peak" ] && peak=$rss
  elapsed=$(( $(date +%s) - start ))
  if [ "$rss" -gt "$MEM_MB" ]; then
    killed="memory ${rss} MB > cap ${MEM_MB} MB"
  elif [ "$elapsed" -gt "$TIME_S" ]; then
    killed="time ${elapsed} s > limit ${TIME_S} s"
  fi
  if [ -n "$killed" ]; then
    victims=$(tree "$child")
    for p in $victims; do kill -9 "$p" 2>/dev/null; done
    break
  fi
  sleep 1
done
wait "$child" 2>/dev/null
rc=$?
elapsed=$(( $(date +%s) - start ))
if [ -n "$killed" ]; then
  rc=137
  echo "guard: killed ($killed)" >&2
fi
printf '%s\t%s\trc=%s\tpeak=%sMB\telapsed=%ss\tcap=%sMB/%ss\t%s\n' \
  "$(date '+%Y-%m-%d %H:%M:%S')" "$LABEL" "$rc" "$peak" "$elapsed" "$MEM_MB" "$TIME_S" "$*" \
  >> "$LOG"
echo "guard: $LABEL rc=$rc peak=${peak}MB elapsed=${elapsed}s" >&2
exit $rc
