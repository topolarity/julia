#!/bin/bash
# Run one boundary-tax perf measurement (see PERF.md for the matrix).
#
#   bash perf_one.sh <S> <chunk|off> <event-list> [loopsecs]
#
# Pins julia to one P-core, waits for the harness's steady-state hot loop,
# attaches perf for the loop window, and prints counters plus the iteration
# rate for normalization. All configs run with SLP disabled so codegen is
# identical modulo the splitting machinery.
set -u
cd "$(dirname "$0")"
S=$1; CH=$2; EVENTS=$3; SECS=${4:-30}
CORE=${CORE:-2}   # pick a P-core (0-11 on a 12700H; E-cores are 12+)
if [ "$CH" = off ]; then
  FLAGS="-vectorize-slp=false"
else
  FLAGS="-vectorize-slp=false -julia-split-function-threshold=64 -julia-split-block-threshold=64 -julia-split-max-region-blocks=8192 -julia-split-block-size=$CH"
fi
LOG=$(mktemp)
PERFMODE=1 LOOPSECS=$SECS GEN=blocks S=$S B=40 W=8 LABEL=perf-$CH \
  JULIA_LLVM_ARGS="$FLAGS" taskset -c $CORE ../usr/bin/julia gen_axes.jl > "$LOG" 2>&1 &
JPID=$!
until grep -q PERFREADY "$LOG" 2>/dev/null; do
  kill -0 $JPID 2>/dev/null || { echo "julia died:"; tail -5 "$LOG"; exit 1; }
  sleep 0.5
done
PID=$(grep -oE "PERFREADY pid=[0-9]+" "$LOG" | grep -oE "[0-9]+")
WINDOW=$((SECS - 4))
perf stat -e "$EVENTS" -p "$PID" -- sleep $WINDOW
wait $JPID
grep -E "PERFDONE|^blocks" "$LOG"
rm -f "$LOG"
