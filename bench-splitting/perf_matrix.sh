#!/bin/bash
# PMU attribution matrix for the region-boundary tax (see PERF.md), AMD Zen4.
#
#   bash perf_matrix.sh <S> <chunk|off> [loopsecs]
#
# Launches julia ONCE, then attaches `perf stat -p` for several 5-counter event
# groups back-to-back against the steady-state hot loop, so the (large, at 256k)
# compile cost is paid once and amortized across all groups. All configs run
# with SLP disabled so codegen is identical modulo the splitting machinery.
#
# The box exposes only 5 free programmable counters (nmi_watchdog holds the 6th,
# no sudo to disable), so every group is <=5 events -> no multiplexing.
set -u
cd "$(dirname "$0")"
S=$1; CH=$2
CORE=${CORE:-2}
WIN=${WIN:-10}
SECS=${3:-$((4 * WIN + 10))}
if [ "$CH" = off ]; then
  FLAGS="-vectorize-slp=false"
else
  FLAGS="-vectorize-slp=false -julia-split-function-threshold=64 -julia-split-block-threshold=64 -julia-split-max-region-blocks=8192 -julia-split-chunk-size=$CH"
fi
FLAGS="$FLAGS ${EXTRA_FLAGS:-}"

# A: code residency (L1i miss, L2-code hit, L2-code miss=fill from system)
EVA="cycles,instructions,L1-icache-load-misses,ic_cache_fill_l2,ic_cache_fill_sys"
# B: iTLB (generic itlb miss, L1-ITLB miss/L2-ITLB hit, full page walk)
EVB="cycles,instructions,iTLB-load-misses,bp_l1_tlb_miss_l2_tlb_hit,bp_l1_tlb_miss_l2_tlb_miss.all"
# C: BTB / front-end resteers (branch behavior + decoder resteer)
EVC="cycles,instructions,branches,branch-misses,bp_de_redirect"
# D: BTB overrides, resyncs, and front-end starvation slots (context)
EVD="cycles,instructions,bp_l2_btb_correct,resyncs_or_nc_redirects,de_no_dispatch_per_slot.no_ops_from_frontend"

LOG=$(mktemp)
PERFMODE=1 LOOPSECS=$SECS GEN=blocks S=$S B=40 W=8 LABEL=perf-$CH \
  JULIA_LLVM_ARGS="$FLAGS" taskset -c "$CORE" ../usr/bin/julia gen_axes.jl > "$LOG" 2>&1 &
JPID=$!
until grep -q PERFREADY "$LOG" 2>/dev/null; do
  kill -0 $JPID 2>/dev/null || { echo "julia died:"; tail -8 "$LOG"; rm -f "$LOG"; exit 1; }
  sleep 0.5
done
PID=$(grep -oE "PERFREADY pid=[0-9]+" "$LOG" | grep -oE "[0-9]+")
for grp in EVA EVB EVC EVD; do
  echo "### GROUP=$grp S=$S CH=$CH"
  perf stat -e "${!grp}" -p "$PID" -- sleep "$WIN" 2>&1
done
wait $JPID
grep -E "PERFDONE" "$LOG"
rm -f "$LOG"
