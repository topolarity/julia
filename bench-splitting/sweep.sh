#!/bin/bash
# Validation suite for the JuliaFunctionSplitting defaults: realistic composite
# workloads (MTK brusselator RHS specialized on several element types, both
# ReverseDiff variants) compiled with the pass off vs on. Threshold/granularity
# *tuning* lives in sweep_axes.sh; this suite checks that the chosen defaults
# help the workloads they should and cost nothing where they shouldn't fire.
#
#   julia setup_envs.jl        # once
#   bash sweep.sh [out.csv] [flags...]   # flags default to the chosen defaults
set -u
cd "$(dirname "$0")"
JULIA=../usr/bin/julia
OUT=${1:-validate.csv}
shift || true
CFG=${*:-"-julia-split-function-threshold=8000 -julia-split-block-threshold=1500 -julia-split-block-size=400"}
FIXED=envs/fixed
STOCK=envs/stock
: > sweep.err
echo "shape,N,label,compile_s,llvm_s,llvm_pct,runtime_us,reps,ok" > "$OUT"

run() { # shape shapeid proj N label flags...
  local shape=$1 shapeid=$2 proj=$3 n=$4 label=$5; shift 5
  SHAPE=$shape SHAPEID=$shapeid RD_N=$n LABEL=$label JULIA_LLVM_ARGS="$*" \
    $JULIA --project=$proj bench_one.jl >> "$OUT" 2>>sweep.err \
    || echo "$shapeid,$n,$label,,,,,,FAIL" >> "$OUT"
  tail -1 "$OUT"
}

echo "== composite off vs on (cheap sizes only) =="
for n in 6 10; do
  for cfg in off on; do
    if [ $cfg = off ]; then F=""; else F="$CFG"; fi
    run float   float         $FIXED $n $cfg $F
    run dual    dual          $FIXED $n $cfg $F
    run tracked tracked       $FIXED $n $cfg $F
    run tracked tracked_stock $STOCK $n $cfg $F
  done
done
# the stock shape is too slow unsplit beyond N=10; measure split-only there
for n in 14 20; do
  for cfg in off on; do
    if [ $cfg = off ]; then F=""; else F="$CFG"; fi
    run float   float   $FIXED $n $cfg $F
    run dual    dual    $FIXED $n $cfg $F
    run tracked tracked $FIXED $n $cfg $F
  done
  run tracked tracked_stock $STOCK $n on $CFG
done

echo "== MTK model build guard (default env, wall seconds) =="
for cfg in off on; do
  if [ $cfg = off ]; then F=""; else F="$CFG"; fi
  s=$(date +%s.%N)
  JULIA_LLVM_ARGS="$F" $JULIA mtk_guard.jl > /dev/null 2>>sweep.err \
    && ok=true || ok=false
  e=$(date +%s.%N)
  echo "mtk_guard,4,$cfg,$(echo "$e - $s" | bc),,,,,$ok" | tee -a "$OUT"
done
echo "validation complete -> $OUT"
