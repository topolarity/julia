#!/bin/bash
# Trimmed threshold-tuning sweep (~10 min): 1 rep, sizes bracketing each
# crossover rather than confirming known tails. Compile crossovers are
# separated by 2-10x so single reps decide them; runtime cells carry the
# +/-40% placement-lottery caveat and are re-run only if borderline.
set -u
cd "$(dirname "$0")"
JULIA=../usr/bin/julia
OUT=${1:-axes_fast.csv}
: > axes.err
echo "gen,S,B,W,label,compile_s,llvm_s,llvm_pct,runtime_us,reps,ns_per_op,chk" > "$OUT"
run() {
  local gen=$1 s=$2 b=$3 w=$4 label=$5; shift 5
  GEN=$gen S=$s B=$b W=$w LABEL=$label JULIA_LLVM_ARGS="$*" \
    $JULIA gen_axes.jl >> "$OUT" 2>>axes.err || echo "$gen,$s,$b,$w,$label,,,,,,,FAIL" >> "$OUT"
  tail -1 "$OUT"
}
ON="-julia-split-function-threshold=64 -julia-split-block-threshold=64 -julia-split-block-size=400 -julia-split-time"

echo "== A: block axis"
for s in 2000 8000 32000; do
  run straight $s 0 8 off
  run straight $s 0 8 on $ON
done
for c in 500 2000 8000; do
  run calls $c 0 8 off
  run calls $c 0 8 on $ON
done
echo "== A2: arrays axis (derived outputs)"
for s in 8000 32000; do
  run arrays $s 0 8 off
  run arrays $s 0 8 on $ON
done
echo "== B: function axis (blocks ~40)"
for s in 16000 64000; do
  run blocks $s 40 8 off
  run blocks $s 40 8 on $ON
done
for c in 4000 16000; do
  run calls $c 40 8 off
  run calls $c 40 8 on $ON
done
echo "== C: chunk axis"
for ch in 200 400 1600 3200; do
  F="-julia-split-function-threshold=64 -julia-split-block-threshold=64 -julia-split-block-size=$ch"
  run straight 65536 0 8 chunk$ch $F
  run calls 16384 0 8 chunk$ch $F
  run arrays 65536 0 8 chunk$ch $F
done
echo "== D: width spot-check (on only)"
run calls 16384 0 128 won $ON
echo done
