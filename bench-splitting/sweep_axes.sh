#!/bin/bash
# Single-axis threshold-tuning sweep for the JuliaFunctionSplitting pass.
# Every point is a fresh process; sizes are chosen so no point exceeds ~30s.
#
#   bash sweep_axes.sh [axes.csv]
#
# Stages (see gen_axes.jl for the generators):
#   A  block axis     — single-block size sweep, float and call flavors,
#                       off vs forced-on            -> block-threshold default
#   B  function axis  — size sweep at pinned ~40-stmt blocks, float and call
#                       flavors, off vs forced-on   -> function-threshold default
#   C  chunk axis     — chunk sweep at fixed large size -> chunk-size default
#   D  width axis     — live-root width sweep at fixed size (off vs on):
#                       checks defaults hold for root-heavy code
#   E  group axis     — group sweep with regions >> group -> group-size default
set -u
cd "$(dirname "$0")"
JULIA=../usr/bin/julia
OUT=${1:-axes.csv}
: > axes.err
echo "gen,S,B,W,label,compile_s,llvm_s,llvm_pct,runtime_us,reps,ns_per_op,chk" > "$OUT"

# REPS=3 sweep_axes.sh ... runs each point in 3 fresh processes (cross-process
# runtime variance is +/-15-20% from code layout; single runs only resolve
# larger effects).
run() { # gen S B W label flags...
  local gen=$1 s=$2 b=$3 w=$4 label=$5; shift 5
  for rep in $(seq 1 ${REPS:-1}); do
    GEN=$gen S=$s B=$b W=$w LABEL=$label-r$rep JULIA_LLVM_ARGS="$*" \
      $JULIA gen_axes.jl >> "$OUT" 2>>axes.err \
      || echo "$gen,$s,$b,$w,$label-r$rep,,,,,,,FAIL" >> "$OUT"
    tail -1 "$OUT"
  done
}

# forced-on: gate always fires; granularity at the working values
ON="-julia-split-function-threshold=64 -julia-split-block-threshold=64 -julia-split-chunk-size=400"

echo "== A: block axis (single block) =="
for s in 1000 2000 4000 8000 16000 32000 64000 128000; do
  run straight $s 0 8 off
  run straight $s 0 8 on $ON
done
for c in 250 500 1000 2000 4000 8000 16000 32000; do
  run calls $c 0 8 off
  run calls $c 0 8 on $ON
done

echo "== A2: arrays axis (derived-pointer outputs; single block) =="
for s in 8000 16000 32000 65536; do
  run arrays $s 0 8 off
  run arrays $s 0 8 on $ON
done

echo "== B: function axis (blocks pinned at ~40) =="
for s in 4000 16000 64000 128000 256000; do
  run blocks $s 40 8 off
  run blocks $s 40 8 on $ON
done
for c in 1000 4000 16000 32000; do
  run calls $c 40 8 off
  run calls $c 40 8 on $ON
done

echo "== C: chunk axis (fixed large size) =="
for ch in 100 200 400 800 1600 3200; do
  F="-julia-split-function-threshold=64 -julia-split-block-threshold=64 -julia-split-chunk-size=$ch"
  run straight 65536 0 8 chunk$ch $F
  run calls 16384 0 8 chunk$ch $F
  run arrays 65536 0 8 chunk$ch $F
done

echo "== D: width axis (calls fixed at 16384) =="
for w in 2 8 32 128; do
  run calls 16384 0 $w woff
  run calls 16384 0 $w won $ON
done

echo "== E: group axis (straight 131072 -> ~330 regions) =="
for g in 8 24 64; do
  run straight 131072 0 8 grp$g $ON -julia-split-group-size=$g
done
echo "axes sweep complete -> $OUT"
