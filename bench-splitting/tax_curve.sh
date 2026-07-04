#!/bin/bash
# Post-fix branchy tax-vs-R curve + high-site-count pair, GROUNDED:
# anchor cells (known values from axes_fast.csv, same power profile) run at
# start/middle/end to detect measurement-condition drift. Conclusions from
# within-batch ratios; anchors reported against their reference values.
set -u
cd "$(dirname "$0")"
JULIA=../usr/bin/julia
OUT=${1:-tax_curve.csv}
: > axes.err
echo "gen,S,B,W,label,compile_s,llvm_s,llvm_pct,runtime_us,reps,ns_per_op,chk" > "$OUT"
run() {
  local gen=$1 s=$2 b=$3 w=$4 label=$5; shift 5
  GEN=$gen S=$s B=$b W=$w LABEL=$label JULIA_LLVM_ARGS="$*" \
    $JULIA gen_axes.jl >> "$OUT" 2>>axes.err || echo "$gen,$s,$b,$w,$label,,,,,,,FAIL" >> "$OUT"
  tail -1 "$OUT"
}
FL="-julia-split-function-threshold=64 -julia-split-block-threshold=64 -julia-split-time"
anchors() {
  run straight 65536 0 8 anchor-$1 $FL -julia-split-chunk-size=400
  run calls 16384 0 8 anchor-$1 $FL -julia-split-chunk-size=400
  run blocks 64000 40 8 anchor-$1-off
}
anchors start
echo "== tax curve: blocks 64k, 3 reps"
for rep in 1 2 3; do
  run blocks 64000 40 8 off-r$rep
  for ch in 400 800 1600 3200 6400; do
    run blocks 64000 40 8 c$ch-r$rep $FL -julia-split-chunk-size=$ch
  done
done
anchors mid
echo "== high-site-count pair: blocks 256k"
for rep in 1 2; do
  run blocks 256000 40 8 off256-r$rep
  run blocks 256000 40 8 c400-256-r$rep $FL -julia-split-chunk-size=400
  run blocks 256000 40 8 c1600-256-r$rep $FL -julia-split-chunk-size=1600
done
anchors end
echo done
