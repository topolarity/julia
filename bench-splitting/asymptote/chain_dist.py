#!/usr/bin/env python3
# For each function: walk instructions in textual order. For every
# 'fmul contract' whose LHS operand is the result of an earlier 'fadd contract',
# report the number of fadds that intervened between that producer fadd and
# this fmul. Interleaved 8-chain code -> distance ~7. Grouped -> 0.
import re, sys
from collections import Counter

path = sys.argv[1]
fn = None
fadd_index = {}   # ssa name -> ordinal of the fadd that defined it
fadd_count = 0
hist = {}         # fn -> Counter of distances

def_re = re.compile(r'^\s*(%[\w.\"]+) = (fadd|fmul) contract double (%[\w.\"]+|[-\d.e+]+), (%[\w.\"]+|[-\d.e+]+)')
fn_re = re.compile(r'^define .*@("?[^("]+"?)\(')

for line in open(path):
    m = fn_re.match(line)
    if m:
        fn = m.group(1)
        fadd_index = {}
        fadd_count = 0
        hist[fn] = Counter()
        continue
    if fn is None:
        continue
    m = def_re.match(line)
    if not m:
        continue
    name, op, a, b = m.groups()
    if op == 'fadd':
        fadd_index[name] = fadd_count
        fadd_count += 1
    else:  # fmul
        for operand in (a, b):
            if operand in fadd_index:
                hist[fn][fadd_count - 1 - fadd_index[operand]] += 1

for fn, c in hist.items():
    if not c:
        continue
    total = sum(c.values())
    top = ', '.join(f'd={d}:{n}' for d, n in sorted(c.items())[:12])
    print(f'{fn}: {total} fmul-from-fadd links; {top}')
