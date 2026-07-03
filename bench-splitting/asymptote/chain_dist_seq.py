#!/usr/bin/env python3
# Segment a -print-after dump stream and report, for each snapshot and each
# function in it, the grouped (d=0) vs interleaved (d=7) fmul-from-fadd link
# counts. Grouped = a muladd consuming the immediately-preceding fadd result.
import re, sys
from collections import Counter

hdr_re = re.compile(r'^; \*\*\* IR Dump After (\S+) on (\S+)')
fn_re = re.compile(r'^define .*@("?[^("]+"?)\(')
def_re = re.compile(r'^\s*(%[\w.\"]+) = (fadd|fmul) (?:contract )?double (%[\w.\"]+|[-\d.e+]+)(?:, (%[\w.\"]+|[-\d.e+]+))?')

snap = None
fn = None
fadd_index = {}
fadd_count = 0
hist = Counter()

def flush_fn():
    global fn, hist
    if fn and sum(hist.values()):
        total = sum(hist.values())
        d0 = hist.get(0, 0)
        d7 = hist.get(7, 0)
        other = total - d0 - d7
        print(f'{snap:55s} {fn:35s} links={total:6d} d0={d0:6d} d7={d7:6d} other={other}')
    hist = Counter()

for line in open(sys.argv[1]):
    m = hdr_re.match(line)
    if m:
        flush_fn()
        snap = f'{m.group(1)}|{m.group(2)}'
        fn = None
        continue
    m = fn_re.match(line)
    if m:
        flush_fn()
        fn = m.group(1)
        fadd_index = {}
        fadd_count = 0
        continue
    if fn is None:
        continue
    m = def_re.match(line)
    if not m:
        continue
    name, op, a, b = m.group(1), m.group(2), m.group(3), m.group(4)
    if op == 'fadd':
        fadd_index[name] = fadd_count
        fadd_count += 1
    else:
        for operand in (a, b):
            if operand and operand in fadd_index:
                hist[fadd_count - 1 - fadd_index[operand]] += 1
flush_fn()
