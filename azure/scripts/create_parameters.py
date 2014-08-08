#!/usr/bin/python

import sys

first = int(sys.argv[1])
last = int(sys.argv[2])
step = int(sys.argv[3])

if len(sys.argv) == 5:
    procs = int(sys.argv[4])
else:
    procs = 0

assert(step > 0 and last >= first and first >= 0)

pad = 2
if procs > 1:
    last2 = last - procs * pad
else:
    last2 = last

def print_cases(first, last, step):
    for i in range(first, last + 1, step):
        next = i + step - 1
        if next > last:
            next = last
        print "{},{}".format(i, next)

print_cases(first, last2, step)
print_cases(last2 + 1, last, pad)
