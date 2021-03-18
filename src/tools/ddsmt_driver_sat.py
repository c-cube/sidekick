#!/usr/bin/python

import subprocess, sys

filename: str = sys.argv[1]

z3_out = subprocess.run([b'z3', filename], capture_output=True).stdout
if b'sat' not in z3_out or b'unsat' in z3_out or b'error' in z3_out:
    sys.exit(0)

b_out = subprocess.run([b'./mc2', filename], capture_output=True).stdout
if b_out.startswith(b'Unsat') and b'Error' not in b_out:
    print('ohno', file=sys.stderr)
    sys.exit(1)

