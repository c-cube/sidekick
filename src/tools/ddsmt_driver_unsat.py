#!/usr/bin/python

# minimize unsat problem

import subprocess, sys

filename: str = sys.argv[1]

z3_out = subprocess.run([b'z3', filename], capture_output=True).stdout
if b'unsat' not in z3_out or b'error' in z3_out:
    print("z3 failed")
    sys.exit(1)

b_out = subprocess.run([b'./sidekick', filename], capture_output=True).stdout
if b'Sat' not in b_out or b'Error' in b_out:
    print('ohno', file=sys.stderr)
    print(b_out, sys.stderr)
    sys.exit(2)

sys.exit(0)

