
## ddSMT

to use ddSMT (from https://github.com/ddsmt/ddSMT/issues):

Assuming `bad_file.smt2` is UNSAT but sidekick returns SAT:
```sh
ddsmt.py -vv bad_file.smt2 foo.smt2 ./src/tools/ddsmt_driver_unsat.py
```

Once it's done, `foo.smt2` should contain a minimal problematic file.


