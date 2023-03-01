#!/bin/sh
exec dune exec --profile=release --display=quiet -- src/leancheck/leancheck.exe $@
