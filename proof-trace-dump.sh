#!/usr/bin/env sh
exec dune exec --profile=release src/proof-trace-dump/proof_trace_dump.exe -- $@
