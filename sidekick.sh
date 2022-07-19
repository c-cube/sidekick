#!/bin/sh
OPTS=--profile=release
exec dune exec $OPTS ./src/main/main.exe -- $@
