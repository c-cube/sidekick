# copyright (c) 2014, guillaume bury
# copyright (c) 2017, simon cruanes

.PHONY: clean build build-dev

J?=3
TIMEOUT?=30
OPTS= -j $(J)

dev: build-dev

# TODO: repair tests
#dev: build-dev test

build-install:
	@dune build $(OPTS) @install --profile=release

build: build-install

build-dev:
	@dune build $(OPTS)

clean:
	@dune clean

test:
	@dune runtest

TESTOPTS ?= -j $(J)
TESTTOOL=logitest
DATE=$(shell date +%FT%H:%M)

logitest-quick:
	@mkdir -p snapshots
	$(TESTTOOL) run -c tests/conf.toml tests/ $(TESTOPTS) \
	  --meta `git rev-parse HEAD` --summary snapshots/quick-$(DATE).txt \
	  --csv snapshots/quick-$(DATE).csv

install: build-install
	@dune install

uninstall:
	@dune uninstall

doc:
	@dune build $(OPTS) @doc

reinstall: | uninstall install

reindent: ocp-indent
	@find src '(' -name '*.ml' -or -name '*.mli' ')' -print0 | xargs -0 echo "reindenting: "
	@find src '(' -name '*.ml' -or -name '*.mli' ')' -print0 | xargs -0 ocp-indent -i

WATCH=@install
watch:
	@dune build $(WATCH) -w
	#@dune build @all -w # TODO: once tests pass

.PHONY: clean doc all bench install uninstall remove reinstall bin test
