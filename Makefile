# copyright (c) 2014, guillaume bury
# copyright (c) 2017, simon cruanes

.PHONY: clean build build-dev

J?=3
TIMEOUT?=30
OPTS= -j $(J) --profile=release

dev: build-dev

# TODO: repair tests
#dev: build-dev test

build-install:
	@dune build $(OPTS) @install

build: build-install

build-dev:
	@dune build $(OPTS)

clean:
	@dune clean
	@rm sidekick || true

test:
	@dune runtest $(OPTS) --force --no-buffer

TESTOPTS ?= -j $(J) -c tests/benchpress.sexp --progress
TESTTOOL=benchpress
DATE=$(shell date +%FT%H:%M)

snapshots:
	@mkdir -p snapshots
sidekick:
	@ln -f -s _build/default/src/main/main.exe ./sidekick

$(TESTTOOL)-quick: sidekick snapshots
	$(TESTTOOL) run $(TESTOPTS) \
	  --csv snapshots/quick-$(DATE).csv --task sidekick-smt-quick
$(TESTTOOL)-quick-proofs: sidekick snapshots
	$(TESTTOOL) run $(TESTOPTS) \
	  --csv snapshots/quick-$(DATE).csv --task sidekick-smt-quick-proofs --proof-dir out-proofs-$(DATE)/
$(TESTTOOL)-local: sidekick snapshots
	$(TESTTOOL) run $(TESTOPTS) \
	  --csv snapshots/quick-$(DATE).csv --task sidekick-smt-local
$(TESTTOOL)-smt-QF_UF: sidekick snapshots
	$(TESTTOOL) run $(TESTOPTS) \
	  --csv snapshots/smt-QF_UF-$(DATE).csv --task sidekick-smt-nodir tests/QF_UF
$(TESTTOOL)-smt-QF_DT: sidekick snapshots
	$(TESTTOOL) run $(TESTOPTS) \
	  --csv snapshots/smt-QF_DT-$(DATE).csv --task sidekick-smt-nodir tests/QF_DT
$(TESTTOOL)-smt-QF_LRA: sidekick snapshots
	$(TESTTOOL) run $(TESTOPTS) \
	  --csv snapshots/smt-QF_LRA-$(DATE).csv --task sidekick-smt-nodir tests/QF_LRA
$(TESTTOOL)-smt-QF_UFLRA: sidekick snapshots
	$(TESTTOOL) run $(TESTOPTS) \
	  --csv snapshots/smt-QF_UFLRA-$(DATE).csv --task sidekick-smt-nodir tests/QF_UFLRA
$(TESTTOOL)-smt-QF_LIA: sidekick snapshots
	$(TESTTOOL) run $(TESTOPTS) \
	  --csv snapshots/smt-QF_LRA-$(DATE).csv --task sidekick-smt-nodir tests/QF_LIA
$(TESTTOOL)-smt-QF_UFLIA: sidekick snapshots
	$(TESTTOOL) run $(TESTOPTS) \
	  --csv snapshots/smt-QF_LRA-$(DATE).csv --task sidekick-smt-nodir tests/QF_UFLIA

install: build-install
	@dune install

uninstall:
	@dune uninstall

doc:
	@dune build $(OPTS) @doc

reinstall: | uninstall install

reindent:
	@find src '(' -name '*.ml' -or -name '*.mli' ')' -print0 \
	  | xargs -0 sed -i 's/[[:space:]]+$$//g'
	@find src '(' -name '*.ml' -or -name '*.mli' ')' -print0 | xargs -0 echo "reindenting: "
	@find src '(' -name '*.ml' -or -name '*.mli' ')' -print0 | xargs -0 ocp-indent -i

WATCH?=@all
watch:
	dune build $(WATCH) -w $(OPTS)
	#@dune build @all -w # TODO: once tests pass

.PHONY: clean doc all bench install uninstall remove reinstall bin test
