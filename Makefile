# copyright (c) 2014, guillaume bury
# copyright (c) 2017, simon cruanes

.PHONY: clean build build-dev

NAME=msat
J?=3
TIMEOUT?=30
TARGETS=src/main/main.exe
OPTS= -j $(J)

build:
	jbuilder build $(TARGETS) $(OPTS)

build-install:
	jbuilder build @install

build-dev:
	jbuilder build $(TARGETS) $(OPTS) --dev

enable_log:
	cd src/core; ln -sf log_real.ml log.ml

disable_log:
	cd src/core; ln -sf log_dummy.ml log.ml

clean:
	jbuilder clean

install: build-install
	jbuilder install

uninstall:
	jbuilder uninstall

doc:
	jbuilder build $(OPTS) @doc


reinstall: | uninstall install

ocp-indent:
	@which ocp-indent > /dev/null || { \
	  	echo 'ocp-indent not found; please run `opam install ocp-indent`'; \
		exit 1 ; \
	  }

reindent: ocp-indent
	@find src '(' -name '*.ml' -or -name '*.mli' ')' -print0 | xargs -0 echo "reindenting: "
	@find src '(' -name '*.ml' -or -name '*.mli' ')' -print0 | xargs -0 ocp-indent -i

WATCH=build
watch:
	while find src/ -print0 | xargs -0 inotifywait -e delete_self -e modify ; do \
		echo "============ at `date` ==========" ; \
		make $(WATCH); \
	done

.PHONY: clean doc all bench install uninstall remove reinstall enable_log disable_log bin test
