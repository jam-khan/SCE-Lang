# SCE-Lang — build orchestration.
# `dune build` generates the lexer (ocamllex) and parser (menhir) and
# compiles everything; the targets below are thin wrappers around it.

.PHONY: all build test docs site run web wasm sepcomp clean setup

all: build

# Compile the whole project (parser/lexer generation included).
build:
	dune build

# Build and run the test suite.
test:
	dune test --force

# Generate the OCaml API reference and its compiler overview.
docs:
	dune build @doc
	@echo 'API docs: _build/default/_doc/_html/sce/index.html'

# Start the REPL.
run:
	dune exec bin/main.exe

# Compile a program to WebAssembly and run it under node.
#   make wasm SRC=examples/modules.sce
SRC ?= examples/modules.sce
wasm:
	dune exec bin/main.exe -- --wasm /tmp/sce.wasm $(SRC) --wat /tmp/sce.wat
	node lib/wasm/run.js /tmp/sce.wasm

# Separate compilation demo: compile the peano units, link at the core and at
# the wasm level, and run all three ways.
SEP := /tmp/sce-sepcomp
sepcomp:
	dune build
	rm -rf $(SEP) && mkdir -p $(SEP)
	cp examples/units/peano/*.sce $(SEP)/
	dune exec --no-build bin/main.exe -- -c $(SEP)/nat.sce -o $(SEP)/nat.sceo
	dune exec --no-build bin/main.exe -- -c $(SEP)/arith.sce -o $(SEP)/arith.sceo
	dune exec --no-build bin/main.exe -- -c $(SEP)/demo.sce -o $(SEP)/demo.sceo
	dune exec --no-build bin/main.exe -- --link $(SEP)/nat.sceo $(SEP)/arith.sceo $(SEP)/demo.sceo -o $(SEP)/prog.sceo
	dune exec --no-build bin/main.exe -- --run $(SEP)/prog.sceo
	dune exec --no-build bin/main.exe -- --wasm $(SEP)/prog.wasm $(SEP)/prog.sceo
	node lib/wasm/run.js $(SEP)/prog.wasm
	dune exec --no-build bin/main.exe -- --unit-wasm $(SEP)/nat.wasm $(SEP)/nat.sceo
	dune exec --no-build bin/main.exe -- --unit-wasm $(SEP)/arith.wasm $(SEP)/arith.sceo
	dune exec --no-build bin/main.exe -- --unit-wasm $(SEP)/demo.wasm $(SEP)/demo.sceo
	dune exec --no-build bin/main.exe -- --link-wasm $(SEP)/linked.wasm $(SEP)/nat.sceo $(SEP)/arith.sceo $(SEP)/demo.sceo
	node lib/wasm/run.js $(SEP)/linked.wasm $(SEP)/nat.wasm $(SEP)/arith.wasm $(SEP)/demo.wasm

# Assemble the playground and API docs for local serving or GitHub Pages.
site:
	dune build web @doc
	rm -rf _build/site
	mkdir -p _build/site
	cp _build/default/web/index.html _build/default/web/playground.bc.wasm.js _build/site/
	cp -R _build/default/web/playground.bc.wasm.assets _build/site/
	cp -R _build/default/_doc/_html _build/site/docs
	rm -f _build/site/playground.bc.wasm.assets/*.map

# Serve the same site that GitHub Pages publishes.
web: site
	python3 web/serve.py

# One-time environment setup: install the OCaml dependencies.
# (binaryen comes from your system package manager, e.g. `brew install binaryen`)
setup:
	opam install --yes dune menhir js_of_ocaml js_of_ocaml-ppx wasm_of_ocaml-compiler odoc
	@command -v node >/dev/null || echo 'note: install node for the wasm backend (brew install node)'

clean:
	dune clean
