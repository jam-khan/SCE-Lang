# SCE-Lang — build orchestration.
# `dune build` generates the lexer (ocamllex) and parser (menhir) and
# compiles everything; the targets below are thin wrappers around it.

.PHONY: all build test run web wasm sepcomp clean setup

all: build

# Compile the whole project (parser/lexer generation included).
build:
	dune build

# Build and run the test suite.
test:
	dune test --force

# Start the REPL.
run:
	dune exec bin/main.exe

# Compile a program to WebAssembly and run it under node.
#   make wasm SRC=examples/modules.sce
SRC ?= examples/basics.sce
wasm:
	dune exec bin/main.exe -- --wasm /tmp/sce.wasm $(SRC) --wat /tmp/sce.wat
	node wasm/run.js /tmp/sce.wasm

# Separate compilation demo: compile the example units, link at core and at
# the wasm level, and run all three ways.
sepcomp:
	dune build
	rm -rf /tmp/sce-sepcomp && mkdir -p /tmp/sce-sepcomp
	cp examples/units/*.sce /tmp/sce-sepcomp/
	dune exec --no-build bin/main.exe -- -c /tmp/sce-sepcomp/counter.sce -o /tmp/sce-sepcomp/counter.sceo
	dune exec --no-build bin/main.exe -- -c /tmp/sce-sepcomp/fmt.sce -o /tmp/sce-sepcomp/fmt.sceo
	dune exec --no-build bin/main.exe -- -c /tmp/sce-sepcomp/app.sce -o /tmp/sce-sepcomp/app.sceo
	dune exec --no-build bin/main.exe -- --link /tmp/sce-sepcomp/counter.sceo /tmp/sce-sepcomp/fmt.sceo /tmp/sce-sepcomp/app.sceo -o /tmp/sce-sepcomp/prog.sceo
	dune exec --no-build bin/main.exe -- --run /tmp/sce-sepcomp/prog.sceo
	dune exec --no-build bin/main.exe -- --unit-wasm /tmp/sce-sepcomp/counter.wasm /tmp/sce-sepcomp/counter.sceo
	dune exec --no-build bin/main.exe -- --unit-wasm /tmp/sce-sepcomp/fmt.wasm /tmp/sce-sepcomp/fmt.sceo
	dune exec --no-build bin/main.exe -- --unit-wasm /tmp/sce-sepcomp/app.wasm /tmp/sce-sepcomp/app.sceo
	dune exec --no-build bin/main.exe -- --link-wasm /tmp/sce-sepcomp/linked.wasm /tmp/sce-sepcomp/counter.sceo /tmp/sce-sepcomp/fmt.sceo /tmp/sce-sepcomp/app.sceo
	node wasm/run.js /tmp/sce-sepcomp/linked.wasm /tmp/sce-sepcomp/counter.wasm /tmp/sce-sepcomp/fmt.wasm /tmp/sce-sepcomp/app.wasm

# Build the wasm playground and serve it at http://127.0.0.1:8000.
web:
	dune build web
	python3 web/serve.py

# One-time environment setup: install the OCaml dependencies.
# (binaryen comes from your system package manager, e.g. `brew install binaryen`)
setup:
	opam install --yes dune menhir js_of_ocaml js_of_ocaml-ppx wasm_of_ocaml-compiler
	@command -v node >/dev/null || echo 'note: install node for the wasm backend tests (brew install node)'

clean:
	dune clean
