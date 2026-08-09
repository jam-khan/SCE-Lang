# SCE-Lang — build orchestration.
# `dune build` generates the lexer (ocamllex) and parser (menhir) and
# compiles everything; the targets below are thin wrappers around it.

.PHONY: all build test run web wasm clean setup

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
