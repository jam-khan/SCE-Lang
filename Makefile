# SCE-Lang — build orchestration.
# `dune build` generates the lexer (ocamllex) and parser (menhir) and
# compiles everything; the targets below are thin wrappers around it.

.PHONY: all build test run clean setup

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

# One-time environment setup: install the OCaml dependencies.
setup:
	opam install --yes dune menhir

clean:
	dune clean
