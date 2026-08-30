# SCE-Lang
This is the repository for source language implementation based on λSCE.

## Running

```console
$ make build                                  # dune build
$ make test                                   # every suite, wasm differentials included
$ dune exec bin/main.exe examples/modules.sce  # interpret a whole file
```

Separate compilation (`-c`, `--link`, `--run`) and the host capabilities
(`sys`, `str`, `loader`) are walked through example by example in
[examples/README.md](examples/README.md).

## WebAssembly backend

The same programs compile to WasmGC and run under node; the backend lives in
[lib/wasm/](lib/wasm/README.md).

```console
$ dune exec bin/main.exe -- --wasm out.wasm examples/modules.sce
$ node lib/wasm/run.js out.wasm
{ started = 11, doubled = 20, next = 11, secret = 42 }
```

`--wasm OUT prog.sceo` compiles a linked artifact, `--unit-wasm` one unit as
its own module (what the runtime loader picks up in place of a `.sceo`), and
`--link-wasm` links unit modules at the wasm level. `make wasm SRC=…` and
`make sepcomp` run the two routes end to end; the test suite requires the
interpreter and the compiled program to print the same trace and value for
every example.
