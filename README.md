# SCE-Lang

SCE-Lang is an OCaml implementation of a source language based on λSCE, with
structures, functors, sandboxing, and linking as language expressions. It
includes an interpreter, separate compilation, a WebAssembly-GC backend, and
a browser playground. The accompanying Lean development formalizes λSCE,
the core calculus λE, and elaboration between them.

## Quick start

Use an initialized **OCaml/opam** switch and **Dune 3.20 or newer**.
`make setup` installs the OCaml dependencies. Install **Binaryen** (`wasm-opt`)
separately: the default build includes the WebAssembly playground. The
[playground CI](.github/workflows/playground.yml) uses OCaml 5.3 and Binaryen 123.
You also need **Node.js with WasmGC support** to run compiled programs and
the full test suite, and **Python 3** to serve the playground locally.

```sh
eval "$(opam env)"
make setup
make build
dune exec bin/main.exe -- examples/modules.sce
```

The example returns `{ started = 11, doubled = 20, next = 11, secret = 42 }`
alongside its type. To start the REPL, run `make run`; submit each program
with a blank line.

| Command | Purpose |
| --- | --- |
| `make test` | Run the interpreter, separate compilation, and Wasm differential suites. |
| `make wasm SRC=examples/modules.sce` | Compile a source file to WasmGC and run it under Node.js. |
| `make sepcomp` | Run separately compiled Peano units through core and Wasm linking. |
| `make web` | Build and serve the playground and both references at <http://127.0.0.1:8000>. |
| `make docs` | Generate the OCaml API reference. |
| `make docs-lean` | Generate the Lean reference. |
| `make site` | Assemble the playground and both references in `_build/site/` for hosting. |

Open `_build/default/_doc/_html/sce/index.html` after `make docs`.
The playground's **Docs** and **Mechanization** links open the references in
new tabs. `make docs-lean`, `make site`, and `make web` also require `elan`
and a C compiler; the first Lean documentation build downloads its pinned
dependencies. GitHub Pages publishes the same site on pushes to `main`.

Wasm execution checks are skipped when Node.js is unavailable; Binaryen
validation is skipped when `wasm-opt` is unavailable.

## Examples

Start with [modules.sce](examples/modules.sce) for structures, functors,
sandboxing, and linking. Then try [the Peano units](examples/units/peano/README.md)
for separate compilation and [effects](examples/effects/README.md) for host
capabilities. The [example guide](examples/README.md) continues through runtime
loading, upgrades, and a lambda-calculus interpreter, with commands and
expected results.

`Unit` is an alias for `Top`, the type of `()`, in source annotations and
interface files. Generated interfaces use `Top`.

## Implementation

The shared [pipeline](lib/pipeline.mli) parses source text, desugars it to
λSCE, resolves names, elaborates to λE, and checks the core term before
evaluation or Wasm compilation. Separately compiled units store their core
terms and interfaces; the linker builds and checks a composition term.

| Path | Role |
| --- | --- |
| [bin/](bin/) | Command-line interface and REPL. |
| [lib/source/](lib/source/) | Surface syntax, lexer, parser, and desugaring. |
| [lib/sce/](lib/sce/) | λSCE syntax, name resolution, elaboration, and reference evaluator. |
| [lib/core/](lib/core/) | λE syntax, type checker, evaluator, and printing. |
| [lib/units/](lib/units/) | Interfaces, compiled artifacts, linking, and host capabilities. |
| [lib/wasm/](lib/wasm/README.md) | WasmGC compiler, binary and text emission, and Node.js runtime. |
| [web/](web/) | Browser playground. |
| [examples/](examples/README.md), [test/](test/) | Example programs and regression suites. |
| [mechanization/](mechanization/) | Lean definitions and proofs. |

The generated API reference documents the OCaml module interfaces; the
[backend guide](lib/wasm/README.md) explains Wasm representation and linking.

## Lean mechanization

With `elan` installed, build the proofs using the repository's pinned Lean
toolchain:

```sh
(cd mechanization && lake build)
```

The [Lean development](mechanization/LeanSce.lean) covers type safety,
elaboration, separate compilation, and linking properties of the calculi.
It does not verify the OCaml implementation or the WebAssembly backend.
The [theorem map](mechanization/THEOREMS.md) links paper results to their proofs.
