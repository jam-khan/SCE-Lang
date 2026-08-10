# SCE-Lang

An ML-flavoured surface language for **λSCE**, a merge calculus with first-class
modules, and its elaboration to the core calculus **λE**.

```
source text ──parse──▶ named AST ──de Bruijn──▶ indexed AST ──desugar──▶ λSCE ──elab──▶ λE ──eval──▶ value
```

```console
$ make build
$ dune exec bin/main.exe examples/modules.sce
- : {started : Int} & {doubled : Int} & {next : Int} & {secret : Int} = { started = 11; doubled = 20; next = 11; secret = 42 }

$ make run     # REPL: type a program, blank line runs it
$ make test
$ make web     # playground at http://127.0.0.1:8000
```

## Why there is a resolution pass

λSCE and λE have **no variables**. `?` (`Query`) denotes the entire typing
context — a left-nested intersection — and `?.n` projects its `n`-th component,
counting from the right. Every binder works by extending that intersection:
`Lam` appends the parameter type, `Letb` the bound type, `Mrg` the type of its
left operand, `Flam` the function type and then the argument type.

So the surface language's central job is to turn a name into a position:

| surface | λSCE |
|---|---|
| a plain binding | `Proj (Query, i)` |
| a field of a structure or an `open` | `Rproj (Proj (Query, i), l)` |

That is what [lib/source/debruijn.ml](lib/source/debruijn.ml) does, on its own,
before any types are involved. The context discipline both it and the desugarer
index into lives in one place, [lib/source/frames.ml](lib/source/frames.ml), so
the two cannot drift apart.

## Language tour

```ocaml
(* types *)
Int  Bool  String  Top
A -> B            (* function        *)
A & B             (* intersection    *)
A | B             (* union           *)
{ l : A; m : B }  (* record          *)
mu a. A           (* iso-recursive   *)
A => B            (* functor         *)

type Point = { x : Int; y : Int }        (* alias, expanded at use sites *)
```

```ocaml
(* expressions *)
1   true   "s"   ()
fun (x : Int) -> x + 1               (* parameters are always annotated *)
let x = 1 in x                       (* the type is synthesized *)
let rec f (n : Int) : Int = ...      (* needs a return annotation *)
if c then a else b                   (* `else` is mandatory *)
{ a = 1; b = 2 }     r.a             (* records and projection *)
e1 ,, e2                             (* non-dependent merge *)
e1 ,,, e2                            (* dependent: the right side sees the left *)
(inl e : A | B)                      (* injections need an ascription *)
case e of inl x -> u | inr y -> v end
(fold e : mu a. A)      unfold e
open e in body
?    e.[n]    box e in body          (* escape hatches onto the raw calculus *)
```

```ocaml
(* modules *)
module M = struct let a : Int = 1  let b : Int = a + 1 end
module S = sandbox struct ... end              (* elaborates under Top *)
module F (X : { a : Int }) = struct ... end    (* the parameter is the import *)
module A = F({ a = 1 })
module L = link M with functor (X : { a : Int }) -> struct ... end
module N = linkall M with functor (X : { a : Int } & { b : Int }) -> ...
open M
```

A program is a sequence of declarations, optionally followed by `;; expr`.
Without one it evaluates to the record of everything it binds at the top level.

## Things worth knowing

**A structure is a dependent merge chain.** `struct` builds a left-nested `Mrg`,
so a declaration can use the ones before it — and because `Mrg` extends the
context by exactly one slot holding *all* the preceding fields, every earlier
field is reached the same way, as `(?.0).l`.

**Sandboxing really cuts the context.** `sandbox struct` and `sandbox functor`
elaborate under `Top`, so nothing from the enclosing scope is reachable inside.
Referring to an outer binding there is a scope error, not a runtime surprise.

**There is no subtyping.** The elaborator compares types with structural
equality, so a module that is *wider* than a functor's import is rejected by
direct application:

```ocaml
module Counter = struct let start : Int = 10  let bump : Int = 1 end
module Doubler (X : { start : Int }) = ...

Doubler(Counter)                    (* rejected: Counter's type is wider *)
Doubler({ start = Counter.start })  (* fine *)
link Counter with Doubler           (* fine: linking looks the label up *)
```

Linking is the mechanism that copes with this — it projects each imported label
out of the module rather than demanding an exact match.

**Both branches of `case` and `if` must have the same type**, and `Cat`/`Eq`
and friends are the only primitives: the core has no other operations.

## Compiling to WebAssembly

[wasm/](wasm/) is a real backend for λE, not another interpreter:

```console
$ dune exec bin/main.exe -- --wasm out.wasm examples/modules.sce
$ node wasm/run.js out.wasm
{ started = 11; doubled = 20; next = 11; secret = 42 }
```

It targets **WasmGC**: values are garbage-collected structs, closures hold a
typed funcref called with `call_ref`, and the emitted module has no linear
memory and no function table at all — the engine's collector owns the heap.

Because λE has no variables there is no closure-conversion pass to write — the
calculus arrives pre-converted. A function becomes a lifted wasm function
`(self, arg) -> result` that rebuilds its own environment; and since the
program is typed and a merge value's shape mirrors its type's shape, `Proj`
and `Rproj` are resolved at compile time into fixed chains of `struct.get`.
See [wasm/README.md](wasm/README.md) for the scheme and the value layout.

## Separate compilation

The calculus was designed for it, and the toolchain now does it — at both
levels:

```console
$ main -c counter.sce -o counter.sceo        # writes Counter.scei alongside
$ main -c app.sce -o app.sceo                # `import Counter` reads it back
$ main --link counter.sceo app.sceo -o prog.sceo
$ main --run prog.sceo                       # link at core, evaluate
$ main --unit-wasm counter.wasm counter.sceo # each unit its own wasm module
$ main --unit-wasm app.wasm app.sceo
$ main --link-wasm linked.wasm counter.sceo app.sceo
$ node wasm/run.js linked.wasm counter.wasm app.wasm   # link at wasm, run
```

A unit is a **sandboxed functor** from its imports to its exports — closed by
the calculus itself, not by toolchain discipline. `import M` reads `M.scei`
(generated when the provider compiles), `import M : name` names an interface
file, and an inline type bypasses files; compile against interfaces, link
against implementations. Linking is the calculus's first-class linking: each
step applies the unit functor to a record of projections wired from the
providers, and the two linkers share one composition term — the core linker
splices the closed unit terms in and re-typechecks; the wasm linker compiles
the *same term* with the units installed through imports, so `Query` in the
link module *is* the loaded units. See [examples/units/](examples/units/).

## Layout

| path | role |
|---|---|
| [lib/core/](lib/core/) | λE: AST, typechecker, big- and small-step evaluators, printer |
| [wasm/](wasm/) | the WasmGC backend: IR, binary emitter, WAT printer, node host |
| [lib/sce/](lib/sce/) | λSCE: AST, evaluators, and the elaboration to λE |
| [lib/source/](lib/source/) | lexer, parser, `frames`, `debruijn`, `sugar`, `driver` |
| [lib/pipeline.ml](lib/pipeline.ml) | the five stages behind one `run` and one error type |
| [examples/](examples/) | runnable programs (units under `units/`), also test fixtures |
| [test/](test/) | parser, scope-resolution, end-to-end, differential and failure tests |

The test suite includes a differential check that λSCE evaluation agrees with λE
evaluation of its elaboration, that big-step agrees with small-step in both, and
that every program **compiled to WebAssembly and run under node** produces the
same value as the interpreter. The wasm tests skip themselves if `node` is not
installed.
