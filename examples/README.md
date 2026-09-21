# Examples

Every example here is a live test fixture: the suite runs each one on every
commit, so nothing on this page can rot.

Single files run directly; unit sets and capability examples have a CLI
session in their own README (linked below):

```console
$ dune exec bin/main.exe examples/modules.sce      # whole file, interpreted
$ dune exec bin/main.exe -- --wasm out.wasm examples/modules.sce && node lib/wasm/run.js out.wasm
```

## The tour (single file)

The surface language — literals, records, ADTs, the two merges — is
introduced in the paper's language section. The one file kept here carries a
design claim rather than a syntax lesson.

| file | what it shows |
|---|---|
| [modules.sce](modules.sce) | structures, sandboxing, functors, application, linking, `open` — and the no-subtyping story: `Doubler(Counter)` is rejected because `Counter` is *wider* than the import; `link Counter with Doubler` is how width is handled |

## Separate compilation ([units/](units/))

`units/peano/` ships with `whole.sce` — the same program as one file. The
commutation suite drives it through every toolchain path (whole interpreted,
whole→wasm, core-linked one-shot / incrementally / permuted, core-linked→wasm,
wasm-level-linked) and requires one answer from all of them. That is the
separate-compilation theorem, checked operationally.

| set | the claim it carries |
|---|---|
| [units/peano/](units/peano/) | a recursive ADT crossing units. The consumer *redeclares* the type with its own constructor names (`Z`/`S` vs `Zero`/`Next`); structural equality makes them compatible — the answer to ML's `with type` sharing machinery |

## Effects and runtime linking

The language has no print statement. `Sys`, `Str`, and `Loader` are
host-built provider units; a program has exactly the authority its link line
grants (`--link sys loader app.sceo`), and everything else about capabilities
is ordinary code.

| example | the claim it carries |
|---|---|
| [effects/](effects/) | effects enter through linking: `--link sys` grants IO; `sandbox` is effect confinement (a scope error, before types); attenuation is a wrapper lambda |
| [boot/](boot/) | construction-time effects meet the linker: a provider that prints while building its exports, wired into a two-import consumer, prints *once* — the operational pin for linearized (bind-once) elaboration; a spliced composition term would print three times |
| [plugins/](plugins/) | a plugin manager in the language: artifacts loaded at run time, interface-checked structurally (the static linker's check, made later), each plugin instantiated by `link` *at the use site* — `(link { Cap = ... } with p).run` — against an attenuated capability record. [evil.sce](plugins/evil.sce) reaches for `Sys` directly and does not compile — the negative fixture is part of the suite |
| [versions/](versions/) | two versions of one library. Linking both statically is rejected — same-name coexistence is an ambiguity, caught eagerly with both units named — but choice is per *use site*: v1 arrives on the link line, v2 by runtime load, both alive under one name. Dependency hell becomes a wiring decision |
| [upgrade/](upgrade/) | typed dynamic upgrade: v2 is a functor whose import interface *is* the migration contract (old state in, new module out). A missing or drifted upgrade comes back as `inr {err}` and v1 keeps running — "rollback is not a mechanism; it is the `inr` branch" |

## The calculus at work

Examples that only make sense in a language where environments are values and
linking is a term.

| example | the claim it carries |
|---|---|
| [linkrec/](linkrec/) | recursive linking as a *derived form*: a functor whose import is satisfied by its own export, knot tied by ordinary `let rec` — exactly the shape the mechanization proves sound, inheriting all metatheory. The toolchain linker stays acyclic on purpose; recursion through linking exists precisely where the theory covers it |
| [linker/](linker/) | the link step, written in the language it links: the hand-written dependent merge `P ;; f({ Seed = P.Seed })` is checked at run time against the builtin `link P with f` — the *same* functor `f`, arrived from disk, compared field by field on both halves. There is no linker formalism to trust, because the linker's composition term is an ordinary term |
| [worlds/](worlds/) | environments as values, both directions: a loaded artifact is *entered* as the current environment (`box w in ?.Theme.decorate "hello"` — dynamic linking is literally "run code under an environment that arrived at run time"), and a snapshot `let snap = ?` is re-entered when a load fails — rollback by evaluating under a value you kept |

## Case study: [lambda/](lambda/)

A lambda-calculus interpreter with real text parsing, written as five units
(`lexer`, `parser`, `eval`, `pretty`, `main`) — the first non-toy program in
the tree, and every claim above shows up in it at once: ADTs for tokens,
terms, and results, redeclared structurally across units; failure as a value
(parse errors and an evaluation fuel bound); and string *introspection* as a
granted capability — the core's only string primitives are `^` and `=`, so
`Str.head`/`Str.tail` arrive through the link line and only the lexer imports
them. The interfaces alone tell you which unit can look inside a string. The
suite also runs the whole thing under node, with `str` compiled as its own
wasm module.

## Conventions worth knowing

- **Running artifacts:** `--run` executes a linked artifact's `main` export
  if it has one; otherwise the module value itself is the result. (Whole
  files without a `main` binding evaluate to the record of their
  top-level bindings.)
- **Through wasm:** every session below also runs compiled. Replace
  `--run prog.sceo` with `--wasm prog.wasm prog.sceo` and
  `node lib/wasm/run.js prog.wasm`; an artifact a program loads *at run time*
  needs its `.wasm` sibling first (`--unit-wasm shout.wasm shout.sceo`), since
  the host loads `X.wasm` where the interpreter loads `X.sceo`. The suite
  (`test/test_runtime.ml`, `test/test_commute.ml`, `test/test_wasm.ml`)
  checks that both routes print the same trace and the same value. See
  [lib/wasm/README.md](../lib/wasm/README.md) for the backend itself.
- **Notation vs the paper:** the surface `Top` is the paper's unit/empty
  type ε; surface `;` is the paper's parallel merge and `;;` its dependent
  merge; `?` is the paper's environment query; `sig A end` is the paper's
  signature type Sig A (the type of a `struct`) and `A => B` its functor type.
- **Elided primitives:** `Bool`, `String`, comparison and arithmetic
  operators (`&&`, `mod`, `/`, …) are implementation primitives layered on
  the formalized calculus, which has only `Int` and ε as base types.

## Reading order

`modules` → `units/peano` → `effects` → `plugins` → `versions` → `upgrade` →
`worlds` → `linker` → `linkrec` → `lambda`. Every directory README ends with
the exact CLI session and expected output.
