# Compiling λE to WebAssembly-GC

```console
$ dune exec bin/main.exe -- --wasm out.wasm examples/modules.sce
$ node lib/wasm/run.js out.wasm
{ started = 11, doubled = 20, next = 11, secret = 42 }
```

Add `--wat out.wat` to also write the text form. The backend targets WasmGC
(standardized in wasm 3.0, on by default in every current engine): values are
garbage-collected structs, and the emitted module has **no linear memory and no
function table at all**.

## Why λE compiles the way it does

λE has **no variables**. `Query` (`?`) *is* the environment, and the environment
is an ordinary value; every binder works by extending it. So the calculus
arrives pre-closure-converted, and two things follow.

**Functions need no dispatch.** A function becomes a lifted wasm function
`(self, arg) -> result` that rebuilds its own environment from `self`:

| λE | environment the body builds |
|---|---|
| `Lam (A, body)` | `Mrg (cenv, arg)` |
| `Flam (A, B, body)` | `Mrg (Mrg (cenv, self), arg)` — argument at `?.0`, itself at `?.1` |

Each lifted body knows statically which of the two it is, so `App` never has to
ask what kind of closure it got: read the typed funcref out of the `$Clos`
struct and `call_ref`. There is no table and no index arithmetic — the funcref
in the struct *is* the function.

**Projections are static.** `Proj` and `Rproj` are searches in the interpreter,
but the program is typed and a merge value's shape mirrors its type's shape.
`Check.tlookup` and `rlookup_path` therefore settle every access at compile
time, so both become a fixed chain of `ref.cast` + `struct.get` — no spine
walk, no label comparison. `Proj (e, n)` is *n* left-field reads followed by one
right-field read; `Rproj (e, l)` follows the route the type dictates.

## Value representation

Every value is a reference to a struct subtyping `$Val`, whose first field is a
tag — **self-describing**, which is what lets `run.js` render a result without
being told its type, and therefore what lets compiled output be diffed against
the interpreter.

```
$Val    = struct { tag }                     the open supertype
$I32Box = struct { tag, n }                  Int and Bool
$Bytes  = array (mut i8)
$Str    = struct { tag, bytes }
$Pair   = struct { tag, left, right }        Mrg
$Lrec   = struct { tag, name bytes, value }
$Fn     = func (self, arg) -> value
$Clos   = struct { tag, fn, env }            Clos and Fclos
$Wrap   = struct { tag, value }              Inl, Inr, Fold
```

Types sharing a shape are told apart by tag alone. All types sit in one
recursion group; every reference is `(ref null ...)` so locals stay defaultable,
and no null is ever actually produced.

A record label rides inside the `$Lrec` value as bytes, so results assembled
from separately compiled modules render with no shared metadata (projection
never reads it — every `Rproj` is a static path). String literal and label
bytes live in one passive data segment, materialized with `array.new_data`.
λE types are erased entirely.

JavaScript cannot look inside GC structs, so the module exports accessors —
`tag`, `num`, `strLen`, `strByte`, `pairA`, `pairB`, `lrecNameLen`,
`lrecNameByte`, `lrecVal`, `wrapVal` — and `run.js` drives the walk, rendering in
exactly the format of [lib/core/pretty.ml](../core/pretty.ml).

## What the GC design removed

The first version of this backend targeted core wasm 1.0: tagged cells in
linear memory, a bump allocator, and a function table driven by
`call_indirect`. Moving to WasmGC deleted all three:

- **The allocator and its no-GC caveat.** `$alloc`/`box1`/`box2`/`mrg` are each
  now a single `struct.new`, and the engine's collector owns the heap — the old
  backend leaked every cell it ever allocated, by design.
- **The function table.** Closures hold a typed funcref; `call_ref` replaces
  `call_indirect`, and the table-slot bookkeeping (the source of a real bug in
  the linear backend) has nothing left to get wrong.
- **The host's memory walking.** `run.js` no longer reads raw bytes out of
  linear memory (and no longer has to re-take views after `memory.grow`
  detaches them); it calls typed accessors.

The runtime that remains is exactly the two functions that need a loop:
`strcat` and `streq`.

## Layout

| file | role |
|---|---|
| `ir.ml` | the module and instruction datatypes — the only thing the emitter and printer share |
| `abi.ml` | the type hierarchy, tags, field positions, fixed indices: the contract with `run.js` |
| `encode.ml` | LEB128, vectors, section framing |
| `emit.ml` | IR → a WasmGC binary: one recursion group, `call_ref`, passive data |
| `wat.ml` | IR → WAT text, for reading what was emitted |
| `runtime.ml` | `strcat`, `streq`, and the host accessor exports |
| `compile.ml` | λE → IR, following `Check.infer` rule for rule |
| `run.js` | the host: instantiate, call `main`, walk the result via accessors, render as `pretty.ml` does |

Binaryen cross-checks every module in the test suite:
`wasm-opt --enable-gc --enable-reference-types --enable-bulk-memory`
(bulk-memory covers the passive data segment `array.new_data` reads).

## Linking at the wasm level

Separate compilation reaches all the way down. Each unit compiles to its own
module through the unchanged compiler — `main` returns the unit's value, which
for a functor unit is literally its `$Clos`. The **link module** is this same
compiler applied to the linkers' shared composition term (each step applies a
unit functor to a record of projections wired from the providers), with one
difference in how the units are installed: `main`'s prologue calls one
imported `u<k>.main` per unit and merges the results into the environment, so
`Query` *is* the loaded units and every unit occurrence in the composition is
an ordinary `Proj (Query, i)`.

```console
$ main --unit-wasm counter.wasm counter.sceo
$ main --link-wasm linked.wasm counter.sceo app.sceo
$ node lib/wasm/run.js linked.wasm counter.wasm app.wasm
```

Values flow between instances because WasmGC type identity is structural: all
modules share the same recursion group, so the link module's casts and
accessors work on structs any unit created. Record labels ride inside `$Lrec`
values (not in per-module tables), which is what makes results assembled
across modules render correctly. The expected unit names travel in an
`sce.units` custom section; `run.js` checks the instantiation order against
it. Interface checking happens in the toolchain against the artifacts' stored
λSCE types — wasm's own type system sees only `() -> (ref null $Val)` imports,
with runtime casts backing what the calculus already proved.

## Host capabilities and the runtime loader (experimental)

A `Hostfn` value compiles to an ordinary `$Clos` whose funcref is a
trampoline into an imported `host.<name>` function, so `App` needs no new
case. `run.js` supplies the host object: `print` and `readfile` read string
payloads through the accessors, and build result values through the
constructor exports (`unitval`, `newStr`/`setStrByte`, `inl`, `inr`, `lrec`)
— JavaScript cannot construct GC structs itself.

The runtime loader's import *name* carries the expected interface
(`load:<printed type>`), and `--unit-wasm` stores each unit's printed slot
type in an `sce.slot` custom section. The check is string equality of the two
texts: `print_typ` is canonical, so equal texts are exactly structural type
equality — the static linker's check, made at instantiation time. Runtime
loads name `.sceo` artifacts; the host loads the `.wasm` sibling, so the same
program and the same config files drive both levels.

## Limitations

- Recursion depth is the wasm stack, so very deep recursion traps rather than
  raising a positioned error.
- Traps replace the interpreter's exceptions generally: a compiled division by
  zero reports `trap: divide by zero`.
- `Clos` and `Fclos` appearing in a *source* program are rejected — they are
  runtime-only values the front end never produces.
