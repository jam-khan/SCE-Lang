# Compiling λE to WebAssembly

```console
$ dune exec bin/main.exe -- --wasm out.wasm examples/modules.sce
$ node wasm/run.js out.wasm
{ started = 11; doubled = 20; next = 11; secret = 42 }
```

Add `--wat out.wat` to also write the text form.

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
ask what kind of closure it got: load the table slot out of the cell and
`call_indirect`.

**Projections are static.** `Proj` and `Rproj` are searches in the interpreter,
but the program is typed and a merge value's shape mirrors its type's shape.
`Check.tlookup` and `rlookup_path` therefore settle every access at compile
time, so both become a fixed chain of loads — no spine walk, no label
comparison. `Proj (e, n)` is *n* loads of the left field followed by one of the
right; `Rproj (e, l)` follows the route the type dictates.

## Value representation

Every value is an `i32` pointer to a tagged cell. Cells are **self-describing**,
which is what lets `run.js` render a result without being told its type — and
therefore what lets compiled output be diffed against the interpreter.

| tag | cell | value |
|---|---|---|
| 0 | `[0][n]` | `Lit (Int n)` |
| 1 | `[1][0\|1]` | `Lit (Bool b)` |
| 2 | `[2][ptr][len]` | `Lit (String s)` |
| 3 | `[3]` | `Unit`, one preallocated cell at address 4 |
| 4 | `[4][left][right]` | `Mrg` |
| 5 | `[5][label id][val]` | `Lrec` |
| 6 / 7 | `[6\|7][table slot][env]` | `Clos` / `Fclos` |
| 8 / 9 | `[8\|9][val]` | `Inl` / `Inr` |
| 10 | `[10][val]` | `Fold` |

Labels are interned into a table in the data section, so a record field costs one
integer at runtime rather than a string. Types are erased entirely.

Every literal in a program is known up front, so literals are **static cells**
and compile to a constant address — no allocation for `1`, `true` or `"abc"`.

## Memory

```
0        unused, so 0 is never a valid pointer
4        the Unit cell
8..      literals, string bytes, label names, then the label table
heap     bump pointer ($hp), grows a page at a time
```

`$alloc` rounds up to a word and grows the memory when the top passes the
current size. **There is no GC** — the heap only grows. That is fine for the
programs this compiles today, and is the obvious next thing to fix.

## Layout

| file | role |
|---|---|
| `ir.ml` | the module and instruction datatypes — the only thing the emitter and printer share |
| `abi.ml` | tags, offsets, fixed function/type indices: the contract with `run.js` |
| `encode.ml` | LEB128, vectors, section framing |
| `emit.ml` | IR → a WebAssembly binary (core 1.0 only: no GC, no bulk memory) |
| `wat.ml` | IR → WAT text, for reading what was emitted |
| `runtime.ml` | the emitted prelude: `$alloc`, `$box1`, `$box2`, `$mrg`, `$strcat`, `$streq` |
| `compile.ml` | λE → IR, following `Check.infer` rule for rule |
| `run.js` | the host: instantiate, call `main`, walk the heap, render as `pretty.ml` does |

## Limitations

- No GC; the bump allocator only ever grows.
- Recursion depth is the wasm stack, so deep recursion traps rather than
  raising.
- `Clos` and `Fclos` appearing in a *source* program are rejected — they are
  runtime-only values the front end never produces.
- Traps replace the interpreter's exceptions, so a compiled division by zero
  reports `trap: divide by zero` rather than a positioned error.
