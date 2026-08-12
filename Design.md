# Design

Why SCE-Lang looks the way it does: the decisions, the reasons, and the
example that demonstrates each one. Every example named here is a live test
fixture — the claims below are enforced by the suite, not asserted.

The one-sentence thesis: **interfaces are ordinary types, modules and functors
are ordinary terms, and linking is ordinary evaluation** — so separate
compilation, dynamic loading, and capability control are one mechanism seen at
three times, not three subsystems.

---

## 1. The core has no variables

λE and λSCE bind nothing by name. `?` (`Query`) denotes the entire typing
context — a left-nested intersection — and `?.n` projects its n-th component.
Every binder extends that intersection: `Lam` appends the parameter type,
`Letb` the bound type, `Mrg` the type of its left operand. The surface
language's central job is therefore to turn a *name* into a *position*
([lib/source/debruijn.ml](lib/source/debruijn.ml)), and the context discipline
lives in exactly one place ([lib/source/frames.ml](lib/source/frames.ml)),
shared by the resolver and the desugarer so the two cannot drift.

**Why.** Because the context is a first-class value, "run this code under that
environment" (`box`), "cut the environment off" (`sandbox`), and "extend the
environment with a provider" (linking) are all *term-level operations on the
same object*. Every headline feature below is a corollary of this choice.

**Consequence worth writing up** (found while building
[examples/worlds/](examples/worlds/)): the context discipline differs by
position. Whole-program `let`s are individual context entries — a snapshot of
them is addressed positionally (`?.[0]`). Inside a compilation unit, top-level
declarations form a *struct chain*, so earlier declarations are labeled fields
of an accumulated entry — the same snapshot is addressed by label (`?.Base`).
Label projection means the same thing in both, which is why the commuting
tests never notice; but any formal statement about `?` must be precise about
which discipline is in force.

## 2. No subtyping; linking is the coping mechanism

Types are compared with structural *equality* everywhere — `A & B ≠ B & A`, a
wider module cannot be passed to a narrower functor, and there is no
subsumption rule in either calculus.

**Why.** Subtyping is where module-calculus metatheory gets expensive
(coercions, principal signatures, avoidance). The observation this design
bets on: the *practical* need subtyping serves in module systems — "my
component provides more than you require" — is served by linking instead.
`link` looks the imported labels up in a wider provider and keeps both halves;
direct functor application demands the exact type.

**See** [examples/modules.sce](examples/modules.sce), which shows
`Doubler(Counter)` rejected and `link Counter with ...` succeeding —
side by side, with the rejection also pinned as a test
([test/test_sce.ml](test/test_sce.ml), "no subtyping on functor application").

## 3. One structural check is the whole ABI

A unit's interface (`.scei`) is a plain type, spelled structurally. The same
equality is checked at three different times:

| when | where | example |
|---|---|---|
| static link time | [lib/sepcomp.ml](lib/sepcomp.ml) `check_imports_satisfied` | [units/hello/](examples/units/hello/) |
| run time, by the loader | `do_load`: `slot_typ a = want` | [plugins/](examples/plugins/) |
| wasm instantiation | `sce.slot` custom section, printed-type equality | [dynconfig/](examples/dynconfig/) under node |

**Why.** The runtime check is *the static linker's check made later* — the
loader's declared import type is derived from the importing unit, so there is
no second notion of compatibility to trust. At the wasm level the comparison
is string equality of printed types, sound because `print_typ` is canonical
(it inverts the parser's precedence levels).

**Structural, not nominal, is load-bearing:**
[units/peano/](examples/units/peano/) has the consumer *redeclare* the
iso-recursive type `N`; it matches the producer's because equality is
structural. No nominal identity has to survive separate compilation — this is
the direct answer to ML's type-sharing (`with type`) machinery.
[units/interp/](examples/units/interp/) scales the same trick to a modular
interpreter: the `eval` and `show` passes import *nothing* and still agree
with the constructors' unit on the AST type.

**ADTs are a definitional extension.** OCaml-style datatypes
(`type shape = | Circle of Int | Rect of Int * Int | Point`, `match`, tuple
expressions) are pure surface sugar, eliminated by a named-AST pre-pass
([lib/source/adt.ml](lib/source/adt.ml)) before resolution: a declaration
becomes a plain alias over left-nested binary unions (`mu`-wrapped when a
payload mentions the type), tuple payloads become `{_1; _2}` records, and
constructors/`match` become exactly the ascribed `inl`/`inr`/`fold`/`case`
idioms a user writes by hand. Nothing downstream — resolution, desugaring,
elaboration, the mechanization, the wasm backend — changes, so the sugar
costs zero new metatheory. Constructor names are surface-only: the `.scei`
stays fully structural, and a consumer redeclares the type with *its own*
constructor names ([units/peano/](examples/units/peano/) does exactly this —
`Z`/`S` in the producer, `Zero`/`Next` in the consumer). The raw encodings
survive as tour exhibits ([unions.sce](examples/unions.sce),
[recursive.sce](examples/recursive.sce)), and the loader examples declare a
local ADT as a *view* on the host's structural result union — pattern
matching over a type the program did not define. Two structurally identical
ADTs are the same type — the nominal distinction OCaml enforces is
deliberately absent, matching §3.

## 4. Merges: ambiguity is caught late in the calculus, early in the toolchain

`Mrg`/`Nmrg` build intersections with no disjointness premise; a duplicated
label is rejected only at *projection* (`rlookup` refuses a label present on
both sides). The toolchain linker, by contrast, rejects overlapping exports
eagerly at link time, because a collision would make both copies permanently
unreachable.

**Why.** Keeping the calculus permissive keeps the metatheory small (no
disjointness judgment); making the linker strict keeps the failure early and
attributable ("units libv1 and libv2 both export 'Lib'").

**See** [examples/versions/](examples/versions/), which makes the policy a
feature: two versions of `module Lib` cannot be linked statically — that is
the ambiguity rejection — but version choice is *per use site*, so v1 arrives
through the link line while v2 is loaded at run time, and both run side by
side under one name. Dependency hell becomes a wiring decision.

## 5. A compilation unit is a sandboxed functor

Compiling a unit wraps it as a sandboxed functor from its imports (a record)
to its exports ([lib/sepcomp.ml](lib/sepcomp.ml) `unit_wrapper`). Linking
applies it to a record of projections wired out of the providers — built by
`Elab.link_step`, *the very term the in-language `link` elaborates to*, so
the toolchain's linker and the calculus's linking construct cannot drift.

**Why this is the paper's §5 in one sentence:** the separate compilation
theorem is a corollary because core linking coincides with elaborated source
linking. [examples/linker/](examples/linker/) makes it executable — the
hand-written dependent merge

```
let byhand = P ,,, f({ Seed = P.Seed })
```

agrees at run time — field by field, on both halves — with the builtin
`link P with f`, applied to the *same* functor `f` that arrived from disk.
There is no linker formalism to trust because the linker's composition term
is an ordinary term of the language.

**Two linking levels compose:** [units/textlib/](examples/units/textlib/) has
the toolchain link a unit whose own body uses first-class `linkall` — the
same mechanism at both levels, in one program.

## 6. Effects are capabilities, and authority flows only through linking

The language has no `print`. `Sys` is a provider unit the *host*
materializes; a program performs IO only if its link line grants it, and
`sandbox` cuts authority off with the rest of the context.

- **Confinement is a scope error, not a runtime denial.**
  [plugins/evil.sce](examples/plugins/evil.sce) reaches for `Sys` and does not
  compile; the test asserts the failure stage is `"scope"`.
- **Attenuation is ordinary code.** A capability record is just a record;
  wrapping `Sys.print` with a prefix is a lambda
  ([plugins/manager.sce](examples/plugins/manager.sce)).
- **Delegation is a record field.** [wiring/](examples/wiring/): the host
  passes one plugin's exported `run` as another's `peer` capability. No
  registry, no policy engine — connectivity exists exactly where the host
  constructed it.
- **Purity is visible in interface types.** A unit whose slot type mentions no
  capability-bearing import provably performs no effects — a property the
  optimizer or linker can read off the ABI. (Unused so far; a follow-up
  paper's hook.)

**Design rule that follows:** host capabilities are few and explicit —
`Sys` (`print`, `readfile`), `Str` (`head`, `tail` — strings are otherwise
write-only, so even *inspecting text* is a granted capability), and
`load:<type>` ([lib/sepcomp.ml](lib/sepcomp.ml) dispatcher), mirrored in
[wasm/run.js](wasm/run.js). In [lambda/](examples/lambda/) only the lexer
imports `Str`: the interface tells you which unit can look inside a string.

## 7. The loader: one import, typed by the ABI it enforces, failing as a value

`import Loader : { load : String -> (Sig | {err : String}) }` — the *success
type is the contract*. The host reads the declaration off the importing
artifact and builds a provider specialized to it. Restrictions, deliberate:
one `Loader` import per program, one success type.

**Use-site linking works on loaded functors unchanged.** The wire is
label-preserving rather than renaming, so the host aligns labels by building
the capability record under the client's import label — the plugin manager
instantiates each plugin as `(link { Cap = ... } with p).run`, first-class
linking applied to a functor that arrived at run time.

**Why failure-as-value matters:** every dynamic-linking example handles the
`inr` branch in-language — a missing plugin
([plugins/](examples/plugins/)), a missing config
([dynconfig/](examples/dynconfig/)), a missing upgrade
([upgrade/](examples/upgrade/)) — no exceptions, no crash paths.
"Rollback is not a mechanism; it is the `inr` branch."

**Shapes it supports today** (each pinned by a test):
a leaf record (dynconfig), a functor — the plugin ABI — (plugins, wiring,
harness), a functor whose import is the *previous version's exports* — a
typed migration contract ([upgrade/](examples/upgrade/)).

## 8. Recursive linking is a derived form, and the toolchain stays acyclic

The mechanization proves `linkrec` definable from `fix` + linking
(`mrec_elab`, RecLinking.lean), inheriting all metatheory as one-line
corollaries instead of needing its own. The reading is generative: each
recursive call re-applies the functor, so construction work repeats per
call — the recursive import must be function-typed for exactly this reason. The surface language can write the knot directly:
[linkrec/parity.sce](examples/linkrec/parity.sce) ties a functor whose import
interface is satisfied by its own export, giving mutual `even`/`odd` through
a single function-typed import — exactly the theorem's shape.

The toolchain linker is deliberately an acyclic left fold (imports must be
satisfied by earlier units): cross-unit recursion is out of scope *matching
the calculus* — recursion through linking exists precisely where the theory
covers it.

## 9. Environments are values; the escape hatches are not decoration

`?` reifies the world; `box e in body` enters another one; inside a box the
body sees *only* what the value contains — names from the enclosing scope do
not resolve ([lib/source/frames.ml](lib/source/frames.ml) resets the frame).

[worlds/](examples/worlds/) uses both directions with the toolchain:
a **loaded artifact is entered as the current environment**
(`box w in ?.Theme.decorate "hello"` — dynamic linking *is* "run code under
an environment that arrived at run time", literally), and a **snapshot**
(`let snap = ?`) is re-entered when a load fails — rollback by evaluating
under a value you kept. [harness/](examples/harness/) is the functor-level
counterpart: one loaded component instantiated under a live world and a
canned one — mocking with no framework, because environments are records and
instantiation is application.

These compile: `?`, `box`, and snapshots produce identical results across
interpreter, core-linked, and wasm-level-linked runs. First-class
environments are not an interpreter-only trick.

## 10. The wasm backend: structural identity all the way down

WasmGC, no linear memory, no tables. Design points that carry the thesis:

- λE arrives closure-converted by construction (no variables), so functions
  lift directly and `App` is `struct.get` + `call_ref`.
- **Cross-instance values work because WasmGC type identity is structural** —
  the same bet the source type system makes. A closure built by one instance
  is `call_ref`'d from another ([units/geometry/](examples/units/geometry/)).
- A unit's interface rides in an `sce.slot` custom section; the link module
  records expected unit names in `sce.units`; the host checks both.
- The wasm linker compiles *the same composition term* the core linker uses
  (`Sepcomp.compose`, parameterized only by how a unit occurrence is
  spelled) — one linker, two installations.
- Host capabilities compile to ordinary closures over trampolines into
  imported `host.<name>` functions; the runtime loader rewrites `.sceo` to
  `.wasm` siblings and re-checks the slot type at instantiation.

## 11. Testing is the design's enforcement mechanism

Two ideas, both worth stating in the paper's implementation section:

1. **Commuting differentials.** Every unit set runs through up to eight
   paths — whole interpreted, whole→wasm, core-linked (one-shot /
   incremental / permuted), core-linked→wasm, wasm-level-linked, binaryen
   validation — and all must agree ([test/test_commute.ml](test/test_commute.ml)).
   The separate-compilation theorem, checked operationally, per commit.
2. **Trace differentials.** Capability-bearing programs must print the same
   lines in the same order under the interpreter and under node
   ([test/test_runtime.ml](test/test_runtime.ml)) — effects, not just values,
   commute with compilation. Traces are compared under a *fixed* link line:
   link order commutes for values (that is what the permuted paths check),
   not for traces — reordering providers reorders their construction effects,
   as the semantics prescribes ([boot/](examples/boot/)).

Negative fixtures are first-class: `evil.sce` (scope error), the versions
ambiguity rejection, stale-`.scei` detection, wrong-interface loads. Every
example directory is a fixture; examples cannot rot.

## 12. Deliberate cuts, and the concrete challenge each one hides

Honest future-work material (§8 of the paper):

- **No sealing / abstract types.** Signatures are fully transparent
  (`elabModTyp (TyIntf t) = elabTyp t`). The challenge: abstraction in a
  calculus where the context is a *type* means deciding what `?` reveals —
  an abstraction boundary must censor the reified environment, which
  interacts with `box` and with structural ABI checks.
- **No polymorphism.** Every functor is monomorphic; the interp case study's
  passes are per-type. Challenge: type variables in context position — the
  context is a type, so quantification quantifies over contexts.
- **No subtyping / no disjointness** (§2, §4): revisiting either reopens the
  metatheory the design deliberately closed; the linker currently *is* the
  answer to width. A limited "width coercion at link time only" might keep
  the calculus clean while easing the exact-equality friction.
- **No inference.** Parameters annotated, `let rec` needs a return type,
  injections/folds ascribed. Cost is visible in every example; benefit is
  that synthesis-only typing keeps elaboration syntax-directed (uniqueness
  theorems in the mechanization depend on it).
- **Single loader, single success type.** Multi-typed loading (versions +
  upgrade in one program) currently requires pairing one static and one
  dynamic route. Generalizing means labeled loader capabilities — mechanical,
  but touches host, interpreter, and wasm host in lockstep.
- **Performance is unoptimized.** Environments are linked merge chains
  (O(depth) lookup), closures capture the whole world, elaboration leaves
  administrative redexes. The interesting research direction is
  *pay-as-you-go*: programs that never reify `?` should compile identically
  to a conventional de Bruijn compiler — first-class environments costing
  zero unless exercised. Deferred until after the current writing pass.
- **Artifacts are OCaml `Marshal`** with a magic header — not portable, not
  safe on untrusted input. Fine for a research prototype; a paper claim about
  deployment would need a real serialization.

## 13. Map: claim → example → test

| claim | example | test |
|---|---|---|
| structs/functors/link/open, no subtyping | [modules.sce](examples/modules.sce) | test_sce end-to-end + rejection |
| ADTs and `match` as pure sugar over unions/mu | [adt.sce](examples/adt.sce) | test_sce sweeps + adt-stage rejections |
| provider sharing (diamond), link-order freedom | [units/diamond/](examples/units/diamond/) | test_commute `diamond` |
| structural types replace nominal sharing | [units/peano/](examples/units/peano/) | test_commute `peano` |
| modular passes over a shared structural AST | [units/interp/](examples/units/interp/) | test_commute `interp` |
| functor closures cross wasm instances | [units/geometry/](examples/units/geometry/) | test_commute `geometry` |
| both linking levels in one program | [units/textlib/](examples/units/textlib/) | test_commute `textlib` |
| capabilities via link lines; sandbox cuts them | [effects/](examples/effects/) | test_runtime `effects` |
| construction effects fire once per unit, however many imports wire it | [boot/](examples/boot/) | test_runtime `boot` |
| plugin ABI = loader's import type; confinement = scope error | [plugins/](examples/plugins/) | test_runtime `plugins` |
| config-driven relinking, failure as value | [dynconfig/](examples/dynconfig/) | test_runtime `dynconfig` |
| same-name versions: static rejection, per-use-site choice | [versions/](examples/versions/) | test_runtime `versions` |
| manager-wired delegation between plugins | [wiring/](examples/wiring/) | test_runtime `wiring` |
| typed dynamic upgrade with state handoff | [upgrade/](examples/upgrade/) | test_runtime `upgrade` |
| recursive linking as a derived form (Thm 31) | [linkrec/](examples/linkrec/) | test_sce pinned value |
| the linker is a term of the language | [linker/](examples/linker/) | test_runtime `linker` |
| environments as values: box-entry, snapshot rollback | [worlds/](examples/worlds/) | test_runtime `worlds` |
| one artifact, live and canned worlds | [harness/](examples/harness/) | test_runtime `harness` |
| a lambda-calculus interpreter with parsing: ADTs, units, and the Str capability at scale | [lambda/](examples/lambda/) | test_runtime `lambda` (+ wasm, wasm-level) |

Every `test_runtime` row above also runs through the wasm trace differential
and the wasm-level-linked variant.
