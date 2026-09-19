# §6 Evaluation — plan (3–4 pages)

Thesis, argued three ways: **making linking a term of the calculus loses you
nothing.** RQ1: linking survives *lowering*. RQ2: transformation survives
*verification*, by semantics reuse. RQ3: linking's runtime cost is
*recoverable* by ordinary term rewriting, and the modular/whole-program
boundary is type-enforced.

Page budget: 6.1 ≈ 0.75p · 6.2 ≈ 0.75p (incl. the backends discussion) ·
6.3 ≈ 1p · 6.4 ≈ 1.25p (the catalogue table + convergence figure).

---

## 6.1 Design and Implementation (~0.75 page)

Everything the RQ sections *measure* is built here; the RQ sections only
present claims and results.

**Artifact.** Pipeline parse → desugar → resolve → elaborate (byte-identical to
`Elaboration.lean`) → typecheck → {interpret | WasmGC}. Separate compilation:
units as sandboxed functors, `.scei` structural contracts, core-level and
wasm-level linking sharing one composition term. State sizes: 20-constructor
IR, 400-line wasm compiler, ~180-line evaluator.

**Optimizer infrastructure (new).** `lib/core/opt/`: a shift/renumber substrate
over `Proj (Query, i)`, passes as λE→λE rewrites, `Check.typecheck` after every
pass, `-O` flags in the CLI. Insertion points: `compile_unit` (pre-link, per
unit) and `Linker.link` (post-link). Elaboration and linker untouched — passes
live outside the mechanized image.

**Closure conversion (new, feeds 6.3).** reach (typed access-path analysis;
whole-`?` escape ⇒ capture-all) → trim (`Lam` ↦ `Box (e_trim, Lam …)`,
Unit-based spine) → renumber. OCaml implementation + Lean mechanization of the
pure fragment.

**Corpus.** Existing: lambda/ (5 units, flagship — add `whole.sce` + fuel-scaled
variant), units/peano + twin, boot/effects (trace pins), worlds (`?`-escape
adversary), plugins/versions/upgrade/linker (open-world), fib-24 /
string-alloc. New: the five unit sets units/README.md already promises (hello,
geometry, textlib, diamond, interp — all with whole twins), and generators:
N-units×M-exports-1-used (scaling), deep-let far-use, closure churn, effect
permutation.

**Metrics + oracles.** Core node counts; capture-spine size and lookup-walk
counters in eval; Ir instruction histograms (`struct.new`/`ref.cast` by type);
dynamic counters via a small `Global_set` extension read by run.js; hrtime
around `main()`; binary bytes. Oracles: typecheck-after-pass, interpreter-vs-
wasm value+trace differential, commutation suite with optimized paths added,
junk-env closedness, force-application fixtures (printer hides returned-closure
envs), boot as the once-ness pin. `wasm-opt -O2` as the generic-optimizer
control (measured ~29% on modules.sce).

---

## 6.2 RQ1 — Does linking survive lowering? (~0.75 page)

**Claim.** The linking construct is not an interpreter artifact: the same
composition term drives core-level linking and *wasm-level* linking, where each
unit is a separately compiled module and linking happens at instantiation.

**Evidence (mostly exists).** The commutation table: every unit set gives one
answer through all seven toolchain paths (whole interpreted, whole→wasm,
core-linked one-shot/incremental/permuted, core-linked→wasm, wasm-linked) —
values *and* traces. Interface checking survives lowering too: `sce.slot`
carries the printed slot type, structural equality checked at instantiation
(the static linker's check, made late); `sce.units` pins link order.

**Why it works — and the 1-page discussion of other backends.** WasmGC's
*structural* type canonicalization is the ABI: every module emits the identical
recursion group, so values flow between instances with no shared metadata.
Backends without structural type identity pay differently: JS — trivial
(erasure); native — needs a uniform boxed representation or shared runtime
(structural casts have no hardware analogue); JVM/CLR — nominal classes block
cross-classloader structural sharing. Punchline: linking survives lowering
exactly where type identity is structural or erased.

**Work items.** The five unit sets (they instantiate the commutation table
beyond peano; geometry exercises cross-instance closures), lambda `whole.sce`.
Predictable outcome: green table — this RQ is consolidation, not risk.

---

## 6.3 RQ2 — Verified transformation by semantics reuse (~1 page)

**Framing.** *Can compiler transformations be expressed and verified within λE,
reusing its semantics and metatheory, rather than requiring a lowered target
language?* Closure conversion is the instance because classically it is the
counterexample: a language translation (closures become code+env packages) with
a cross-language logical relation. In λE, environments are already values and
closures already env+code — the calculus arrives pre-closure-converted — so the
pass degenerates to an intra-language rewrite: **environment strengthening**,
`Lam` ↦ `Box (e_trim, Lam …)`, existing syntax only (sandbox is the
trim-to-empty case already emitted).

**Theorem (scoped small).** Whole-program correctness at observable types:
`BStep unit e v → BStep unit (cc e) v`, plus typing preservation. No logical
relation — converted closures differ as values, results at base types do not.
Contextual equivalence: stated as future work.

**The measurable claim is reuse.** New Lean definitions ≈ 2 (reachability,
renumbering); zero edits to Syntax/Semantics; count reused lemmas vs new lines.
Honest split: mechanization covers the pure fragment (no Hostfn in Lean);
effect/trace preservation is empirical, via the differential harness.

**Empirical companion (small table).** Capture-spine sizes, allocations, casts,
binary bytes, before/after, on the corpus — one pass improves both backends
because the rewrite is at the calculus level.

**Risks / honest findings.** De Bruijn renumbering proofs are tedious — that
tedium is *data* (what the IR made us pay). First-class `?` escaping whole
(worlds) forces capture-all — report the precision frontier, don't hide it.
Administrative lambdas (every `let` is `App (Lam …)`) inflate closure counts —
measure after administrative β or report separately.

---

## 6.4 RQ3 — What does linking cost, and can optimization pay it back? (~1.25 pages)

**Framing.** Linking is a term, so its cost is visible *as terms* — and the
modular/whole-program optimization boundary is enforced by the calculus, not by
convention. Three falsifiable sub-claims:

1. **Pre-link optimization is boxed in by the theory.** Structural interface
   equality freezes export labels, types, and `&`-association; imports are
   effect-opaque. Only interface-invisible rewrites are legal — and the
   typechecker + trace suite *reject* violations.
2. **The linked program's overhead is the linker's own terms.** `link_step` /
   `nmrg_step` applications and wire projections are known closed redexes;
   post-link optimization = collapsing them + what concrete imports unlock
   (wire elimination, cross-unit inlining, dead exports), under the bind-once
   invariant (boot: one print, never three).
3. **Convergence.** The commutation suite proves *values* agree between
   `whole.sce` and its linked twin; RQ3 asks whether *cost* converges:
   does optimize(link(units)) reach optimize(whole)?

**Table 1 (condensed for the paper; full version in the artifact).** Rows:
administrative β · link-step β-normalization · wire elimination · cross-unit
inlining · dead internal bindings · dead exports · env trimming (6.3's pass) ·
projection folding · `Box(Query,e)`→`e` · constant/known-case folding ·
*disallowed:* host-call motion, merge reorder. Columns: pre-link / post-link
core / post-link wasm / gate (purity, once-ness, closed-world). Predictable
shape: the post-link-wasm column is nearly empty (separate instances, frozen
ABI) — that emptiness is a finding, the price of runtime-loadable modularity.

**Experiment.** Per benchmark with a whole twin, five points: whole-optimized
(gold) and linked under {none, pre, post, both}; report the gap to gold on
nodes/allocs/bytes/time. Figure: gap vs N units (generator). Purity gate read
off `.scei`: a unit importing no capability interface is pure — the modular
analysis is itself a small result. Open-world benchmarks (loader) excluded from
DCE arms, stated explicitly.

**Predictable:** pre-link alone leaves most of the gap; post-link closes most
of it on closed-world programs; a residual wasm-level gap remains and is
reported as a number. **Not predictable:** magnitudes and the slope in N —
the interesting curve.

---

## Order of work

1. **W0** 6.1 infrastructure: metrics, counters, harness extensions,
   force-application fixtures, `-O` flags.
2. **W1** opt substrate + cheap rows (admin β, projection folding, peepholes).
3. **W2** closure conversion in OCaml; precision study on worlds.
4. **W3** Lean mechanization of cc (pure fragment, base-type theorem).
5. **W4** post-link passes (link-step β, wire elim, closed-world DCE).
6. **W5** corpus completion (five unit sets, lambda whole, generators).
7. **W6** experiments, Table 1, convergence figure, writing.

Threats: administrative-closure inflation (separate counts); printer blindness
to returned closures (fixtures, W0); Marshal `.sceo` (stay inside the
constructor set); Lean drift (passes outside elaboration); loader reopening the
world (benchmark classification); node timing noise (hrtime around main,
medians, fuel scaling).
