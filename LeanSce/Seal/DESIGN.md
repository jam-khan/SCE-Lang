# λE^≤ — a sealing core calculus (λE binding + Eᵢ restriction)

λE^≤ is the minimum extension of λE (Tan & Oliveira, OOPSLA 2024) needed to make
**sealing** expressible: a compilation unit can hide part of its structure so clients
compile against a declared interface rather than the unit's full inferred type. The
sealing primitive `(e : A)` and everything that supports it (subtyping, disjointness,
casting) is ported from Eᵢ (Tan & Oliveira, ECOOP 2023). Nothing here is claimed as
novel except the combination; every ported rule is credited below. The calculus is
deliberately minimal — it exists to serve the module/linking work in `SCE/`, not as a
general-purpose calculus.

Scope of this version: the paper fragment `Int | ε | A → B | A & B | {l : A}`,
**plus abstract type names (brands) for module sealing with type abstraction — see
§(g)**. Left out (and why): unions and iso-recursive μ (casting rules for them exist
in *neither* paper — open design); fix (paper-backed via Eᵢ Appendix B, natural next
step); polymorphism proper — type variables, ∀/∃ (λE §6.3 flags type-level
substitution under environment semantics as open; Eᵢ lists polymorphism as future
work). Type abstraction is obtained without type variables, by generative brands.

Mechanization: `Syntax`, `Subtyping`, `Disjointness`, `Casting`, `Typing`,
`SmallStep`, `CastingLemmas`, `Lookup`, `Determinism`, `Progress`, `Preservation`,
`Sealing` (binary logical relation + fundamental lemma + sealing corollary),
`Abstraction` (representation independence), `Elaboration`/`Correctness`/
`Linearization` (SCE → λE^≤, including sealed compilation units), `Examples`. Zero
`sorry`, zero custom axioms — everything uses at most `propext`.

---

## (a) Which of Eᵢ's complications are avoidable given de Bruijn indices?

**The ◦ abstraction mode is redundant.** In Eᵢ, `{e}◦ : {l : A} → B` exists for one
purpose: to model a conventional lambda whose parameter name is internal. Its rules
do exactly two things — `Typ-abs` extracts `{l : A}◦ = A` so the *type* is `A → B`
while the body addresses the argument through label `l`, and `Step-beta` wraps the
argument as `{l : A}⟨v⟩◦ = {l = v}` so the label lookup finds it. Both are
name-hiding devices. With de Bruijn binders the argument is addressed *positionally*
(`?.0`, since `lookup(Γ & A, 0) = A` — λE Typ-lam/Typ-proj), no label ever exists,
and the type is `A → B` directly. So λE^≤ has a single abstraction form and drops
the mode annotation, the `Aᵐ` extraction function, and the `A⟨v⟩ᵐ` value
constructor. (A second Eᵢ complication also dies: bidirectional typing. Eᵢ needs
checking mode to give annotations meaning; λE^≤ is fully syntax-directed — see (b)
note on where subtyping enters.)

**The `A ∗ Γ` premise of Typ-dmerge is NOT avoidable.** One might hope positional
lookup removes the ambiguity it guards. It removes the *lookup* ambiguity — `?.0` is
unambiguous, and `?.l` is guarded per-use by λE's containment judgment `l : A ∈ B`.
But it does not remove the *casting* ambiguity, because the sealing primitive
re-imports type-based selection: `(? : A)` reduces by casting the reified
environment. Eᵢ's own counterexample transplants directly: under context `Γ = Int`,
the merge `2 # {l = (? : Int)}` evaluates its right branch under environment
`v # 2`, and casting that environment at `Int` can select either the ambient `Int`
or the freshly merged `2` — two different results. Determinism of casting (Eᵢ
Lemma 6) needs the environment `v # v₁` to be *well-typed*, hence *consistent*, and
after `Step-merger` extends the environment the only source of that consistency is
`Γ ∗ A` via disjointness-implies-consistency (Eᵢ Lemma 4). So the premise stays.
The same reasoning adds `Γ ∗ A` to abstraction typing (beta extends the closure
environment with the cast argument).

## (b) Does merge stay dependent, and what side conditions does it need?

Merge stays dependent: `Γ ⊢ e₁ : A` and `Γ & A ⊢ e₂ : B` — dependent declarations
are the whole point (modules whose later fields use earlier ones), and the SCE
elaboration relies on it. But λE's premise-free `Typ-merge` is no longer tenable
once casting exists. λE happily types `1 # 2 : Int & Int`; sealing it — `(1 # 2 :
Int)` — would cast nondeterministically to `1` or `2`. Two conditions are added,
both ported from Eᵢ Typ-dmerge:

- `A ∗ B` — the branches must be disjoint, or the merged value itself is ambiguous
  under casting.
- `A ∗ Γ` — the left branch must be disjoint from the ambient context, or the
  extended runtime environment `v # v₁` is ambiguous under casting (see (a)).

Additionally, Eᵢ's *runtime* rule `Typ-mergev` (merge of values, premise: the
values are **consistent**, `v₁ ≈ v₂`, defined via casting) is ported. It is not
optional: values must be typeable under *any* context (value closedness, Eᵢ
Lemma 5 — the analogue of the mechanization's `value_weaken`, which preservation of
`Step-box`/`Step-boxv` depends on), and `Typ-dmerge`'s `A ∗ Γ` premise is
context-sensitive, so it cannot type closed value merges under arbitrary contexts.

Where subtyping enters (and nowhere else): (1) the sealing rule
`Γ ⊢ e : B → B <: A → Γ ⊢ (e : A) : A`; (2) two *runtime-only* slacks in closure
typing (input widening `C <: A`, body-result `B' <: B`) which are exactly what
preservation of arrow casting requires — this is our syntax-directed rendering of
Eᵢ's `C <: Aᵐ` premise plus checking-mode subsumption in Typ-abs, which Eᵢ itself
notes is runtime-only; (3) nothing else — application demands the exact argument
type, coercion is written explicitly as `(e₂ : A)`. There is no subsumption rule;
typing stays syntax-directed and inversion-friendly.

## (c) Which determinism route: typed selection or casting?

Both, because they answer different questions and neither subsumes the other.
λE^≤ keeps λE's *direct* selection `e.l` (`sel-mrgl`/`sel-mrgr`), nondeterministic
as a raw relation and tamed by the typing hypothesis through containment (λE
Lemma 4.1) — deliberately not Eᵢ's annotate-cast-project indirection, which the λE
paper explicitly criticizes. And it adds casting, also nondeterministic as a raw
relation (`Casting-mergevl`/`mergevr` overlap) and also tamed by a typing
hypothesis, through consistency (Eᵢ Lemma 6). Generalized determinism then carries
one typing premise (`ε ⊢ v : Γ`, `Γ ⊢ e : A`) that feeds both lemmas.

Implication for *elaborated* terms: the determinism/soundness theorems demand a
core typing derivation, but the witness available downstream is an elaboration
derivation. This is already the repo's pattern: `type_preservation`
(`SCE/Theories.lean`) converts `elabExp Γ es A ec` into `HasType ⟦Γ⟧ ec ⟦A⟧`, and
every determinism-style result for elaborated programs goes through it. The same
discipline transfers — with one new obligation: a future SCE→λE^≤ elaboration must
*establish the disjointness premises*. `edmrg` must carry `A ∗ Γ` and `A ∗ B`
(i.e., the source type system must check disjointness at merges), or elaborated
merges simply will not type in λE^≤ and the conversion theorem cannot exist.
Nothing about the proofs becomes harder; the side conditions just have to flow
from source typing.

## (d) The sealing property

Stated (and mechanized, in `Sealing.lean`) as a **binary, type-indexed logical
relation** — the binary generalization of λE's Fig. 4 semantic typing, defined by
structural recursion on the type:

- `v₁ ≈⟦Int⟧ v₂` — equal literals;
- `v₁ ≈⟦ε⟧ v₂` — both `ε` (degenerate; observations must be at `Int`);
- `≈⟦A & B⟧`, `≈⟦{l:A}⟧` — componentwise on merges / records;
- `v₁ ≈⟦A → B⟧ v₂` — **extensional**: both are closures, and for all arguments
  related at `A`, the *applications* co-evaluate to values related at `B`. (The
  clause is phrased at the application level so the semantics' internal
  argument-cast at the closure's annotation input is absorbed; runs are
  existentially quantified.)
- Open terms: `Γ ⊨ e₁ ≈ e₂ : A` quantifies over environments related at `Γ` —
  and because contexts *are* types, `≈⟦Γ⟧` itself is the environment relation; no
  separate context clauses are needed.

Results:
- **Fundamental lemma**: `Γ ⊢ e : A → Γ ⊨ e ≈ e : A`. (Termination of well-typed
  λE^≤ programs falls out, exactly as in λE §4.2.)
- **Casting respects the relation**: `v₁ ≈⟦B⟧ v₂ → B <: A → v₁ ↪_A v₁' →
  v₂ ↪_A v₂' → v₁' ≈⟦A⟧ v₂'` — the semantic content of sealing: the cast is a
  coercion between the relations. (Proof by induction on the subtyping derivation;
  the arrow case uses cast transitivity + cast determinism to reconcile resealing.)
- **Sealing corollary**: for providers `⊢ vᵢ : Bᵢ` with `Bᵢ <: A`, sealed as
  `vᵢ ↪_A vᵢ'`: if `v₁' ≈⟦A⟧ v₂'`, then for every client `A ⊢ e : Int`, the
  programs `v₁' ▷ e` and `v₂' ▷ e` evaluate to the **same integer literal**.

Precision about what this is and is not:
- It is **equality at base-type observations**, and a **logical relation (not
  syntactic equality) at arrow types** — extensional: the providers' functions may
  be different closures, they need only agree observably at the sealed type.
- It holds for **values/termination behavior only**. The calculus is pure and (by
  the fundamental lemma) strongly normalizing, so there are no effects or traces to
  speak of; nothing is claimed about an effectful extension (that would require a
  ⊤⊤-closed/biorthogonal relation and is **not established** here).
- On its own it is **not representation independence**: with the value-level seal
  `(e : A)` alone the client can name every type it depends on. What `(e : A)`
  hides is *width* (components not named in `A`) and *behavior beyond the seal at
  depth* (record fields and function results are resealed recursively).
  Width-hiding is in fact almost trivial in this calculus — the cast **erases**
  discarded components, so the sealed value literally does not contain them
  ("erasure sealing"); the genuine content of the theorem is extensionality at
  arrows and depth. Representation independence proper is §(g).

## (e) What breaks in λE's existing metatheory?

| result | verdict |
|---|---|
| **determinism** | needs a casting premise. Determinism of casting (Eᵢ L6, typing-hypothesis'd via consistency) joins determinism of selection (λE L4.1). Statement shape unchanged. *Mechanized.* |
| **progress** | needs a casting premise: progress of casting (Eᵢ L9) for the new `(v : A)` redex and the argument-cast in beta. Otherwise same structure. *Mechanized.* |
| **preservation** | needs the full casting lemma layer: transitivity (L10), consistency-after-casting (L11), preservation of casting (L12), disjointness⇒consistency (L4), value closedness (L5). Structure survives; the lemma layer is the cost. *Mechanized.* |
| **normalization** (λE Fig. 4 predicate) | statement survives; the proof needs one new semantic lemma — casting preserves the predicate (semantic subsumption). **No precedent**: no TDOS merge calculus has a mechanized normalization proof (Eᵢ's termination is unknown — λE paper Table 1). Here it *falls out of the sealing logical relation*, which is its unary shadow. *Mechanized (via `Sealing.lean`).* |
| **big-step equivalence** | needs cast premises in `Bstep-app` (argument cast + result reseal) and a new `Bstep-anno`; λE Lemma 4.18 (global-as-local) and the proof structure are unaffected. Believed routine. *Not mechanized.* |
| **STLC conservativity** | the *statement* is restored relative to Eᵢ (where it is unknown). The proof needs `S(v,e,k)` extended to annotated closures, the lemma "casting an STLC-image value at its own type is the identity", and the simulation becomes lock-step *up to administrative cast steps* (beta now emits a result annotation). Believed provable, genuinely new work. *Not mechanized.* |
| **SECD machine** | extension is systematic — a `Cast(A)` instruction implementing `↪_A`, `(e : A)` compiles to `⟦e⟧, Cast(A)`, beta's compilation casts the argument — but the machine becomes **type-passing**: types are runtime data. This makes the runtime cost of sealing visible (a cast traverses and rebuilds the sealed prefix). Correctness proof expected routine given big-step. *Not mechanized.* |

## (f) Full rule set with provenance

Provenance key: **(i)** unchanged from λE · **(ii)** ported from Eᵢ · **(iii)** new.

### Syntax

```
Types A, B, Γ ::= Int | ε | A → B | A & B | {l : A}          (i) — Eᵢ's Top ≡ λE's ε
Exprs e ::= ? | e.n | i | ε | e₁ ▷ e₂ | e₁ e₂ | e₁ # e₂       (i)
          | {l = e} | e.l                                     (i)
          | λ(A→B). e | ⟨v, λ(A→B). e⟩                        (iii) — λE's λA.e/⟨v,λA.e⟩
                                                                     with the codomain
                                                                     annotation forced (below)
          | (e : A)                                           (ii) — the sealing primitive
Values v ::= i | ε | ⟨v, λ(A→B). e⟩ | v₁ # v₂ | {l = v}       (i, closure modified)
```

**Why annotated lambdas are forced (the one deviation from design constraint 1).**
Sealing at an arrow type is inherently extensional: `Casting-arrow` must check
`B <: D` and *rewrite* the closure's return annotation, and beta must reseal every
call's result (`… ▷ (e : B)`). A substitution-free small-step semantics can only do
that if the codomain is materialized in the value: with λE's bare `⟨v, λA. e⟩`
there is nothing to check, nothing to rewrite, and the cast result cannot
re-synthesize the target type (there is no subsumption rule to absorb the gap), so
preservation of casting fails. Every escape hatch (typed casting rules; forbidding
arrows under seals; value-level subsumption) either breaks the
consistency/typing stratification, kills the module use-case, or destroys
syntax-directedness. Hence `lam A B e` / `clos v A B e`.

### Subtyping `A <: B` — all (ii), Eᵢ Fig. 1 verbatim (ε plays Top)

```
S-z:    Int <: Int
S-top:  A <: ε
S-arr:  B₁ <: A₁ → A₂ <: B₂ → A₁ → A₂ <: B₁ → B₂
S-andl: A₁ <: A₃ → A₁ & A₂ <: A₃
S-andr: A₂ <: A₃ → A₁ & A₂ <: A₃
S-and:  A₁ <: A₂ → A₁ <: A₃ → A₁ <: A₂ & A₃
S-rcd:  A <: B → {l : A} <: {l : B}
```

### Ordinary, top-like, value generator — all (ii)

`Ordinary A` (casting variant: not ε, not &): `Int`, `A → B`, `{l : A}`.
`⌉A⌈`: `⌉ε⌈`; `⌉A&B⌈` if both; `⌉A→B⌈` if `⌉B⌈`; `⌉{l:B}⌈` if `⌉B⌈`.
Generator: `ε↑ = ε`, `(A&B)↑ = A↑ # B↑`, `{l:A}↑ = {l = A↑}`,
`(C→D)↑ = ⟨ε, λ(C→D). D↑⟩`, and (total-function junk) `Int↑ = ε` — every lemma
about `A↑` is guarded by `⌉A⌈`, so the junk value is never observable.

### Disjointness `A ∗ B` — (ii), Eᵢ Def. 1 / Appendix A.1

Taken *algorithmically* as the definition: `A ∗ B := ¬(A ⊓ B)` where `⊓` is the
COST (Common Ordinary Super Type) relation:

```
Cost-int:   Int ⊓ Int
Cost-andl:  A ⊓ C → A & B ⊓ C          Cost-randl: A ⊓ B → A ⊓ B & C
Cost-andr:  B ⊓ C → A & B ⊓ C          Cost-randr: A ⊓ C → A ⊓ B & C
Cost-arr:   B ⊓ D → A → B ⊓ C → D
Cost-rcd:   A ⊓ B → {l : A} ⊓ {l : B}
```

**It ports cleanly**: the λE^≤ type grammar is exactly Eᵢ's (given ε ≡ Top), so
Def. 1 / A.1 transfer without change. (The spec form — "no common ordinary
supertype" — and the equivalence Eᵢ Thm 22 are not needed by any proof here; we
work with COST directly. `Cost-arr` ignoring input types is load-bearing: it is
what makes `(A→C) ∗ (B→D)` ↔ `C ∗ D` (Eᵢ L2.5) hold, which the closure cases of
consistency depend on.) Note the fragment *without* unions/μ is essential to "ports
cleanly": extending COST to unions or recursive types is exactly where it stops
being a verbatim port.

### Casting `v ↪_A v'` — all (ii), Eᵢ Fig. 3, arrow rules adapted to de Bruijn closures

```
C-int:     i ↪_Int i
C-top:     v ↪_ε ε
C-arrow:   ¬⌉D⌈ → C <: A → B <: D →
           ⟨v, λ(A→B). e⟩ ↪_{C→D} ⟨v, λ(A→D). e⟩
C-arrowtl: ⌉D⌈ → C <: A → B <: D →
           ⟨v, λ(A→B). e⟩ ↪_{C→D} (C→D)↑
C-mrgl:    Ordinary A → v₁ ↪_A v₁' → v₁ # v₂ ↪_A v₁'
C-mrgr:    Ordinary A → v₂ ↪_A v₂' → v₁ # v₂ ↪_A v₂'
C-and:     v ↪_A v₁ → v ↪_B v₂ → v ↪_{A&B} v₁ # v₂
C-rcd:     v ↪_A v' → {l = v} ↪_{l:A} {l = v'}
```

Casting is deliberately **typing-free** — its premises mention only the closure's
own annotations, never a typing derivation. (A "typed cast" would collapse the
stratification between `Consistent` — defined from casting — and `HasType` — whose
`tmergev` rule consumes consistency.) Top-like machinery is unavoidable given
S-top: `(A→ε) ∗ (B→ε)` holds (Cost-arr needs `ε ⊓ ε`, and no COST rule produces
it), so a merge of two ε-codomain closures is well-typed, and casting it at `C→ε`
would fire both C-mrgl and C-mrgr with different results — C-arrowtl collapses
both to the canonical generated value.

`Consistent v₁ v₂ := ∀ A w₁ w₂, v₁ ↪_A w₁ → v₂ ↪_A w₂ → w₁ = w₂` — (ii), Eᵢ Def. 3.

### Typing `Γ ⊢ e : A` — provenance per rule

```
T-query:  Γ ⊢ ? : Γ                                                  (i)
T-int:    Γ ⊢ i : Int                                                (i)
T-unit:   Γ ⊢ ε : ε                                                  (i)
T-app:    Γ ⊢ e₁ : A → B → Γ ⊢ e₂ : A → Γ ⊢ e₁ e₂ : B               (i)  exact arg type
T-box:    Γ ⊢ e₁ : Γ₁ → Γ₁ ⊢ e₂ : A → Γ ⊢ e₁ ▷ e₂ : A               (i)
T-proj:   Γ ⊢ e : B → lookup(B, n) = A → Γ ⊢ e.n : A                (i)
T-rcd:    Γ ⊢ e : A → Γ ⊢ {l = e} : {l : A}                          (i)
T-rproj:  Γ ⊢ e : B → l : A ∈ B → Γ ⊢ e.l : A                        (i)  λE containment
T-mrg:    Γ ⊢ e₁ : A → Γ & A ⊢ e₂ : B → A ∗ Γ → A ∗ B
          → Γ ⊢ e₁ # e₂ : A & B                                      (i) + (ii) premises
T-mrgv:   ε ⊢ v₁ : A → ε ⊢ v₂ : B → v₁ ≈ v₂
          → Γ ⊢ v₁ # v₂ : A & B         (values only)                (ii)
T-lam:    Γ ∗ A → Γ & A ⊢ e : B → Γ ⊢ λ(A→B). e : A → B              (i) + (ii) premise
T-clos:   Value v → ε ⊢ v : Γ₁ → Γ₁ ∗ A → Γ₁ & A ⊢ e : B'
          → B' <: B → C <: A → Γ ⊢ ⟨v, λ(A→B). e⟩ : C → B            (i) + (ii) slacks
T-anno:   Γ ⊢ e : B → B <: A → Γ ⊢ (e : A) : A                       (ii)  THE SEALING RULE
```

Flagged uncertainty (u1): `T-clos`'s double slack is our syntax-directed rendering
of Eᵢ's `Typ-abs` (`C <: Aᵐ` premise) + checking-mode body subsumption. Believed
equivalent on the common fragment; equivalence not proved. A consequence: closure
typing is not functional (a closure inhabits many arrow types) — harmless for the
theorems (all ∀-quantified over a derivation), but inversion lemmas are stated
existentially.

### Small-step `v ⊢ e ↪ e'` — congruence style (as in the mechanization; the paper's frames are equivalent)

```
S-query:  v ⊢ ? ↪ v                                                  (i)
S-proj:   v ⊢ v₁.n ↪ lookupv(v₁, n)                                  (i)
S-mrgr:   v # v₁ ⊢ e₂ ↪ e₂' → v ⊢ v₁ # e₂ ↪ v₁ # e₂'                 (i)
S-box:    v₁ ⊢ e ↪ e' → v ⊢ v₁ ▷ e ↪ v₁ ▷ e'                          (i)
S-boxv:   v ⊢ v₁ ▷ v₂ ↪ v₂                                            (i)
S-clos:   v ⊢ λ(A→B). e ↪ ⟨v, λ(A→B). e⟩                              (i)  carries B now
S-beta:   v₂ ↪_A v₂' →
          v ⊢ ⟨v₁, λ(A→B). e⟩ v₂ ↪ (v₁ # v₂') ▷ (e : B)              (iii) — λE shape,
                                                       Eᵢ cast premise + result reseal
S-sel:    v₁.l ⇝ v₂ → v ⊢ v₁.l ↪ v₂                                   (i)  sel-mrgl/mrgr
S-annov:  v₁ ↪_A v' → v ⊢ (v₁ : A) ↪ v'                               (ii)
+ congruence rules for each frame position, incl. the new (e : A)     (i) + (ii)
```

`S-beta`'s cast is what makes casting and de Bruijn indices *compatible*: the body
addresses the argument at type `A` (positionally and by label), and `C-and`
rebuilds the argument's merge structure to follow `A`'s intersection structure, so
runtime `lookupv` agrees with static `lookup`. Without the cast, an argument passed
at a subtype would have the wrong shape and positional lookup would be unsound.

### Not included (deliberately)

Type components / existentials / polymorphism (see header); unions and μ (no
casting rules exist in either paper); fix (Eᵢ App. B makes it a mechanical
extension); BCD/distributive subtyping (Eᵢ future work; would break the simple
COST story); big-step semantics, STLC conservativity, and the SECD machine for
λE^≤ (statements and expected proof burdens are in (e); out of the minimal
correctness scope).

### Relation to SCE

SCE keeps elaborating to Core (λE) unchanged; λE^≤ is a sibling target — and the
retargeting is now **mechanized** for the module/linking fragment
(`Elaboration.lean`: `elabSeal`, `seal_type_preservation`). It covers
mstruct/mfunctor/mclos/mapp/mlink/mlinkn/letb/openm/nmrg, records, boxes,
lambdas, closures, and dependent merges; unions/fix/μ have no rules (no casting
exists for them in either paper). As predicted in (c): every context-extending
rule carries the `Disj` premises on the `sealTyp` images — the source type
system must check disjointness. Two findings from doing it:

- **The bind-once combinators are dead and sealing replaces them.** Core's
  `nmrgCore`/`linkedCore` use the self-application idiom `(λ⟦Γ⟧. …) ?`, which is
  untypeable in λE^≤ — `tlam` demands `Γ ∗ Γ`, false for any non-top-like `Γ`.
  Instead `(? : Γ)` *restricts the extended environment back to the ambient one*,
  so the non-capturing merge is `e₁ # ((? : Γ) ▷ e₂)` and the link combinators
  are merges of sealed boxes. The construct λE needed combinator machinery for
  is a one-liner once restriction is first-class.
- **n-ary linking needs a disjointness-enriched interface judgment** (`WireOk`):
  SCE's `LinkOk` carries only the import lookups; λE^≤ additionally needs each
  accumulated import package disjoint from the ambient context and from the next
  import (`wireArgSeal_typed`).

Semantic preservation is now **mechanized** too (`Correctness.lean`):
`seal_semantic_preservation` simulates source big-step evaluation by target
`MStep` runs, with values related by `EVal` — *elaboration up to top-like
collapse*.  The syntactic statement used for the Core target is false here: beta
casts the argument and reseals the result, and casting a closure at a top-like
arrow collapses it to the generator; `EVal` mirrors value elaboration, stores
EVal-related closure environments, and admits the generator at any top-like type.
Its key lemma is `eval_cast_self` (casting at a value's own type preserves the
relation); the restriction combinators are handled by `eval_env_restrict`
(cast-of-extended-env = self-cast of the ambient part, via `cast_merge_eq_l` —
the semantic payoff of the `A ∗ Γ` premise).  Corollaries:
`seal_whole_program_correctness`, `seal_separate_compilation` (+`_closed`, `_n`,
`_n_closed`), and `mstep_value_determinism`.

Bind-once (linearized) linking is mechanized in `Linearization.lean`.  Core's
bind-once spelling is untypeable in λE^≤ (binding the module value puts `Γ₁` in
the context, and the body's merge then needs `Γ₁ ∗ (Γ & Γ₁)`, which fails); the
working spelling uses Eᵢ's fresh-label wrap — bind `{x = m}` so the bound copy has
type `{x : Γ₁}` — with freshness premises `¬Lin x ⟦Γ⟧`, `¬Lin x ⟦Γ₁⟧` as the price
of evaluate-once under a sealing discipline (`linkedSealLin_typed`,
`seal_separate_compilation_lin`, `_closed`).  Coherence with the evaluate-twice
seal spelling is `linearization_coherent_seal`, stated at the EVal level — Core's
syntactic-equality coherence is provably the wrong statement here (asymmetric
top-like collapse).  The non-capturing merge needs no linearized variant at all:
`e₁ # ((? : Γ) ▷ e₂)` already evaluates each operand once.  The n-ary bind-once
combinator is the same construction iterated per import (projections from the
bound value under re-sealed environments) and is left as mechanical.

Still open on this path: a source-level signature-ascription construct
elaborating to `(e : A)` (one rule + one BStep case), and fix/unions/μ as before.

---

## (g) Type abstraction: brands, `seal`, and representation independence

**Goal.** ML-style module sealing: a unit implements a signature `S` with an abstract
type `α`, over some representation `R`; clients compile against `S` with `α` opaque;
two implementations over different representations, related in the standard
relational way at `α`, are indistinguishable to every client. Mechanized as
`representation_independence` (`Abstraction.lean`).

**Route.** Not type variables (∀/∃): under environment semantics that reopens λE §6.3
(type-level substitution as resolution-under-environment, casts at type variables
across closure environments, COST with variables, disjoint quantification just to
discharge `tlam`'s `Γ ∗ A`). Instead, **generative brands**: an abstract type is a
statically allocated type name `brand n` (α_n) whose representation lives in a
private *brand store* `Δ : Nat → Option Typ`; sealed values are wrapped `⟨n⟩v`; the
seal is a coercion between the two views of a signature. Provenance: Sumii–Pierce
dynamic sealing / Matthews–Ahmed (parametricity via runtime sealing) /
Neis–Dreyer–Rossberg (non-parametric parametricity: type analysis + generated names
still gives representation independence) — minus dynamic name generation, because in
SCE seals happen at compilation-unit boundaries and brands can be allocated by the
linker like symbols. Static brands ⇒ no allocation ⇒ no Kripke worlds; strong
normalization ⇒ no step index. **Slogan: sealing = casting + branding.**

**Rules.**

```
Typ  ::= … | brand n
Sub:   brand n <: brand n           (only; NOT brand n <: R — that is translucency, kills RI)
Cost:  brand n ⊓ brand n            (so  α_n ∗ B  iff  α_n does not occur in B: disj_brand_notin)
Ordinary (brand n); ¬TopLike (brand n); genVal (brand n) = ε (junk, guarded as for Int)
Exp  ::= … | wrap n e | seal n R S e | unseal n R S e        Value ::= … | ⟨n⟩v
Cast:  ⟨n⟩v ↪_{brand n} ⟨n⟩v          THE ONLY NEW CAST RULE

Δ; Γ ⊢ e : A                                  (typing carries the unit's brand store)
twrap:    Δ n = R → v value → Δ; ε ⊢ v : R → Δ; Γ ⊢ ⟨n⟩v : brand n
tseal:    Δ n = R → NoRes R → WfSig n R S → Δ; Γ ⊢ e : S[n:=R] → Δ; Γ ⊢ seal n R S e : S
tunseal:  Δ n = R → NoRes R → WfSig n R S → Δ; Γ ⊢ e : S       → Δ; Γ ⊢ unseal n R S e : S[n:=R]
```
Clients are typed with `Δ n = none`: they can use α_n opaquely but cannot brand, seal
or unseal at it; both client and provider derivations weaken to the union store
(`hastype_weaken_store`), which is how the composed program types.

`WfSig n R S`: every `A & B` inside `S` is disjoint in *both* views (abstract and
representation — disjointness is preserved by substitution in neither direction:
`α & Int` vs `Int & Int`; `α & α` vs `ε & ε`), and `S` (and `R`, `NoRes`) avoid the
reserved label `#f`.

**Semantics.** `seal`/`unseal` on values step in one shot through value-level coercion
relations `SealV`/`UnsealV` (mirroring how `(v : A)` steps through `Cast`), structural
on the signature: wrap/unwrap at `brand n`, identity at other leaves, componentwise at
`&`/records, and at arrows a **proxy**
```
seal   n R (A → B) c  ↪  ⟨ ε # {#f = c},  λ(A → B).           seal n R B (?.1.#f (unseal n R A ?.0)) ⟩
unseal n R (A → B) c  ↪  ⟨ ε # {#f = c},  λ(A[R] → B[R]).   unseal n R B (?.1.#f (seal n R A ?.0)) ⟩
```
Why a proxy and not `Casting-arrow`'s annotation rewrite: the underlying body computes
at `R`, the client passes `⟨n⟩v`; something must unwrap on the way in and wrap on the
way out. Why the closure is stored under a *reserved record label*: `tclos` demands
`Disj Γ₁ A` for the closure environment; a bare closure environment COST-collides with
any signature arrow of matching codomain (e.g. `S = (Int→Int)→Int`); a record under a
label the signature cannot use is disjoint from everything in it (`disj_proxyEnv`).
Why coercions are relations on values and not structural term rewriting: an
intermediate `mrg (seal … v₁) (seal … v₂)` would have to be typed by `tmrg`, whose
`A ∗ Γ` premise fails under an arbitrary ambient context; the one-shot value coercion
re-types the result via `tmergev` + `disjoint_consistent` (hence `WfSig`).

**Why casting at a brand must not be universal.** The tempting rule `v ↪_{α_n} ⟨n⟩v`
for all `v` (let the cast install the brand) destroys the calculus: every value would
cast at α_n, so `5` and `{l = 3}` — typed at disjoint types — would cast at α_n to
different values, `disjoint_consistent` (Eᵢ L4) fails, with it `tmergev`, value
closedness, and preservation. Casting at a brand is therefore the identity on
same-brand wrappers and undefined otherwise; branding is installed by `seal` only.
Consequently `Consistent ⟨n⟩v ⟨n⟩v'` iff `v = v'`, matching Eᵢ's treatment of
`Int # Int`.

**Metatheory.** Every Eᵢ casting lemma (L4–L12) re-established with brands
(`CastingLemmas`); progress of the coercions by canonical forms
(`sealv_progress`/`unsealv_progress`); preservation of the coercions
(`sealv_preservation`/`unsealv_preservation`, the proxy typed by `tclos` with the
reserved-label environment); determinism of the coercions is typing-free (the
signature's shape picks the rule). `gdeterminism`, `gprogress`, `gpreservation`
extend.

**The relation.** `LRg Δ₁ Δ₂ η o` — two stores (the two providers have different
representations, so left values type under Δ₁ and right values under Δ₂), a brand
interpretation `η : Nat → Exp → Exp → Prop`, and an *open brand*
`o : Option (Nat × Typ × Typ)`:
- `o = none` (`LR`): every brand abstract — at `brand m` two values are related iff both
  are wrappers whose payloads are η-related.
- `o = some (n, R₁, R₂)`: brand n open — at `brand n` two values are raw
  representations, typed at R₁/R₂, related by η n; every type is read through the
  substitution (`viewL`/`viewR`). This is the relation the *implementations* stand in.
`cast_lr` and `toplike_lr_gen` are proved once for both views (`OpenAdm`: the
representations are not top-like, so top-likeness agrees across views, and η n is
closed under self-casts at R₁/R₂ — a mild admissibility condition forced by beta's
argument-cast at a proxy's annotation). The fundamental lemma is stated for *client*
typing (`HasType noBrands`): a client cannot wrap/seal/unseal, and everything else it
can do respects η by construction. This stratification is what avoids a relation that
recurses through the store.

**Results.** `coe_lr`: sealing carries implementation-relatedness to
client-relatedness and unsealing carries it back (mutual induction on the signature;
the arrow case runs the proxies). `representation_independence`: for `OpenBrand`
(stores agree on n, reps `NoRes` and not top-like, η n cast-closed), `WfSig` on both
sides, implementations `p₁ p₂` related in `LRg (some (n,R₁,R₂)) S`, and any client
`noBrands; S ⊢ e : Int`: `(seal n R₁ S p₁) ▷ e` and `(seal n R₂ S p₂) ▷ e` evaluate to
the same literal. Instantiated in `Examples.lean` (`{mk : Int → α} & {get : α → Int}`
over `Int` vs `{v : Int}`).

**Scope limits (design choices, stated up front).**
- No functor polymorphism over abstract types: an import interface names the concrete
  brand it links against — natural for `--link sys counter app`, but "generic" functors
  need type variables.
- Applicative-by-brand generativity: a `seal` inside a functor body uses the same brand
  and representation for every application (sound; not ML-generative).
- One brand per `seal`; several abstract types = nested seals.
- Top-like representations excluded (`OpenAdm`); a top-like abstract type is inhabited
  only by the generator anyway.
- Brand allocation is a toolchain concern (`WfStore`-style uniqueness assumed; the
  implementation must allocate distinct brands per sealed unit).

**The SCE source side (sealed compilation units).** SCE mirrors the target one-to-one:
`SCE.Typ.brand n`, `SCE.substBrand`, and the runtime/coercion forms `wrap n e`,
`mseal n R S e`, `munseal n R S e` (`SCE/Syntax.lean`), with the same structural
value-level coercions `SSealV`/`SUnsealV` (source proxies are `clos (ε # {#f = c}) A
(mseal n R B (?.1.#f (munseal n R A ?.0)))`; SCE lambdas carry only the domain) and
big-/small-step rules `BStep.wrap/mseal/munseal`, `SStep.ss…`; SCE's own equivalence,
determinism and preservation extend (`SCE/…`). Design decision: `mseal` is *not*
transparent at the source — the source and target both wrap — so that `EVal`
(elaboration-shaped simulation relation, "up to top-like collapse") gets a plain
clause `EVal.wrap` and `eval_cast_self` survives. The Core-targeting elaboration
(`SCE/Elaboration.lean`) has no rules for the sealing forms — Core has no brands, so
sealed units live in the λE^≤-targeted development only.

Elaboration (`Seal/Elaboration.lean`) carries a *source* brand store
`Δ : SCE.BrandStore := Nat → Option SCE.Typ`; the target store is its image
`sealStore Δ`; `sealTyp (S[n:=R]) = (sealTyp S)[n:=sealTyp R]` (`sealTyp_substBrand`).
Rules `ewrap`/`emseal`/`emunseal` mirror `twrap`/`tseal`/`tunseal` (`emunseal`'s
result type is equation-guarded like `tunseal`'s); `seal_type_preservation :
elabSeal Δ Γ e A ce → HasType (sealStore Δ) …`; only these three rules consult Δ, so a
derivation weakens along store extension (`elabSeal_weaken_store`) — a client compiled
knowing no representation composes with the provider that has it. Semantic
preservation (`Correctness.lean`) covers the sealing forms through `eval_sealv`/
`eval_unsealv`: source `SSealV` is simulated by target `SealV` on `EVal`-related
values, structurally on the signature; the arrow case relates the two proxies directly
by `EVal.clos` (the proxy body elaborates rule-for-rule), so no mutual induction is
needed; generator-shaped values (`EVal.gen`) are re-split along the signature.
Corollaries: `seal_separate_compilation_sealed` (a sealed provider `mseal n R Γ₁ p`
linked into a client functor compiled in any smaller store) and
`source_representation_independence` — a source client typed against `S` with every
brand opaque computes the same literal against either sealed source provider whose
elaborations are related as implementations (semantic preservation + target RI +
determinism). `Examples.lean` runs the `{mk} & {get}` example at the source level
(`sRun₁`/`sRun₂` evaluate the sealed source programs through the proxies to 5).
Brand allocation remains a toolchain concern: the mechanization takes Δ as a
hypothesis; the implementation allocates distinct brands per sealed unit, like symbols.

## (h) Brand polymorphism: ∀β, conservative disjointness, and the instantiation-closed relation

**Goal.** One generic client serving many sealed providers: `Λβ. λ(s : Sig β). …` typed
once at `∀β. Sig β → Int` and instantiated at each provider's brand. The target-side
mechanization is Phase 3 (`bvar`/`allb`/`blam`/`bclos`/`bapp` + the full safety layer +
the relational ∀-clause and `generic_client_representation_independence`).

**Syntax route.** Brand variables are their own de Bruijn namespace `Typ.bvar i`, bound
by `Typ.allb` — disjoint from both `Typ.var` (μ) and `Typ.brand` (concrete names).
Instantiation `bsubst d n T` substitutes the CLOSED `brand n`, so no shifting exists
anywhere (the μ/substTyp trick). `blam A e` steps to `bclos ρ A e` capturing the ambient
environment (the lam→clos pattern); both carry the ∀-body annotation because casting at
a ∀-type is an identity the VALUE must pin (the fold/wrap precedent — else
cast_preservation's `cbclos` case is unprovable). `bapp (bclos ρ A e) n` beta-steps to
`box ρ (bsubstExp 0 n e)` — instantiation is pure annotation rewriting, no reseal.

**Conservative COST at brand variables.** Disjointness must be stable under
instantiation (`disj_bsubst`, unconditional), because the substitution lemma inducts
over whole derivations whose intermediate types may mention the instantiation brand.
Equivalently: `Cost` may only be LOST under `bsubst`, never gained. Hence `cbvar` (any
two bvars), `cbvarbrand`/`cbrandbvar` (a bvar against any brand, both directions so
`cost_symm` stays a permutation), and the HasBVar-guarded `callbbv`/`cmubv` (two
syntactically distinct ∀- or μ-bodies can become equal after substitution — the subtle
gain case; without `cmubv`, `disj_bsubst` is false). Consequence (the price of
conservativity): nothing typed at a bvar, or at a bvar-containing μ/∀, can be MERGED
with anything brand- or bvar-typed — the same "wrap them in records" discipline as
`Cost.coror` for unions. Module-land disjointness is label-driven, so signatures like
`{mk : Int→β} & {get : β→Int}` are unaffected. Fallout: the equality-keyed compose
lemmas (`cost_mu_compose` etc.) are FALSE with the conservative rules and were replaced
by refl-leaf peels (`sub_brand_peel`/`sub_var_peel`/`sub_mu_peel`/`sub_bvar_peel`/
`sub_allb_peel`) — subtyping-derived costs end in the exact leaf, which is all
`sub_sub_cost` needs.

**The runtime-merge split (`tmergev`/`tmergevc`).** `Consistent` is not bsubst-stable
(two closures with domains `bvar 0` and `brand 5` are consistent — no common cast
target — until β:=5 identifies the domains), so `tmergev` gains a `Disj A B` premise.
But casting one value at `A & B` (Casting-and) duplicates it into a merge with NO
disjointness (`anno 3 (Int & Int)` steps to `mrg 3 3`) — a Disj-only rule falsifies
preservation. Resolution: a second rule `tmergevc` for cast-duplicated merges that
records the common ORIGIN (its typing and the two casts). That shape is bsubst-stable
BY CONSTRUCTION: the substituted components are casts (`cast_bsubst`) of the
substituted origin, so consistency is rebuilt semantically (`consistent_after_cast`)
rather than assumed. Both rules keep `Consistent` so the ~60 inversion sites stay
mechanical.

**The three fences** (all liftable later, none needed by the motivating example):
- `¬ AllbIn T` on `tfold`/`tunfold`: `substTyp` does not shift brand variables, so a ∀
  INSIDE a μ-body would capture cross-binder bvars (`bsubst_substTyp_comm` holds exactly
  under the fence). μ over an OUTER β stays allowed.
- `BClosed 1 A` on `tbapp`: the shift-free beta is index-coherent only when the ∀-body's
  bvars are bound by its own binder (single-binder polymorphism).
- `¬ HasBVar` on captured contexts (`tblam`/`tbclos`), on representations
  (`twrap`/`tseal`/`tunseal`), and on signatures (WfSig has NO bvar case;
  `wfsig_no_hasbvar`): contexts, provider stores and sealing annotations are
  bsubst-invariant. Sealing and ∀ therefore compose as seal-first, abstract-second —
  the ∀ serves the CLIENT side, matching the motivating example.

**The relational ∀-clause: instantiation closure.** The clause (Sealing.lean's `LRg`):
related generic values are values, typed at the SYNTACTIC `∀β.A` (under the ambient
view), and for EVERY concrete brand m the runs of `bapp · m` exist and are related at
`bsubst 0 m A`. η is never extended and no freshness is demanded: at brand-m positions
the relation is whatever η already says about m — exactly what representation
independence needs, since the client instantiates at the provider's own allocated brand,
where η relates the two representations. Two rejected designs, for the record:
- *η-extension at a concrete brand* is unsound (a fresh-brand guard excludes
  instantiation at allocated provider brands; an unguarded extension conflates β with
  existing brands in the tblam intro case).
- *δ-environments* (bvar-interpretation environments keeping the relation structural)
  die on a fork: with typing conjuncts at δ-instantiated images, the fundamental at the
  empty δ is false for degenerate bvar-annotated subjects (`lam (bvar 0) (bvar 0) e` is
  well-typed but its closure is not typed at the image) unless a properly-bound
  discipline (EBClosed) is threaded through the statement AND the tclos/tfclos
  contravariant slacks; with syntactic typings, the δ-analog of the substitution lemma
  is false, and a nonvacuous bvar interpretation demands runs of UNsubstituted bodies —
  which are stuck (casts at bvar annotations are empty, `cast_bvar_empty`).
The instantiation-closure clause keeps typings syntactic (degenerate subjects stay
vacuously related through the False bvar clause — exactly as pre-∀) and runs only
substituted bodies. Its one cost: `LRg` recurses at `bsubst 0 m A`, which is not a
subterm — the definition descends on `tsize` (bsubst trades a bvar leaf for a brand
leaf, so it is size-preserving) by well-founded recursion, and therefore no longer
unfolds definitionally: clause construction/destruction goes through `simp only [LRg]`
(and the `lr_and_intro` helper). What is NOT delivered: free theorems over arbitrary
relations at β (relational parametricity proper). That needs the δ-environment
machinery plus the EBClosed discipline — future work; RI of generic clients does not.

**Fundamental over generics.** `Finitary` includes `blam`/`bclos`/`bapp` (sbappbeta
rewrites only annotations — never duplicates subterms, so normalization is preserved).
The lemma is proved by strong induction on `esize` (annotations excluded, so
`esize_bsubstExp` is an equality): the tblam/tbclos cases recurse at the INSTANTIATED
body — typed by `hastype_bsubst`, not a subderivation — because the unsubstituted body
cannot run; the tbapp case instantiates the clause at its own brand and finishes by
`mstep_bapp` composition. `generic_client_representation_independence`
(Abstraction.lean) then runs the client to a generic value, instantiates the ∀-clause at
the provider brand n (landing at `arr (bsubst 0 n Sig) Int` — the concrete-signature
world), seals the providers through `coe_lr`, and reads off the equal literal.
`Examples.lean` instantiates it: one `genClient`, two sealed providers over `Int` and
`{v : Int}` at brand 0, same output.
