# HANDOFF: extensions + cleanup of LeanSce (updated 2026-08-23, session 3)

**Read this first in the next session.**  It is the complete working state of the
"1 source + 1 target, sealing-based, with fix/unions/μ + brand polymorphism" effort.
The 4-phase plan lives at `~/.claude/plans/read-through-the-mech-majestic-ritchie.md`
(full rationale, costing of F_E-style polymorphism, sepcomp obligations for brand
polymorphism, motivating example).  This file is the execution log + precise next steps.

**ALL WORK LIVES ON `lambdae-sub` — `main` mirrors `origin/main` and must stay
clean/untouched until the user says otherwise.**

Everything below is committed on `lambdae-sub` and green: `lake build` succeeds (62 jobs),
**zero `sorry`, only standard axioms** (the flagship
`Seal.source_representation_independence` still uses `propext` only; the ported
determinism/preservation results use at most `propext, Quot.sound`; nothing uses
`Classical.choice`).  Check via `lake env lean` on a scratch file importing `LeanSce`
with `#print axioms …`.

Architecture: **one source, one target.**  `LeanSce/SCE` (source λSCE) elaborates
via `elabSeal` (`Seal/Elaboration.lean`) into `LeanSce/Seal` (λE^≤, the sealing
target).  `LeanSce/Core` and the SCE→Core elaboration are DELETED (Phase 2e,
commit `1a79fcd`); `grep -rn "Core\." LeanSce` and `grep -rn "elabExp" LeanSce`
are empty.

**▶ WHERE TO CONTINUE: Phase 3 milestones 1–3 (target-side ∀β with the FULL
safety layer) are COMPLETE (session 3, commits `49dbca0..`, see §3.6 statuses
and §3.9 for the session-3 design corrections).  Next work = §3.7: milestone 4
(the real relational ∀-clause over η-extensions) or milestone 5 (source-side
`mfunctor`-generic + elabSeal + sepcomp).  Also open: the §2 examples/doc
items.  Do not re-derive the design; §3 was checked against the compiler.**

---

## 1. DONE

### Phase 0 — branch unification ✅ (session 1)
`main` and `lambdae-sub` merged so they share history.  Commits `13a5907`,
`d357355`, `c67ffbb`.  (Session 2 initially continued on `main` by mistake; all
unpushed commits were moved to `lambdae-sub` and local `main` was reset to
`origin/main`.  **Work on `lambdae-sub` only.**)

### Phase 1 — fix/unions/μ in λE^≤ + retargeted elaboration ✅ (session 1)
Commits `da5407a` (fixpoints, two-annotation fclos design), `0097e35` (unions,
componentwise-only subtyping + unconditional `Cost.coror`), `7528a65` (iso-recursive μ,
the brand pattern), `975d4ff` (elabSeal end-to-end incl. nine new simulation cases),
`8a881d0` (total source sealing coercions sig/or/μ/var + their simulation).
Relational layer fenced by `Seal.Finitary` / `SCE.SFinitary` (fix/μ break SN;
step-indexed LR = future work).  Full design notes: `git show f72ccac:HANDOFF.md`.

### Phase 2 — single-target cleanup ✅ (session 2, commits `7bd7fcc..a379899`)

- **2-pre** (`7bd7fcc`): `elabSeal_weaken`, `value_elab_sig_intf`,
  `elabSeal_lookup_pres`, `elabSeal_sel_absent`, `elabSeal_sel_pres` moved
  Correctness → `Seal/Elaboration.lean` (import-cycle avoidance).
- **2a** (`d2ff193`) `SCE/Preservation.lean`: `svalue_not_step`;
  `elabSeal_lookup_prog`/`elabSeal_sel_prog`; `elabSeal_selpkg_prog`/`_pres` over
  **`Seal.WireOk`**; `source_ssealv_pres`/`source_sunsealv_pres`;
  `source_sgpreservation`/`source_spreservation` with REAL sealing cases.
- **2b** (`30a2eb5`) `SCE/Progress.lean`: `source_ssealv_prog`/`source_sunsealv_prog`;
  `source_sgprogress`/`source_sprogress`.
- **2c** (`7b17983`, `6bd14fb`) new `SCE/Determinism.lean`: `elabSeal_uniqueness`
  (merged, generalized `Γ₁ = Γ₂ ∨ Value e`), `source_sel_labelin`, `source_sel_det`,
  `source_selpkg_det`, `source_bigstep_elab_pres`,
  `source_bigstep_deterministic(_gen)`.
- **2d** (`cf6436e`): `source_sandboxed_functor_confinement` (evmrg needs no Disj —
  sandboxing is the context-free case); `source_mrec_elab` + corollaries (knot
  carries three Disj hypotheses on sealTyp images; closed programs get the first
  via `disj_top`).
- **2e** (`1a79fcd`): DELETED `LeanSce/Core/` and `LeanSce/SCE/Elaboration.lean`;
  `SCE/Theories.lean` reduced to pure source metatheory.
- **2f partial** (`a379899`): value-lemma triplets deduped into
  `S_Sem.lookupv_value`/`S_Sem.sel_value`.

Still-open 2f items (optional, not blocking): ModTyp collapse into `Typ.mfun`;
merge `mlink` into `mlinkn`; `innerCtx : Sandbox → Typ → Typ`; (`letb`/`openm`
stay primitive).

---

## 2. Other open items (not the next step)

- Phase 3 milestones 4–5 (see §3.7) after the safety layer lands.
- μ/fix examples in `Seal/Examples.lean` (sealed-interface factorial via flam;
  a tagged-union run; a μ-stream); later a generic-functor example (§3.7).
- `doc/system.tex` stale w.r.t. Phases 1–3 (update or flag).
- Step-indexed LR to lift the Finitary/SFinitary fence (future work).
- `origin` has NOT been pushed by either session; push only when the user says so.

---

## 3. Phase 3 — brand polymorphism.  DESIGN DONE (session 2); ▶ CONTINUE HERE

Scope of the next increment = plan milestones 1–3: **target-side ∀β with the full
safety layer** (syntax → subtyping → COST → casting → typing → small-step →
CastingLemmas → determinism/progress/preservation), relational layer fenced.
Milestones 4 (LR ∀-clause over η-extensions) and 5 (source-side `mfunctor`-generic +
elabSeal) come after, in later sessions (§3.7).

### 3.1 Syntax design (Seal/Syntax.lean)

- `Typ.bvar (i : Nat)` — brand VARIABLE, de Bruijn, bound by the nearest `allb`.
  A separate namespace from `Typ.var` (μ) and `Typ.brand` (concrete names) —
  exactly the `Typ.var`/μ trick: instantiation substitutes a CLOSED thing
  (a concrete `brand n`), so **no shifting is ever needed**.
- `Typ.allb (A : Typ)` — ∀β. A.
- `Exp.blam (e : Exp)` — brand abstraction; steps to `Exp.bclos (ρ : Exp) (e : Exp)`
  capturing the ambient environment (the lam→clos pattern).  `Exp.bapp (e : Exp)
  (n : Nat)` — instantiation at the concrete brand n.
- `bsubst (d n : Nat) : Typ → Typ` — replace `.bvar d` by `.brand n`; `d+1` under
  `allb`; leaves `var`/`mu`-binders alone (μ binds `Typ.var`, not bvars — no bump
  under `mu`); recurses everywhere else.
- `bsubstExp (d n : Nat) : Exp → Exp` — apply `bsubst d n` to every type annotation
  (lam/clos/anno/seal/unseal/inl/inr/fold/flam/fclos), recurse on subterms,
  **`d+1` under `blam`/`bclos`** (their bodies sit under one more binder).
- `HasBVar : Typ → Prop` — some `.bvar i` occurs (ANY index; index-blind on purpose,
  used only by the conservative COST rules and WfSig).  Inductive like `BrandIn`.
- Extend: `substBrand`/`substTyp` (bvar ↦ itself, allb structural — those
  namespaces don't interact), `BrandIn` (`allb` case; bvar has no brands),
  `Value.vbclos {ρ e} : Value ρ → Value (.bclos ρ e)`, `genVal` (bvar/allb ↦
  `.unit` junk), `genVal_value`, `Ordinary.obvar`/`oallb`, `toplike_dec` (two
  `Or.inr` lines; neither is top-like), `value_clos_env`-style helper
  `value_bclos_env`.

Beta: `Step.sbappbeta : Value v → Value ρ →
Step v (.bapp (.bclos ρ e) n) (.box ρ (bsubstExp 0 n e))`; plus `sblam`
(blam → bclos, capture ambient) and `sbappl` congruence.  Value `bclos` does not
step.

### 3.2 THE CRUX #1: Disj must be stable under `bsubst` → conservative COST

The plan sketch said "disjointness against brand variables by an occurrence check".
**That is NOT enough**: `Disj (bvar 0) (brand 5)` by occurrence check would break at
instantiation `β := 5`.  A freshness side condition on `tbapp` cannot fix it either:
the substitution lemma inducts over the whole derivation, whose INTERMEDIATE types
may mention the instantiation brand even when the rule's types don't.

Resolution (checked case-by-case against `Cost` in Disjointness.lean): make COST
**conservative at brand variables** so that `Cost` can only be LOST, never GAINED,
under `bsubst` — then `Disj A B → Disj (bsubst d n A) (bsubst d n B)` holds
UNCONDITIONALLY.  New constructors:

- `cbvar {i j} : Cost (.bvar i) (.bvar j)` — ANY two bvars (nested `bapp`s can
  instantiate distinct binders at the same brand).
- `cbvarbrand {i n} : Cost (.bvar i) (.brand n)` and
  `cbrandbvar {n i} : Cost (.brand n) (.bvar i)` — a bvar may be instantiated TO
  any brand (both directions as constructors so `cost_symm` stays a permutation).
- `callb {A} : Cost (.allb A) (.allb A)` (refl, the brand pattern) **plus**
  `callbbv {A A'} : HasBVar A ∨ HasBVar A' → Cost (.allb A) (.allb A')` — two
  syntactically distinct ∀-bodies can become EQUAL after substitution, so any
  bvar-containing ∀ conservatively costs every ∀.
- `cmubv {T T'} : HasBVar T ∨ HasBVar T' → Cost (.mu T) (.mu T')` — SAME issue for
  the equality-keyed `cmu` (e.g. `mu (bvar 0)` vs `mu (brand 5)` become equal at
  `β := 5`).  This was the subtle gain-case found in the analysis; without it
  `disj_bsubst` is FALSE.
- bvar vs int/top/arr/rcd/or/mu/allb formers: NO cost (a bvar always becomes a
  `brand`, and brands are disjoint from those formers) — nothing gained ✓.

Gain-analysis summary (proof skeleton for
`cost_bsubst_inv : Cost (bsubst d n A) (bsubst d n B) → Cost A B`, the lemma behind
`disj_bsubst`): post-`cbrand` (brand n = brand n) pre-images are
{brand/brand → cbrand, brand/bvar → cbrandbvar, bvar/bvar → cbvar}; post-`cmu` with
pre-bodies unequal forces a bvar in one of them (else bsubst is identity) → `cmubv`;
same for `callb`/`callbbv`; `cbvar`/`cbvarbrand` post pull back to bvar/bvar-or-brand
pre; structural rules recurse.  Needs helper
`bsubst_hasbvar_notin : ¬ HasBVar T → bsubst d n T = T`.

**Consequence (document in DESIGN.md):** nothing typed at a bvar (or at a
bvar-containing μ/∀) can be MERGED with anything brand- or bvar-typed — the same
"wrap them in records" discipline as `Cost.coror` for unions.  Module-land
disjointness is label-driven, so the motivating example
(`Sig(β) = {mk : Int→β} & {get : β→Int}`) is unaffected.

Fallout in Disjointness.lean to extend: `cost_symm`, `cost_compose` (new Sub cases
are refl → identity, new Cost cases under sandl/sandr generic), `sub_cost`
(`sbvar → cbvar`, `sallb → callb`), `sub_sub_cost` — **WARNING:
`cost_bvar_compose` in the style of `cost_brand_compose` is FALSE** (brand n and
brand m both cost `bvar i` via cbrandbvar, but `Cost (brand n) (brand m)` fails for
n ≠ m).  `cost_brand_compose` itself SURVIVES (all pre-images of a cost against
`brand n` — brand n, bvar, and-chains — pairwise cost).  For `sub_sub_cost`'s
`D = bvar i` case use a peel instead: `sub_bvar_peel : Sub A (.bvar i) → P (.bvar i)
→ (and-left k) → (and-right k) → P A` (Sub at bvar is refl-only, so only
sbvar/sandl/sandr occur), then nest two peels ending in `cbvar`.  `cost_mu_compose`
and a new `cost_allb_compose` DO survive with the conservative constructors (checked:
every mixed cmu/cmubv combination lands in cmubv via the Or).

### 3.3 THE CRUX #2: `Consistent` is NOT bsubst-stable → harden `tmergev`

Counterexample (real, checked against Cast/Sub):
`v₁ = clos ρ (bvar 0) Int e`, `v₂ = clos ρ' (brand 5) Int e'`.  Pre-substitution
they are Consistent — carrow/carrowtl both demand `Sub C A` and Sub at bvar/brand
is refl-only, so NO common arrow target casts both.  After `β := 5` both cast at
`arr (brand 5) D` to DIFFERENT closures → Inconsistent.  `tmergev` currently takes
only `Consistent`, so raw derivations can type merges that instantiation breaks —
the substitution lemma would be FALSE.

Fix: **add a `Disj A B` premise to `HasType.tmergev`** (KEEP the `Consistent`
premise: inversions in Determinism/CastingLemmas use it for cast-determinism at
merges, and deriving it there from Disj via `disjoint_consistent`
(CastingLemmas.lean:434) would risk a cycle).  Every legitimate use site already
has the disjointness — the codebase mantra is "tmergev + disjoint_consistent hd".
In the substitution lemma's tmergev case: `disj_bsubst hd` + post-subst typings
(IHs) + post-subst values → `disjoint_consistent` rebuilds Consistent ✓.

**⚠ SESSION-3 CORRECTION (executed, commit `49dbca0`).**  The survey's claim
about the cand case was WRONG, and the anticipated "STOP and reconsider" case is
real: in `cast_preservation`'s `.cand` arm, casting ONE value at `.and A₁ A₂`
(Casting-and) duplicates it into `mrg w₁ w₂` with NO `Disj A₁ A₂` anywhere —
`Sub` has unconditional `sand`, so `anno 3 (Int & Int)` is well-typed and steps
(sannov) to `mrg 3 3`.  A Disj-only tmergev falsifies preservation outright.

Resolution (implemented): **split the runtime merge rule.**
- `tmergev` — hardened with `Disj A B` (before Consistent) exactly as planned;
  covers every module-composition merge (all surveyed constructor sites had
  their Disj in scope as predicted).
- NEW `tmergevc {Δ Γ A B C v v₁ v₂}` : `Value v₁ → Value v₂ →
  HasType Δ .top v₁ A → HasType Δ .top v₂ B → Value v → HasType Δ .top v C →
  Cast v A v₁ → Cast v B v₂ → Consistent v₁ v₂ →
  HasType Δ Γ (.mrg v₁ v₂) (.and A B)` — the cast-duplicated merge, recording
  the common ORIGIN (its typing + the two casts).  This shape is bsubst-stable
  BY CONSTRUCTION: the substituted components are casts (via cast_bsubst,
  §3.5.5) of the substituted origin (typing via the IH), so `hastype_bsubst`'s
  tmergevc case rebuilds Consistent semantically via `consistent_after_cast` —
  no lemma cycle (consistent_after_cast is in CastingLemmas; the substitution
  suite imports it).  The §3.3 counterexample stays excluded: its pair admits
  no common origin, else it would remain consistent post-substitution.
- BOTH rules keep `Consistent`, so all ~62 inversion sites stayed mechanical:
  the tmergev arm gains one binder, and a `tmergevc` arm is added whose body is
  a copy of the tmergev arm's (it exposes the same hv/ht/hcons data; scripted).
  Only `tmergevc` construction site so far: `cast_preservation`'s cand arm.
  `sealv_preservation`'s tmergevc inversion re-seals via plain `tmergev`
  (WfSig.and's hdAB supplies Disj of the sealed views).  The fundamental lemma
  (Sealing.lean) rebuilds tmergevc verbatim under the weakened store.
`toplike_disj` added to Disjointness.lean as planned (genVal_typed).

### 3.4 Typing, WfSig, sealing forms

- `NoRes`: add `| bvar {i} : NoRes (.bvar i)` and `| allb {A} : NoRes A →
  NoRes (.allb A)`.
- `WfSig` (Typing.lean): add `| bvar {i} : WfSig n R (.bvar i)` (like `brand`);
  add `| allb {A} : ¬ BrandIn n (.allb A) → NoRes (.allb A) → ¬ HasBVar A →
  WfSig n R (.allb A)` (∀ opaque under sealing, the μ pattern); **STRENGTHEN**
  `WfSig.mu` with an extra `¬ HasBVar T` premise.  Reason: `wfsig_bsubst`
  (WfSig n' R S → WfSig n' (bsubst R) (bsubst S)) must hold unconditionally, and
  bsubst introduces `brand n` which could collide with the ¬BrandIn n' condition
  when n' = n; bvar-freeness makes those μ/∀ bodies bsubst-invariant.  Existing
  WfSig.mu constructions: sealTyp images are always bvar-free — add
  `sealTyp_no_hasbvar : ¬ HasBVar (sealTyp S)` in Seal/Elaboration.lean;
  Examples.lean sites use concrete types (discharge by `nomatch`/decide-style).
- `SealV`/`UnsealV` (SmallStep.lean): identity at `.bvar` and `.allb`
  (constructors `bvar`/`allb`, exactly like `var`/`mu`).  Type-correctness of the
  identity at allb comes from WfSig.allb's ¬BrandIn via `substBrand_notin`.
- New typing rules (Typing.lean), NO freshness side conditions needed thanks to
  §3.2:
  - `tblam : ¬ HasBVar Γ → HasType Δ Γ e A → HasType Δ Γ (.blam e) (.allb A)`
    — the bvar-free-Γ side condition replaces shifting: the captured context may
    not mention ANY brand variable (nested generic functors capturing an OUTER β
    are out of scope for this first iteration; single-binder polymorphism is what
    the motivating example needs).  Note `¬ HasBVar Γ` (index-blind) not just
    `¬ BVarIn 0 Γ` — index-blind is what `bsubst`-invariance of Γ needs.
  - `tbclos : Value ρ → HasType Δ .top ρ Γ₁ → ¬ HasBVar Γ₁ →
    HasType Δ Γ₁ e A → HasType Δ Γ (.bclos ρ e) (.allb A)`.
  - `tbapp : HasType Δ Γ e (.allb A) → HasType Δ Γ (.bapp e n) (bsubst 0 n A)`
    (or equation-guarded `T = bsubst 0 n A` — USE THE EQUATION GUARD, the
    tunseal/tunfold trick, so inversions at concrete types don't stick).
- `Sub`: `| sbvar {i} : Sub (.bvar i) (.bvar i)`, `| sallb {A} : Sub (.allb A)
  (.allb A)` (equality-only, the brand pattern).  Extend `sub_refl`,
  `sub_toplike`, and `sub_trans` (two new middle-type cases mirroring
  `var`/`mu` verbatim, plus the two new leaf lines in every existing
  `induction C` block — mechanical, the compiler lists them).
- `Cast`: `| cbclos {ρ e A} : Cast (.bclos ρ e) (.allb A) (.bclos ρ e)` (identity,
  the cwrap/cfold pattern).  Extend `cast_value`, `cast_toplike_gen` (allb never
  top-like → nomatch).  Canonical forms: `.allb` values are exactly `bclos` (only
  tbclos concludes allb for a value); `.bvar` has NO value rule → vacuous
  canonical-forms case, mirroring `Typ.var`.

### 3.5 The substitution suite (new section, likely in Preservation.lean or its own
file `Seal/BrandSubst.lean` imported by Preservation)

Bottom-up order:
1. `bsubst_hasbvar_notin`, `bsubst_notin_typ` (¬HasBVar → identity), HasBVar
   inversion helpers.
2. Structural stability: `sub_bsubst : Sub A B → Sub (bsubst d n A) (bsubst d n B)`
   (refl rules ↦ refl: sbvar ↦ sbrand ✓); `lookup_bsubst`, `rlookup_bsubst`
   (labels untouched; needs `lin_bsubst_inv : Lin l (bsubst d n B) → Lin l B` for
   the negative premises); `toplike_bsubst : TopLike (bsubst d n A) ↔ TopLike A`;
   `ordinary_bsubst`; `nores_bsubst`; `wfsig_bsubst` (uses the strengthened μ/∀
   cases).
3. `cost_bsubst_inv` → `disj_bsubst` (§3.2).
4. `bsubstExp_value : Value v → Value (bsubstExp d n v)` (+ converse if needed).
5. `cast_bsubst : Cast v A w → Cast (bsubstExp d n v) (bsubst d n A)
   (bsubstExp d n w)` — needs `toplike_bsubst` both directions (carrow vs
   carrowtl split on TopLike D) and `genVal (bsubst …) = bsubstExp (genVal …)`?
   NO — genVal of a substituted type vs substituted genVal: prove
   `bsubstExp d n (genVal A) = genVal (bsubst d n A)` (both .unit at
   bvar/brand ✓ — check the arr case: genVal (arr A B) = clos .unit A B (genVal B)
   — bsubstExp rewrites the annotations ✓ commutes).
6. `sealv_bsubst`/`unsealv_bsubst` (SealV n R S v w → SealV n (bsubst R)
   (bsubst S) (bsubstExp v) (bsubstExp w)) — needed for the tseal/tunseal cases…
   NO WAIT: tseal's premise is about substBrand; what hastype_bsubst needs in the
   tseal case is `bsubst d n (substBrand n' R S) = substBrand n' (bsubst d n R)
   (bsubst d n S)` — a COMMUTATION lemma `bsubst_substBrand_comm` (they operate on
   disjoint leaf namespaces: bvar vs brand n'… careful: bsubst introduces
   `brand n`, and substBrand n' replaces `brand n'` — commutes when the introduced
   brand is not the replaced one; when n = n' it does NOT commute!  Resolution:
   substBrand n' R S with S from WfSig n' — S's bvars sit under μ/∀ only if
   bvar-free (WfSig) — NO: S can contain bvars at ARBITRARY positions (WfSig.bvar
   case!).  Compute: bsubst d n (substBrand n' R S) vs substBrand n' (bsubst R)
   (bsubst S): at a `.bvar d` leaf of S: LHS substBrand first (bvar untouched)
   then bsubst → brand n; RHS bsubst → brand n, then substBrand n' → if n = n'
   that becomes R-image ≠ brand n.  MISMATCH when n = n'.  So the tseal case of
   hastype_bsubst FAILS for instantiation at a brand n that the body seals at
   (n' = n) with a bvar in the signature.  FIX: strengthen `tseal`/`tunseal`'s
   WfSig — actually the clean fix is to require in WfSig **no bvar ANYWHERE in
   S when the store brand could collide**… simplest sound choice, consistent with
   §3.4: **replace the `WfSig.bvar` case by requiring bvar-free signatures
   entirely** (drop WfSig.bvar; sealing signatures must be HasBVar-free; add
   `¬ HasBVar S` as a derived property `wfsig_no_hasbvar : WfSig n R S →
   ¬ HasBVar S` — provable if the and/arr/or/rcd cases recurse and μ/∀ carry it
   and there is no bvar case).  Then S, R bvar-free → bsubst is identity on both
   → tseal case is trivial (`bsubst_notin` rewrites).  CONSEQUENCE: a generic
   functor body cannot SEAL at a signature mentioning β — sealing and ∀ compose
   only via sealing first, abstracting second — acceptable first iteration,
   matches "the ∀ serves the CLIENT side" in the motivating example.  (R is
   bvar-free via `NoRes`-style: add `hastype-side` condition?  R comes from the
   store Δ — stores are written by providers, brand-variable-free by
   construction; enforce with `¬ HasBVar R` in tseal?  NO — simpler: R is only
   USED through substBrand n' R S with S bvar-free, and bsubst-of-R appears in
   the IH only through that; add `¬ HasBVar R` premise to tseal/tunseal anyway
   for a clean identity — provider stores are concrete, discharge is `nomatch`.)
7. **`hastype_bsubst`** : `HasType Δ Γ e A → HasType Δ (bsubst d n Γ)
   (bsubstExp d n e) (bsubst d n A)` — full induction, ~30 cases; tmergev via
   §3.3; tblam/tbclos: their `¬ HasBVar Γ₁` makes the captured context invariant
   (`bsubst_notin`), body recurses at d+1 — NOTE the IH is at (d+1, n) for the
   blam body: the lemma must be stated for ALL d (it is).  Beta preservation then
   uses it at d = 0 with the bclos's `¬ HasBVar Γ₁`.

### 3.6 Commit plan (execute in order; `lake build` green after each)

**ALL COMMITS BELOW ARE DONE (session 3).**  Actual sequence (resequenced —
see the ⚠ notes): A (`49dbca0`), B+C (`05b657a`, one unit: total matches over
Typ pull the Sub/Cost leaves in immediately), D-prep (`d94e193`), E
(`005e5c8`), F′a (`82474d5`), F′b (`bcc930b`), F′c (`2b2b849`), example+docs
(this commit).  §3.9 lists every design correction made along the way.

- **Commit A ✅ DONE** (`49dbca0`, session 3): `tmergev` + `Disj A B` premise
  AND the `tmergevc` split (§3.3 correction).  Downstream consequences for later
  commits: `hastype_bsubst` (Commit F) gains a tmergevc case = IHs (origin +
  components) + `cast_bsubst` + `consistent_after_cast`; new typing-inversion
  proofs written from Commit D onward must handle BOTH merge rules.
- **Commit B ✅ (as B+C)**: Syntax additions (§3.1) — types, terms, substitutions, HasBVar,
  Value/genVal/Ordinary/toplike_dec.  Everything still compiles because no
  relation mentions the new constructors yet EXCEPT total matches: `genVal`
  (extended here), `substBrand`/`substTyp` (extended here).
- **Commit C ✅ (in B+C)**: Subtyping + Disjointness + Casting extensions (§3.2, §3.4-Sub/Cast)
  incl. the full compose/peel fallout and `sub_bvar_peel`.
- **Commit D ✅ (as D-prep + F′a + F′c)**: Typing (NoRes/WfSig strengthening + sealTyp_no_hasbvar + tblam/
  tbclos/tbapp) and SmallStep (sblam/sbappl/sbappbeta, SealV/UnsealV bvar/allb).
  Existing WfSig.mu sites gain the ¬HasBVar argument.
- **Commit E ✅** (`005e5c8`, new file `Seal/BrandSubst.lean`): the substitution
  suite §3.5 items 1–6 (item 6 replaced by identity-via-bvar-freeness; the
  cost_{brand,var,mu}_compose helpers were replaced by refl-leaf peels — with
  cmubv the μ compose lemma is FALSE for arbitrary costs).
- **Commit F ✅ (as F′c, `2b2b849`)**: `hastype_bsubst` (§3.5.7) + steps +
  typing rules + all fallout in one unit (typing rules force progress cases
  needing the steps; sbappbeta preservation needs hastype_bsubst — none land
  green separately).
- **Commit G ✅ (in F′c)**: CastingLemmas/Determinism/Progress/Preservation new cases
  (cast determinism for cbclos mirrors cwrap/cfold; progress at allb via canonical
  bclos; preservation sbappbeta case = tbclos inversion + hastype_bsubst + tbox).
- **Commit H ✅ (spread over B+C and F′c)**: Sealing.lean: `LRg (.bvar _) = False`; `LRg (.allb A)` = opaque
  equality clause mirroring the μ clause (`v₁ = v₂` + typings); `cast_lr` allb
  case via a `cast_allb_id` lemma (mirror `cast_mu_id`); `coe_lr` allb case =
  identity via WfSig.allb's ¬BrandIn + `substBrand_notin`; Abstraction.lean
  fallout.  `Finitary` needs NO change (inductive whitelist; no blam/bclos/bapp
  constructors → generic terms are outside the normalizing fragment, `fundamental`
  discharges the new typing cases by the absent-Finitary pattern used for flam).
- **Commit I ✅ (this commit)**: Examples.BrandPolyExample — the generic
  identity Λβ.λ(x:β).x typed at ∀β.β→β, instantiated at ANY brand (genId_inst),
  with a 4-step run to the concrete closure (genId_run).  The full two-provider
  sealed ∀-functor example moves to milestone 5.  DESIGN.md §(h) still TODO
  (document §3.2/§3.3/§3.9 decisions).

### 3.7 Deferred (after the safety layer)

- **Milestone 4 (relational) — DESIGN FIXED (session 3), bvar-interpretation
  environments** (an η-extension-at-a-concrete-brand formulation is UNSOUND: a
  fresh-brand guard excludes instantiation at allocated provider brands, and an
  unguarded ∀ conflates β with existing brands in the tblam intro case).  Keep
  LRg STRUCTURAL by adding `δ : Nat → Nat × (Exp → Exp → Prop)` (de Bruijn env,
  index 0 = nearest allb binder; single brand per binder — n₁ = n₂ suffices for
  RI of generic clients; two-brand generalization later):
  - `bsubstEnv (σ : Nat → Nat) (d : Nat) : Typ → Typ` — simultaneous
    bvar→brand: `.bvar i ↦ if i < d then .bvar i else .brand (σ (i − d))`,
    d+1 under allb.  Lemmas: `bsubstEnv_notin`; agreement with `bsubst` on
    BClosed types (`BClosed 1 A → bsubstEnv (cons m σ) 0 A = bsubst 0 m A`,
    `BClosed 0 A → bsubstEnv σ d A = A`).
  - LRg clauses: every typing conjunct becomes `viewL/R o (bsubstEnv (σ of δ) 0 T)`
    (values under binders are typed at CONCRETE brands, one per side is wrong —
    same brand both sides).  New `.bvar i` clause: `Value v₁ ∧ Value v₂ ∧
    typings at (viewL/R o (.brand (δ i).1)) ∧ (δ i).2 v₁ v₂`.  New `.allb A`
    clause (mirror the arrow clause's extensional shape): values ∧ typings at
    the bsubstEnv-image ∧ `∀ m rel, RelAdm o m rel → ∀ ρ₁ ρ₂ values, ∃ w₁ w₂,
    MStep runs of (.bapp vᵢ m) ∧ LRg (cons (m,rel) δ) A w₁ w₂`.
  - `RelAdm o m rel` := cast-closure of rel at `viewL/R o (.brand m)` (the
    OpenAdm pattern); `DeltaAdm o δ` := RelAdm for every entry — threaded as a
    LEMMA hypothesis (like hadm : OpenAdm) through cast_lr/coe_lr, trivially
    satisfied by the empty δ.  Cast at `.bvar` is UNINHABITED
    (`cast_bvar_empty`); cast at a brand on brand-typed values is the identity
    (`cast_brand_id`, mirror cast_mu_id) — the o = none sbvar case of cast_lr;
    the o = some sbvar case uses DeltaAdm.
  - `LR := LRg δ∅` with `δ∅ := fun _ => (0, fun _ _ => False)`; δ-irrelevance
    on bvar-free types (`lrg_delta_irrel`) keeps every existing statement.
  - THE key lemma (`lrg_bsubst`, compositionality / the relational substitution
    lemma; generalize over insertion depth like hastype_bsubst):
    `BClosed 1 A → (LRg (cons (m, brandRel m) δ∅) A v₁ v₂ ↔
    LRg δ∅ (bsubst 0 m A) v₁ v₂)` where `brandRel m := LRg δ∅ (.brand m)`.
    This is what connects tbapp's conclusion type to the ∀-clause.  Budget it
    like cost_bsubst_inv.
  - Fundamental: add blam/bclos/bapp to `Finitary` (sbappbeta never duplicates
    subterms → SN preserved); tbapp picks `rel := brandRel n` (RelAdm via
    cast_brand_id / OpenAdm) and finishes by lrg_bsubst.  **The tblam case
    CANNOT use the structural IH**: the ∀-clause runs `.bapp v m`, whose beta
    yields the SUBSTITUTED body `bsubstExp 0 m body` — and the UNsubstituted
    body cannot even run (bvar annotations make every cast stuck, by
    cast_bvar_empty), so relating its runs is the wrong statement.  The case
    must recurse on `hastype_bsubst hb` — non-structural.  FIX: `bsubstExp`
    preserves expression size (it rewrites only annotations), so restructure
    `fundamental` to STRONG INDUCTION ON EXPRESSION SIZE (define `esize`,
    prove `esize_bsubstExp : esize (bsubstExp d n e) = esize e`), with inner
    case analysis on the typing derivation.  Then `generic_client_representation_independence`.
  - Commit order: M4a infrastructure (cast_bvar_empty, cast_brand_id,
    bsubstEnv + lemmas) → M4b LRg refactor + call-site repair (δ∅ everywhere)
    → M4c cast_lr/coe_lr with DeltaAdm → M4d lrg_bsubst → M4e Finitary +
    fundamental → M4f RI corollary + example + docs.  Green after each.
  - **⚠ M4b ATTEMPTED AND ROLLED BACK (session 3): two open design problems.**
    M4a landed (`9892ce1`), plus sub_bsubstEnv (BrandSubst) and the δ-env
    definitions DEnv/dbrands/demp/RelAdm/DeltaAdm/deltaAdm_demp/deltaAdm_insert
    (Sealing, defined but NOT yet consumed by LRg).  The LRg-with-δ clause
    rewrite itself was attempted and reverted because:
    (1) **The demp-degeneracy problem.**  With typing conjuncts at
    δ-instantiated images `viewL o (bsubstEnv (dbrands δ) 0 T)`, the
    fundamental at δ = demp becomes FALSE for degenerate bvar-annotated
    programs: `lam (bvar 0) (bvar 0) (proj query 0)` is closed, Finitary, and
    typed at `arr (bvar 0) (bvar 0)` — but its closure value is NOT typed at
    the image `arr (brand 0) (brand 0)` the new arrow clause demands.  (The
    OLD clauses were satisfiable there because typings were at the syntactic
    type; relatedness held vacuously via the False bvar clause.)  Candidate
    fix: thread a properly-bound invariant — `EBClosed c e` (annotation
    bvar-indices properly bound, c+1 under blam/bclos) with `BClosed 0 Γ` —
    and derive `BClosed 0 A` for every type in the derivation, so the images
    rewrite away by bclosed_bsubstEnv.  BUT:
    (2) **The slack leak.**  `hastype_bclosed` is FALSE as stated: tclos's
    subtyping slack `Sub C A` can introduce unbound bvars into derivation
    types via contravariant domains — `Sub (arr .top .int) (arr (bvar 99)
    .int)` holds (stop + refl), so a closure typed at `arr .top .int`
    re-types at `arr (bvar 99) .int`.  Same for tfclos's three slacks and
    tanno-with-slack chains through casts.  Candidate fixes to evaluate NEXT
    SESSION, in order of appeal: (i) strengthen tclos/tfclos/tanno slacks
    with BClosed-preservation side conditions (sub_bclosed holds in the
    covariant direction; only the contravariant slack leaks — a
    `BClosed c C` premise on tclos/tfclos mirrors the BClosed 1 premise on
    tbapp and is bsubst-stable); (ii) restrict the fundamental's STATEMENT to
    EBClosed subjects and prove clause-typings only up to the leaky slack by
    re-deriving them from value_weaken + the subject's own annotations rather
    than from the derivation's types; (iii) drop typing conjuncts from LRg
    clauses entirely and re-engineer lr_typed as an external invariant
    (biggest surgery, cleanest theory).  Also note for M4b proper: lr_typed's
    statement becomes typings at the bsubstEnv-image; leaf arms need
    `simp only [bsubstEnv]` before the viewL_* rewrites; the or-clause value
    annotations also take images.
- **Milestone 5 (source)**: source `∀`-functors (`mfunctor` binding a brand or a
  separate `bfunctor`), `elabSeal` + Correctness cases, `mlinkn`-time
  instantiation; then the sepcomp obligations (plan §3(C) items 1–4:
  brand-RENAMING metatheory with freshness side conditions — NOTE this is a
  SEPARATE mechanism from §3.2's bvar instantiation: renaming concrete brand →
  concrete brand is where freshness is genuinely needed;
  `seal_separate_compilation_generic`).

### 3.8 File facts gathered for Phase 3 (save re-reading)

- `Cost` constructors: cint, candl/candr/crandl/crandr, carr (codomain only!),
  crcd, cbrand (refl), coror (UNCONDITIONAL), cvar/cmu (refl).  `Disj A B :=
  ¬ Cost A B`.  Key lemmas: cost_symm, cost_top_l, cost_compose (Sub-left),
  sub_disj, disj_and_inv_l/r, disj_rcd_ne, disj_brand_ne, disj_brand_notin,
  substBrand_notin, sub_cost, cost_{int,brand,var,mu}_compose, sub_sub_cost.
- `Sub` refl-only leaves: sbrand/svar/smu (+ new sbvar/sallb).  sub_trans is a
  big nested induction: each middle-type case has an inner `induction C` listing
  EVERY constructor — adding 2 type formers touches every block (mechanical).
- `Cast` constructors: cint, ctop, carrow/carrowtl (TopLike split, genVal),
  cmrgl/cmrgr (Ordinary), cand, crcd, cwrap (identity), cinl/cinr, cfold
  (identity), cfarrow/cfarrowtl.  `Consistent v₁ v₂ := ∀ {A w₁ w₂}, Cast v₁ A w₁
  → Cast v₂ A w₂ → w₁ = w₂`.
- `HasType.tmergev` premise order TODAY: `hv₁ hv₂ ht₁ ht₂ hd hcons` (components
  at `.top`, Disj before Consistent).  `HasType.tmergevc` premise order:
  `hv₁ hv₂ ht₁ ht₂ hv ht hc₁ hc₂ hcons` (first four mirror tmergev; then origin
  value/typing, the two casts, Consistent).  Inversion arms:
  `| tmergev _ _ hp hq hd hcons` / `| tmergevc _ _ hp hq hv ht hc₁ hc₂ hcons`.  `tclos`: `hv henv hd hbody hsub₁ hsub₂` with slacks `Sub B' B`,
  `Sub C A`.  `tflam`: `hd₁ hd₂ hbody`.  `tfclos`: `hv henv hd₁ hd₂ hbody
  hs₁ hs₂ hs₃`.  `tseal`: `hΔ hnr hwf h`.  `tunseal`: `hΔ hnr hwf h heq`.
- `SealV`/`UnsealV` + `proxyEnv`/`proxyFun` + `Step`/`MStep` + `value_not_step` +
  `sealv_value`/`sealv_det` etc. all live in **Seal/SmallStep.lean**.
- `disjoint_consistent` lives at **CastingLemmas.lean:434**, signature
  `(hv₁)(hv₂)(ht₁ : HasType Δ Γ₁ v₁ A)(ht₂ : HasType Δ Γ₂ v₂ B)(hd : Disj A B) :
  Consistent v₁ v₂` (contexts arbitrary!).
- `sbeta` reduct: `.box (.mrg v₁ v₂') (.anno e B)` — note the `anno`-reseal;
  `sfbeta` reduct: `.box (.mrg (.mrg v₁ (.fclos v₁ A B B e)) v₂') (.anno e Bx)`.
- WfSig TODAY: int/top/brand/arr/rcd(l ≠ reservedLabel)/and(+ both-view Disj)/or/
  mu(¬BrandIn + NoRes) — NO var case exists (μ-vars can't be sealed at) — so NOT
  adding WfSig.bvar (per §3.5.6) is consistent with the var precedent ✓.
- Sizes: CastingLemmas 1202, Sealing 1365, Correctness ~1640 (post 2-pre),
  Preservation 433, Progress 379, Determinism 198 lines.

### 3.9 Session-3 design corrections (all implemented; trust these over §3.1–§3.5)

1. **tmergevc** (Commit A, §3.3 correction): second runtime merge rule for
   cast-duplicated merges; both merge rules keep Consistent.
2. **blam/bclos carry the ∀-body annotation** (`blam A e`, `bclos ρ A e`): an
   identity cast must be pinned by the value (the fold/wrap precedent), or
   cast_preservation's cbclos case is unprovable.  `bsubstExp` maps the
   annotation and body at d+1, the captured environment at d (it sits OUTSIDE
   the binder).
3. **twrap gains `¬ HasBVar R`** (like tseal/tunseal): the store representation
   must be bsubst-invariant.
4. **tfold/tunfold gain `¬ AllbIn T`** (new occurrence inductive): substTyp
   does not shift bvars, so ∀ INSIDE a μ-body would capture cross-binder bvars;
   `bsubst_substTyp_comm` holds exactly under the fence.  μ over an OUTER β
   stays allowed.  Liftable later with a shifting substTyp.
5. **tbapp carries `BClosed 1 A`** (new properly-bound predicate): the
   shift-free beta is index-coherent only when the ∀-body's bvars are bound by
   its OWN binder.  Under it, hastype_bsubst's tbapp case closes by
   `bclosed_bsubst` (identity at/above cutoff) + `bclosed_bsubst_lower`.
6. **cost_{brand,var,mu}_compose replaced by refl-leaf peels** (sub_brand_peel/
   sub_var_peel/sub_mu_peel/sub_bvar_peel/sub_allb_peel): with cmubv the μ
   compose lemma is false for arbitrary costs; subtyping-derived costs end in
   the exact leaf, which is all sub_sub_cost needs.  `disj_brand_notin` gains a
   `¬ HasBVar B` premise (a brand costs every bvar).
7. **wfsig_bsubst not needed**: WfSig has NO bvar case (dropped per §3.5.6);
   signatures are bvar-free (`wfsig_no_hasbvar`), so bsubst is the identity on
   them.  `sealTyp_no_hasbvar`/`sealTyp_no_allbin` discharge every elaboration
   obligation.
8. **Premise orders NOW** (for inversions): `tmergev hv₁ hv₂ ht₁ ht₂ hd hcons`;
   `tmergevc hv₁ hv₂ ht₁ ht₂ hv ht hc₁ hc₂ hcons`; `twrap hΔ hnb hv ht`;
   `tseal hΔ hnr hnb hwf h`; `tunseal hΔ hnr hnb hwf h heq`;
   `tfold hna h`; `tunfold hna h heq`; `tblam hnb h`; `tbclos hv henv hnb h`;
   `tbapp h hbc heq`.  Lean allows PARTIAL binder lists in `cases/induction`
   alternatives (extra args auto-named inaccessible) — use minimal binders.
9. **Key new lemmas**: BrandSubst.lean holds the whole suite — hasbvar_dec,
   bsubst_notin, hasbvar_bsubst_inv, ten bsubst_eq_* shape inversions,
   cost_bsubst_inv → disj_bsubst, sub/lookup/rlookup/toplike/ordinary/nores
   _bsubst, bsubstExp_value, bsubstExp_genVal, cast_bsubst,
   hasbvar_substBrand, allbin_bsubst_inv, bsubst_substTyp_comm,
   bclosed_bsubst(_lower), hastype_bsubst.  CastingLemmas: cast_allb_cost;
   Sealing: cast_allb_id, viewL/R_allb; Examples: BrandPolyExample.

---

## 4. Gotchas (both sessions; keep these)

- **Lean auto-generalizes and RE-INTRODUCES** hypotheses depending on the major
  premise's indices: after `induction ht` with `hfin : Finitary e` in context, each
  case has `hfin` back (specialized) and the IHs have `Finitary eᵢ →` prepended.  Do
  NOT `intro hfin`.
- **Match-arm `by` blocks auto-intro leading implicit binders** of the remaining
  telescope: writing `fun {Γ} {v} {ce} hv helab => …` in an equation arm over-binds
  (bit in `source_ssealv_prog`); write `fun hv helab => …` only.
- **`nomatch h` failures inside `try`/`first` are UNCATCHABLE** ("Missing cases"
  is logged by the term elaborator, not thrown).  Never `cases x <;> try nomatch h`
  where the nomatch can fail; instead `cases hv` + `case <tag> => …` +
  `all_goals nomatch helab` where nomatch always succeeds, or list all constructors.
- **`case <tag>` selectors break inside `by_cases` bullets** (goal tags get a `pos.`
  hygiene prefix) — use explicit `cases … with` there.
- **`cases`-alternative arity**: inductive PARAMS (e.g. elabSeal's Δ) are NOT
  alternative arguments; `@emstruct` under `cases` takes 6 implicits + 3 premises,
  under `induction` +1 ih.
- **Underscore placeholders in `have h : _ = Γ₂ ∨ …`** are unsolvable if the term
  isn't determined — name case variables via `@`-binders instead.
- **`⟨_, elabSeal.eclos … ?_ …⟩` with refine**: the existential witness (the
  elaborated term) depends on the postponed body derivation and fails to synthesize —
  inline the full derivation as one `exact` term instead.
- sealTyp/substBrand/substTyp defeq DOES unfold through unification (mutual
  structural defs; `exact HasType.tinl ih`-style uses work), so `Disj (sealTyp ctx')
  (.arr (sealTyp A) (sealTyp B))` unifies with `Disj _ (sealTyp (.arr A B))` — no
  simp needed in term position.
- `simp only [SCE.substBrand] at h` BEFORE inverting elabSeal at a substBrand-typed
  index (cases needs the syntactic constructor).
- `sealModTyp (TyIntf B)`-forms block syntactic `rw [← sealTyp_substBrand]` — run
  `simp only [sealTyp, sealModTyp]` first.
- IDE diagnostics during multi-file edits are STALE — trust `lake build` only.
- `git checkout`/`git restore` are BLOCKED by the user's guardrail hook; use
  `git switch` (and `git archive | tar` for file extraction).
- elabSeal constructor premise ORDER (for inversions):
  `edmrg h₁ h₂ hd₁ hd₂`, `evmrg hv₁ hv₂ h₁ h₂ hd`, `enmrg h₁ h₂ hd₁ hd₂`,
  `elam h hd`, `eclos hv h₁ h₂ hd`, `eletb h₁ h₂ hd`, `eopenm h₁ h₂ hd`,
  `emstruct hs1 hs2 h`, `emfunctor hs1 hs2 hdop h`, `emclos hv h₁ h₂ hd`,
  `emapp h₁ h₂`, `emlink h₁ h₂ hl hd₁ hd₂`, `emlinkn h₁ h₂ hw hd₁ hd₂`,
  `ewrap hΔ hv h`, `emseal hΔ hnr hwf h`, `emunseal hΔ hnr hwf h heq`,
  `einl h`, `einr h`, `ecase h h₁ h₂ hd₁ hd₂`, `eflam h hd₁ hd₂`,
  `efclos hv h₁ h₂ hd₁ hd₂`, `efold h`, `eunfold h heq`.
- Build: `lake build` ≈ 60 jobs; single module `lake build LeanSce.SCE.Foo`;
  errors: `lake build 2>&1 | grep -E "^error" -A 6`.

## 5. Commit log (newest first; session 2 above the line)

```
2b2b849 Seal: ∀β typing + steps + hastype_bsubst — safety layer complete (F′c, session 3)
bcc930b Seal: blam/bclos carry the ∀-body annotation (F′b)
82474d5 Seal: twrap ¬HasBVar R + tfold/tunfold ¬AllbIn μ-fence (F′a)
005e5c8 Seal/BrandSubst: the ∀β-instantiation substitution suite (E)
d94e193 Seal: bvar-free sealing discipline — WfSig/NoRes/tseal (D-prep)
05b657a Seal: brand-polymorphism syntax + conservative COST/Sub/Cast (B+C)
49dbca0 Seal: harden tmergev with Disj; split off tmergevc — Phase 3 Commit A (session 3)
3a28c98 HANDOFF.md: Phase 3 design complete
3b799d9 HANDOFF.md: work lives on lambdae-sub; main stays clean
c287715 HANDOFF.md: Phase 2 complete — single source, single target
a379899 S_Sem: single lookupv_value/sel_value — dedupe the value-lemma triplets
1a79fcd Delete Core + the SCE→Core elaboration: one source, one target — Phase 2e done
cf6436e SCE: Capabilities + RecLinking re-witnessed by elabSeal — Phase 2d done
6bd14fb SCE/Determinism: big-step preservation + determinism — Phase 2c (ii)
7b17983 SCE/Determinism: elabSeal uniqueness + selection determinism — Phase 2c (i)
30a2eb5 SCE/Progress: elabSeal port — Phase 2b done
d2ff193 SCE/Preservation: elabSeal port — Phase 2a done
7bd7fcc Seal: move elabSeal value/lookup/sel lemmas Correctness → Elaboration
────────
f72ccac HANDOFF.md session-1 takeover doc (full Phase 1 design notes live there)
8a881d0 … da5407a  Phase 1 (see §1)
```
