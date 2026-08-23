import LeanSce.Seal.Sealing

-- Representation independence for λE^≤ with brands.
--
-- The picture: a sealed unit is `seal n R S p` — the implementation `p`, typed at the
-- representation view S[n:=R] of its signature, coerced to the abstract view S.  Two
-- such units with representations R₁, R₂ are *related as implementations* when they
-- stand in `LRg (some (n, R₁, R₂)) S`: componentwise on the signature, extensionally at
-- arrows, and at the abstract type by an arbitrary (admissible) relation η n on the raw
-- representations.  The theorem `coe_lr` says the sealing coercion carries this relation
-- to the client-facing one, `LR S` (every brand abstract), and its converse for
-- unsealing — the two directions are mutually inductive because a proxy at an arrow
-- unseals its argument and seals its result.  Representation independence is then the
-- sealing corollary applied to the coerced units: every client typed against S with
-- α_n opaque computes the same integer against either sealed unit.
namespace Seal

variable {Δ₁ Δ₂ : BrandStore} {η : Nat → Exp → Exp → Prop}

-- Everything the two sides of an open brand must agree on.
structure OpenBrand (Δ₁ Δ₂ : BrandStore) (η : Nat → Exp → Exp → Prop)
    (n : Nat) (R₁ R₂ : Typ) : Prop where
  st₁ : Δ₁ n = some R₁
  st₂ : Δ₂ n = some R₂
  nores₁ : NoRes R₁
  nores₂ : NoRes R₂
  nobvar₁ : ¬ HasBVar R₁
  nobvar₂ : ¬ HasBVar R₂
  ntl₁ : ¬ TopLike R₁
  ntl₂ : ¬ TopLike R₂
  cast_closed : ∀ w₁ w₂, η n w₁ w₂ → ∀ w₁' w₂', Cast w₁ R₁ w₁' → Cast w₂ R₂ w₂' → η n w₁' w₂'

theorem OpenBrand.adm {n : Nat} {R₁ R₂ : Typ} (hb : OpenBrand Δ₁ Δ₂ η n R₁ R₂)
    : OpenAdm η (some (n, R₁, R₂)) := by
  intro m S₁ S₂ h
  cases h
  exact ⟨hb.ntl₁, hb.ntl₂, hb.cast_closed⟩

-- ── MStep toolkit for the coercion forms ─────────────────────────────────────────────

theorem mstep_seal {v e e' : Exp} {n : Nat} {R S : Typ} (hv : Value v) (h : MStep v e e')
    : MStep v (.seal n R S e) (.seal n R S e') := by
  induction h with
  | refl => exact MStep.refl
  | step hs _ ih => exact MStep.step (Step.sseal hv hs) ih

theorem mstep_unseal {v e e' : Exp} {n : Nat} {R S : Typ} (hv : Value v) (h : MStep v e e')
    : MStep v (.unseal n R S e) (.unseal n R S e') := by
  induction h with
  | refl => exact MStep.refl
  | step hs _ ih => exact MStep.step (Step.sunseal hv hs) ih

-- Under the proxy's extended environment, `proxyFun` evaluates to the stored closure and
-- `?.0` to the argument.
theorem proxyFun_run {c u : Exp} (hc : Value c) (hu : Value u)
    : MStep (.mrg (proxyEnv c) u) proxyFun c := by
  have henv : Value (.mrg (proxyEnv c) u) :=
    Value.vmrg (Value.vmrg Value.vunit (Value.vrcd hc)) hu
  refine MStep.step (Step.srproj henv (Step.sproj henv (Step.squery henv))) ?_
  refine MStep.step (Step.srproj henv (Step.sprojv henv henv (LookupV.lvsucc LookupV.lvzero))) ?_
  exact MStep.step (Step.srprojv henv (Value.vrcd hc) RLookupV.rvlzero) MStep.refl

theorem proxyArg_run {c u : Exp} (hc : Value c) (hu : Value u)
    : MStep (.mrg (proxyEnv c) u) (.proj .query 0) u := by
  have henv : Value (.mrg (proxyEnv c) u) :=
    Value.vmrg (Value.vmrg Value.vunit (Value.vrcd hc)) hu
  refine MStep.step (Step.sproj henv (Step.squery henv)) ?_
  exact MStep.step (Step.sprojv henv henv LookupV.lvzero) MStep.refl

-- A complete run of a sealing proxy: beta (cast the argument at A), unseal it, apply the
-- stored closure, seal the result, reseal at B (beta's result annotation), return.
theorem seal_proxy_run {ρ c u u' x y z z' : Exp} {n : Nat} {R A B : Typ}
    (hρ : Value ρ) (hc : Value c) (hu : Value u)
    (hcu : Cast u A u') (hx : UnsealV n R A u' x)
    (hy : MStep (.mrg (proxyEnv c) u') (.app c x) y) (hvy : Value y)
    (hz : SealV n R B y z) (hz' : Cast z B z')
    : MStep ρ (.app (.clos (proxyEnv c) A B
        (.seal n R B (.app proxyFun (.unseal n R A (.proj .query 0))))) u) z' := by
  have hvu' : Value u' := cast_value hu hcu
  have hvx : Value x := unsealv_value hvu' hx
  have hvz : Value z := sealv_value hvy hz
  have henv : Value (.mrg (proxyEnv c) u') :=
    Value.vmrg (Value.vmrg Value.vunit (Value.vrcd hc)) hvu'
  refine MStep.step (Step.sbeta hρ (Value.vmrg Value.vunit (Value.vrcd hc)) hu hcu) ?_
  -- body run under the extended environment
  have hbody : MStep (.mrg (proxyEnv c) u')
      (.seal n R B (.app proxyFun (.unseal n R A (.proj .query 0)))) z := by
    refine mstep_trans (mstep_seal henv (mstep_appl henv (proxyFun_run hc hvu'))) ?_
    refine mstep_trans (mstep_seal henv (mstep_appr henv hc
      (mstep_unseal henv (proxyArg_run hc hvu')))) ?_
    refine mstep_trans (mstep_seal henv (mstep_appr henv hc
      (mstep_one (Step.sunsealv henv hvu' hx)))) ?_
    refine mstep_trans (mstep_seal henv hy) ?_
    exact mstep_one (Step.ssealv henv hvy hz)
  refine mstep_trans (mstep_boxr hρ henv (mstep_anno henv hbody)) ?_
  refine MStep.step (Step.sboxr hρ henv (Step.sannov henv hvz hz')) ?_
  exact mstep_one (Step.sboxv hρ henv (cast_value hvz hz'))

-- The mirror image for an unsealing proxy.
theorem unseal_proxy_run {ρ c u u' x y z z' : Exp} {n : Nat} {R A B : Typ}
    (hρ : Value ρ) (hc : Value c) (hu : Value u)
    (hcu : Cast u (substBrand n R A) u') (hx : SealV n R A u' x)
    (hy : MStep (.mrg (proxyEnv c) u') (.app c x) y) (hvy : Value y)
    (hz : UnsealV n R B y z) (hz' : Cast z (substBrand n R B) z')
    : MStep ρ (.app (.clos (proxyEnv c) (substBrand n R A) (substBrand n R B)
        (.unseal n R B (.app proxyFun (.seal n R A (.proj .query 0))))) u) z' := by
  have hvu' : Value u' := cast_value hu hcu
  have hvx : Value x := sealv_value hvu' hx
  have hvz : Value z := unsealv_value hvy hz
  have henv : Value (.mrg (proxyEnv c) u') :=
    Value.vmrg (Value.vmrg Value.vunit (Value.vrcd hc)) hvu'
  refine MStep.step (Step.sbeta hρ (Value.vmrg Value.vunit (Value.vrcd hc)) hu hcu) ?_
  have hbody : MStep (.mrg (proxyEnv c) u')
      (.unseal n R B (.app proxyFun (.seal n R A (.proj .query 0)))) z := by
    refine mstep_trans (mstep_unseal henv (mstep_appl henv (proxyFun_run hc hvu'))) ?_
    refine mstep_trans (mstep_unseal henv (mstep_appr henv hc
      (mstep_seal henv (proxyArg_run hc hvu')))) ?_
    refine mstep_trans (mstep_unseal henv (mstep_appr henv hc
      (mstep_one (Step.ssealv henv hvu' hx)))) ?_
    refine mstep_trans (mstep_unseal henv hy) ?_
    exact mstep_one (Step.sunsealv henv hvy hz)
  refine mstep_trans (mstep_boxr hρ henv (mstep_anno henv hbody)) ?_
  refine MStep.step (Step.sboxr hρ henv (Step.sannov henv hvz hz')) ?_
  exact mstep_one (Step.sboxv hρ henv (cast_value hvz hz'))

-- ── Open/abstract agreement away from the open brand ─────────────────────────────────

-- On a type mentioning neither the open brand nor any brand variable, the open and
-- client relations coincide: substBrand is the identity on every clause annotation, the
-- RawRel branch is unreachable (m ≠ n), and — the ∀-clause — a brand-variable-free
-- ∀-body is invariant under instantiation (bsubst_notin), so the instantiation-closure
-- clause recurses at the body itself.  coe_lr's ∀-arm is the consumer.
theorem lrg_notin_iff {n : Nat} {R₁ R₂ : Typ} : {T : Typ} → ¬ BrandIn n T → ¬ HasBVar T
    → (v₁ v₂ : Exp) → (LRg Δ₁ Δ₂ η (some (n, R₁, R₂)) T v₁ v₂ ↔ LR Δ₁ Δ₂ η T v₁ v₂)
  | .int, _, _, v₁, v₂ => by simp only [LR, LRg]
  | .top, _, _, v₁, v₂ => by simp only [LR, LRg]
  | .brand m, hnin, _, v₁, v₂ => by
    have hm : m ≠ n := fun h => hnin (h ▸ BrandIn.self)
    simp only [LR, LRg, hm, if_false]
  | .var _, _, _, v₁, v₂ => by simp only [LR, LRg]
  | .bvar _, _, _, v₁, v₂ => by simp only [LR, LRg]
  | .arr A B, hnin, hnb, v₁, v₂ => by
    simp only [LR, LRg, viewL_some, viewR_some, viewL_none, viewR_none,
      substBrand_notin hnin,
      lrg_notin_iff (fun h => hnin (BrandIn.arrl h)) (fun h => hnb (HasBVar.arrl h)),
      lrg_notin_iff (fun h => hnin (BrandIn.arrr h)) (fun h => hnb (HasBVar.arrr h))]
  | .and A B, hnin, hnb, v₁, v₂ => by
    simp only [LR, LRg, viewL_some, viewR_some, viewL_none, viewR_none,
      substBrand_notin hnin,
      lrg_notin_iff (fun h => hnin (BrandIn.andl h)) (fun h => hnb (HasBVar.andl h)),
      lrg_notin_iff (fun h => hnin (BrandIn.andr h)) (fun h => hnb (HasBVar.andr h))]
  | .rcd l A, hnin, hnb, v₁, v₂ => by
    simp only [LR, LRg,
      lrg_notin_iff (fun h => hnin (BrandIn.rcd h)) (fun h => hnb (HasBVar.rcd h))]
  | .or A B, hnin, hnb, v₁, v₂ => by
    simp only [LR, LRg, viewL_some, viewR_some, viewL_none, viewR_none,
      substBrand_notin (fun h => hnin (BrandIn.orl h)),
      substBrand_notin (fun h => hnin (BrandIn.orr h)),
      lrg_notin_iff (fun h => hnin (BrandIn.orl h)) (fun h => hnb (HasBVar.orl h)),
      lrg_notin_iff (fun h => hnin (BrandIn.orr h)) (fun h => hnb (HasBVar.orr h))]
  | .mu T, hnin, _, v₁, v₂ => by
    simp only [LR, LRg, viewL_some, viewR_some, viewL_none, viewR_none,
      substBrand_notin hnin]
  | .allb A, hnin, hnb, v₁, v₂ => by
    have hnbA : ¬ HasBVar A := fun h => hnb (HasBVar.allb h)
    simp only [LR, LRg, viewL_some, viewR_some, viewL_none, viewR_none,
      substBrand_notin hnin, bsubst_notin hnbA,
      lrg_notin_iff (fun h => hnin (BrandIn.allb h)) hnbA]

-- ── The coercions respect the relations ──────────────────────────────────────────────

-- Sealing carries implementation-relatedness (brand n open) to client-relatedness
-- (brand n abstract); unsealing carries it back.  Mutual induction on the signature.
theorem coe_lr {n : Nat} {R₁ R₂ : Typ} (hb : OpenBrand Δ₁ Δ₂ η n R₁ R₂)
    : (S : Typ) → WfSig n R₁ S → WfSig n R₂ S →
      (∀ {v₁ v₂ w₁ w₂ : Exp}, LRg Δ₁ Δ₂ η (some (n, R₁, R₂)) S v₁ v₂
        → SealV n R₁ S v₁ w₁ → SealV n R₂ S v₂ w₂ → LR Δ₁ Δ₂ η S w₁ w₂) ∧
      (∀ {v₁ v₂ w₁ w₂ : Exp}, LR Δ₁ Δ₂ η S v₁ v₂
        → UnsealV n R₁ S v₁ w₁ → UnsealV n R₂ S v₂ w₂ → LRg Δ₁ Δ₂ η (some (n, R₁, R₂)) S w₁ w₂)
  | .or A B, hwf₁, hwf₂ => by
    cases hwf₁ with
    | or hwfA₁ hwfB₁ =>
      cases hwf₂ with
      | or hwfA₂ hwfB₂ =>
        constructor
        · intro v₁ v₂ w₁ w₂ hlr h₁ h₂
          simp only [LR, LRg] at hlr ⊢
          cases hlr with
          | inl h' =>
            obtain ⟨p₁, p₂, e₁, e₂, hp⟩ := h'
            subst e₁; subst e₂
            cases h₁ with
            | inl hs₁ =>
              cases h₂ with
              | inl hs₂ =>
                exact Or.inl ⟨_, _, rfl, rfl, (coe_lr hb A hwfA₁ hwfA₂).1 hp hs₁ hs₂⟩
          | inr h' =>
            obtain ⟨p₁, p₂, e₁, e₂, hp⟩ := h'
            subst e₁; subst e₂
            cases h₁ with
            | inr hs₁ =>
              cases h₂ with
              | inr hs₂ =>
                exact Or.inr ⟨_, _, rfl, rfl, (coe_lr hb B hwfB₁ hwfB₂).1 hp hs₁ hs₂⟩
        · intro v₁ v₂ w₁ w₂ hlr h₁ h₂
          simp only [LR, LRg] at hlr ⊢
          cases hlr with
          | inl h' =>
            obtain ⟨p₁, p₂, e₁, e₂, hp⟩ := h'
            subst e₁; subst e₂
            cases h₁ with
            | inl hu₁ =>
              cases h₂ with
              | inl hu₂ =>
                exact Or.inl ⟨_, _, rfl, rfl, (coe_lr hb A hwfA₁ hwfA₂).2 hp hu₁ hu₂⟩
          | inr h' =>
            obtain ⟨p₁, p₂, e₁, e₂, hp⟩ := h'
            subst e₁; subst e₂
            cases h₁ with
            | inr hu₁ =>
              cases h₂ with
              | inr hu₂ =>
                exact Or.inr ⟨_, _, rfl, rfl, (coe_lr hb B hwfB₁ hwfB₂).2 hp hu₁ hu₂⟩
  | .var _, hwf₁, _ => nomatch hwf₁
  | .bvar _, hwf₁, _ => nomatch hwf₁
  -- ∀-signatures: WfSig makes the body brand-variable-free, so the ∀ binds nothing —
  -- every instantiation is the body itself (bsubst_notin) and, away from the open brand,
  -- open and abstract relatedness coincide on it (lrg_notin_iff).  The coercions are the
  -- identity (¬BrandIn n) and the instantiation-closure clause transfers.
  | .allb A, hwf₁, hwf₂ => by
    cases hwf₁ with
    | allb hnin₁ _ hnb₁ =>
      cases hwf₂ with
      | allb hnin₂ _ _ =>
        have hninA : ¬ BrandIn n A := fun h => hnin₁ (BrandIn.allb h)
        have hnbA : ¬ HasBVar A := fun h => hnb₁ (HasBVar.allb h)
        constructor
        · intro v₁ v₂ w₁ w₂ hlr h₁ h₂
          simp only [LRg, viewL_some, viewR_some] at hlr
          obtain ⟨hv₁, hv₂, ht₁, ht₂, hinst⟩ := hlr
          rw [substBrand_notin hnin₁] at ht₁
          rw [substBrand_notin hnin₂] at ht₂
          cases h₁ with
          | allb =>
            cases h₂ with
            | allb =>
              simp only [LR, LRg, viewL_none, viewR_none]
              refine ⟨hv₁, hv₂, ht₁, ht₂, ?_⟩
              intro m ρ₁ ρ₂ hρ₁ hρ₂
              obtain ⟨u₁, u₂, r₁, r₂, hrel⟩ := hinst m ρ₁ ρ₂ hρ₁ hρ₂
              rw [bsubst_notin hnbA] at hrel ⊢
              exact ⟨u₁, u₂, r₁, r₂, (lrg_notin_iff hninA hnbA u₁ u₂).1 hrel⟩
        · intro v₁ v₂ w₁ w₂ hlr h₁ h₂
          simp only [LR, LRg, viewL_none, viewR_none] at hlr
          obtain ⟨hv₁, hv₂, ht₁, ht₂, hinst⟩ := hlr
          cases h₁ with
          | allb =>
            cases h₂ with
            | allb =>
              simp only [LRg, viewL_some, viewR_some]
              rw [substBrand_notin hnin₁, substBrand_notin hnin₂]
              refine ⟨hv₁, hv₂, ht₁, ht₂, ?_⟩
              intro m ρ₁ ρ₂ hρ₁ hρ₂
              obtain ⟨u₁, u₂, r₁, r₂, hrel⟩ := hinst m ρ₁ ρ₂ hρ₁ hρ₂
              rw [bsubst_notin hnbA] at hrel ⊢
              exact ⟨u₁, u₂, r₁, r₂, (lrg_notin_iff hninA hnbA u₁ u₂).2 hrel⟩
  | .mu T, hwf₁, hwf₂ => by
    cases hwf₁ with
    | mu hnin₁ _ _ =>
      cases hwf₂ with
      | mu hnin₂ _ _ =>
        constructor
        · intro v₁ v₂ w₁ w₂ hlr h₁ h₂
          simp only [LRg, viewL_some, viewR_some] at hlr
          obtain ⟨hv₁, hv₂, ht₁, ht₂, heq⟩ := hlr
          subst heq
          cases h₁ with
          | mu =>
            cases h₂ with
            | mu =>
              simp only [LR, LRg, viewL_none, viewR_none]
              exact ⟨hv₁, hv₂, substBrand_notin hnin₁ ▸ ht₁, substBrand_notin hnin₂ ▸ ht₂,
                trivial⟩
        · intro v₁ v₂ w₁ w₂ hlr h₁ h₂
          simp only [LR, LRg, viewL_none, viewR_none] at hlr
          obtain ⟨hv₁, hv₂, ht₁, ht₂, heq⟩ := hlr
          subst heq
          cases h₁ with
          | mu =>
            cases h₂ with
            | mu =>
              simp only [LRg, viewL_some, viewR_some]
              refine ⟨hv₁, hv₂, ?_, ?_, trivial⟩
              · rw [substBrand_notin hnin₁]
                exact ht₁
              · rw [substBrand_notin hnin₂]
                exact ht₂
  | .int, _, _ => by
    constructor
    · intro v₁ v₂ w₁ w₂ hlr h₁ h₂
      simp only [LR, LRg] at hlr ⊢
      obtain ⟨i, e₁, e₂⟩ := hlr
      subst e₁; subst e₂
      cases h₁; cases h₂
      exact ⟨i, rfl, rfl⟩
    · intro v₁ v₂ w₁ w₂ hlr h₁ h₂
      simp only [LR, LRg] at hlr ⊢
      obtain ⟨i, e₁, e₂⟩ := hlr
      subst e₁; subst e₂
      cases h₁; cases h₂
      exact ⟨i, rfl, rfl⟩
  | .top, _, _ => by
    constructor
    · intro v₁ v₂ w₁ w₂ _ h₁ h₂; cases h₁; cases h₂; simp [LRg]
    · intro v₁ v₂ w₁ w₂ _ h₁ h₂; cases h₁; cases h₂; simp [LRg]
  | .brand m, _, _ => by
    by_cases hm : m = n
    · subst hm
      constructor
      · intro v₁ v₂ w₁ w₂ hlr h₁ h₂
        simp only [LRg, if_true] at hlr
        obtain ⟨hv₁, hv₂, ht₁, ht₂, hη⟩ := hlr
        cases h₁ with
        | brand_eq =>
          cases h₂ with
          | brand_eq =>
            simp only [LR, LRg]
            exact ⟨HasType.twrap hb.st₁ hb.nobvar₁ hv₁ ht₁,
              HasType.twrap hb.st₂ hb.nobvar₂ hv₂ ht₂,
              _, _, rfl, rfl, hη⟩
          | brand_ne hne => exact absurd rfl hne
        | brand_ne hne => exact absurd rfl hne
      · intro v₁ v₂ w₁ w₂ hlr h₁ h₂
        simp only [LR, LRg] at hlr
        obtain ⟨ht₁, ht₂, u₁, u₂, e₁, e₂, hη⟩ := hlr
        subst e₁; subst e₂
        simp only [LRg, if_true]
        cases h₁ with
        | brand_eq =>
          cases h₂ with
          | brand_eq =>
            cases ht₁ with
            | twrap hst₁ _ hu₁ hp₁ =>
              cases ht₂ with
              | twrap hst₂ _ hu₂ hp₂ =>
                rw [hb.st₁] at hst₁; cases hst₁
                rw [hb.st₂] at hst₂; cases hst₂
                exact ⟨hu₁, hu₂, hp₁, hp₂, hη⟩
          | brand_ne hne => exact absurd rfl hne
        | brand_ne hne => exact absurd rfl hne
    · constructor
      · intro v₁ v₂ w₁ w₂ hlr h₁ h₂
        simp only [LRg, hm, if_false] at hlr
        simp only [LR, LRg]
        cases h₁ with
        | brand_eq => exact absurd rfl hm
        | brand_ne _ =>
          cases h₂ with
          | brand_eq => exact absurd rfl hm
          | brand_ne _ => exact hlr
      · intro v₁ v₂ w₁ w₂ hlr h₁ h₂
        simp only [LR, LRg] at hlr
        simp only [LRg, hm, if_false]
        cases h₁ with
        | brand_eq => exact absurd rfl hm
        | brand_ne _ =>
          cases h₂ with
          | brand_eq => exact absurd rfl hm
          | brand_ne _ => exact hlr
  | .rcd l A, hwf₁, hwf₂ => by
    cases hwf₁ with | rcd _ hA₁ =>
    cases hwf₂ with | rcd _ hA₂ =>
    have ih := coe_lr hb A hA₁ hA₂
    constructor
    · intro v₁ v₂ w₁ w₂ hlr h₁ h₂
      simp only [LR, LRg] at hlr ⊢
      obtain ⟨u₁, u₂, e₁, e₂, hA⟩ := hlr
      subst e₁; subst e₂
      cases h₁ with | rcd h₁' =>
      cases h₂ with | rcd h₂' =>
      exact ⟨_, _, rfl, rfl, ih.1 hA h₁' h₂'⟩
    · intro v₁ v₂ w₁ w₂ hlr h₁ h₂
      simp only [LR, LRg] at hlr ⊢
      obtain ⟨u₁, u₂, e₁, e₂, hA⟩ := hlr
      subst e₁; subst e₂
      cases h₁ with | rcd h₁' =>
      cases h₂ with | rcd h₂' =>
      exact ⟨_, _, rfl, rfl, ih.2 hA h₁' h₂'⟩
  | .and A B, hwf₁, hwf₂ => by
    have ihA := coe_lr hb A (by cases hwf₁ with | and h _ _ _ => exact h)
      (by cases hwf₂ with | and h _ _ _ => exact h)
    have ihB := coe_lr hb B (by cases hwf₁ with | and _ h _ _ => exact h)
      (by cases hwf₂ with | and _ h _ _ => exact h)
    constructor
    · intro v₁ v₂ w₁ w₂ hlr h₁ h₂
      simp only [LR, LRg] at hlr ⊢
      obtain ⟨ht₁, ht₂, a₁, b₁, a₂, b₂, e₁, e₂, hA, hB⟩ := hlr
      subst e₁; subst e₂
      have hv₁ := Value.vmrg (lr_value hA).1 (lr_value hB).1
      have hv₂ := Value.vmrg (lr_value hA).2 (lr_value hB).2
      have hw₁ := sealv_preservation hb.st₁ hb.nores₁ hb.nobvar₁ h₁ hwf₁ hv₁ ht₁
      have hw₂ := sealv_preservation hb.st₂ hb.nores₂ hb.nobvar₂ h₂ hwf₂ hv₂ ht₂
      cases h₁ with | and h₁a h₁b =>
      cases h₂ with | and h₂a h₂b =>
      exact ⟨hw₁, hw₂, _, _, _, _, rfl, rfl, ihA.1 hA h₁a h₂a, ihB.1 hB h₁b h₂b⟩
    · intro v₁ v₂ w₁ w₂ hlr h₁ h₂
      simp only [LR, LRg] at hlr ⊢
      obtain ⟨ht₁, ht₂, a₁, b₁, a₂, b₂, e₁, e₂, hA, hB⟩ := hlr
      subst e₁; subst e₂
      have hv₁ := Value.vmrg (lr_value hA).1 (lr_value hB).1
      have hv₂ := Value.vmrg (lr_value hA).2 (lr_value hB).2
      have hw₁ := unsealv_preservation hb.st₁ hb.nores₁ hb.nobvar₁ h₁ hwf₁ hv₁ ht₁
      have hw₂ := unsealv_preservation hb.st₂ hb.nores₂ hb.nobvar₂ h₂ hwf₂ hv₂ ht₂
      cases h₁ with | and h₁a h₁b =>
      cases h₂ with | and h₂a h₂b =>
      exact ⟨hw₁, hw₂, _, _, _, _, rfl, rfl, ihA.2 hA h₁a h₂a, ihB.2 hB h₁b h₂b⟩
  | .arr A B, hwf₁, hwf₂ => by
    have hA₁ : WfSig n R₁ A := by cases hwf₁ with | arr h _ => exact h
    have hB₁ : WfSig n R₁ B := by cases hwf₁ with | arr _ h => exact h
    have hA₂ : WfSig n R₂ A := by cases hwf₂ with | arr h _ => exact h
    have hB₂ : WfSig n R₂ B := by cases hwf₂ with | arr _ h => exact h
    have ihA := coe_lr hb A hA₁ hA₂
    have ihB := coe_lr hb B hB₁ hB₂
    constructor
    -- sealing an arrow: the proxies are related at A → B (abstract)
    · intro v₁ v₂ w₁ w₂ hlr h₁ h₂
      simp only [LR, LRg] at hlr ⊢
      obtain ⟨hv₁, hv₂, ht₁, ht₂, CL⟩ := hlr
      have hw₁ := sealv_preservation hb.st₁ hb.nores₁ hb.nobvar₁ h₁ hwf₁ hv₁ ht₁
      have hw₂ := sealv_preservation hb.st₂ hb.nores₂ hb.nobvar₂ h₂ hwf₂ hv₂ ht₂
      cases h₁ with | arr =>
      cases h₂ with | arr =>
      refine ⟨Value.vclos (Value.vmrg Value.vunit (Value.vrcd hv₁)),
        Value.vclos (Value.vmrg Value.vunit (Value.vrcd hv₂)), hw₁, hw₂, ?_⟩
      intro u₁ u₂ hu ρ₁ ρ₂ hρ₁ hρ₂
      have hvu := lr_value hu
      have htu := lr_typed hu
      -- beta casts the arguments at A
      obtain ⟨u₁', cu₁⟩ := cast_progress hvu.1 htu.1 (sub_refl _)
      obtain ⟨u₂', cu₂⟩ := cast_progress hvu.2 htu.2 (sub_refl _)
      have hu' := cast_lr openadm_none (sub_refl _) hu cu₁ cu₂
      have hvu' := lr_value hu'
      have htu' := lr_typed hu'
      -- unseal them (into the representation view)
      obtain ⟨x₁, hx₁⟩ := unsealv_progress (n := n) (R := R₁) A hvu'.1 htu'.1
      obtain ⟨x₂, hx₂⟩ := unsealv_progress (n := n) (R := R₂) A hvu'.2 htu'.2
      have hx := ihA.2 hu' hx₁ hx₂
      have hvx := lr_value hx
      -- apply the underlying closures under the proxies' extended environments
      have henv₁ : Value (.mrg (proxyEnv v₁) u₁') :=
        Value.vmrg (Value.vmrg Value.vunit (Value.vrcd hv₁)) hvu'.1
      have henv₂ : Value (.mrg (proxyEnv v₂) u₂') :=
        Value.vmrg (Value.vmrg Value.vunit (Value.vrcd hv₂)) hvu'.2
      obtain ⟨y₁, y₂, ry₁, ry₂, hy⟩ := CL x₁ x₂ hx _ _ henv₁ henv₂
      have hvy := lr_value hy
      have hty := lr_typed hy
      -- seal the results (back into the abstract view)
      obtain ⟨z₁, hz₁⟩ := sealv_progress (n := n) (R := R₁) B hvy.1 hty.1
      obtain ⟨z₂, hz₂⟩ := sealv_progress (n := n) (R := R₂) B hvy.2 hty.2
      have hz := ihB.1 hy hz₁ hz₂
      have hvz := lr_value hz
      have htz := lr_typed hz
      -- beta reseals the results at B
      obtain ⟨z₁', cz₁⟩ := cast_progress hvz.1 htz.1 (sub_refl _)
      obtain ⟨z₂', cz₂⟩ := cast_progress hvz.2 htz.2 (sub_refl _)
      exact ⟨z₁', z₂',
        seal_proxy_run hρ₁ hv₁ hvu.1 cu₁ hx₁ ry₁ hvy.1 hz₁ cz₁,
        seal_proxy_run hρ₂ hv₂ hvu.2 cu₂ hx₂ ry₂ hvy.2 hz₂ cz₂,
        cast_lr openadm_none (sub_refl _) hz cz₁ cz₂⟩
    -- unsealing an arrow: the proxies are related at A[R] → B[R] (representation view)
    · intro v₁ v₂ w₁ w₂ hlr h₁ h₂
      simp only [LR, LRg] at hlr ⊢
      obtain ⟨hv₁, hv₂, ht₁, ht₂, CL⟩ := hlr
      have hw₁ := unsealv_preservation hb.st₁ hb.nores₁ hb.nobvar₁ h₁ hwf₁ hv₁ ht₁
      have hw₂ := unsealv_preservation hb.st₂ hb.nores₂ hb.nobvar₂ h₂ hwf₂ hv₂ ht₂
      cases h₁ with | arr =>
      cases h₂ with | arr =>
      refine ⟨Value.vclos (Value.vmrg Value.vunit (Value.vrcd hv₁)),
        Value.vclos (Value.vmrg Value.vunit (Value.vrcd hv₂)), hw₁, hw₂, ?_⟩
      intro u₁ u₂ hu ρ₁ ρ₂ hρ₁ hρ₂
      have hvu := lr_value hu
      have htu := lr_typed hu
      -- beta casts the arguments at A[R]
      obtain ⟨u₁', cu₁⟩ := cast_progress hvu.1 htu.1 (sub_refl _)
      obtain ⟨u₂', cu₂⟩ := cast_progress hvu.2 htu.2 (sub_refl _)
      have hu' := cast_lr hb.adm (sub_refl _) hu cu₁ cu₂
      have hvu' := lr_value hu'
      have htu' := lr_typed hu'
      -- seal them (into the abstract view)
      obtain ⟨x₁, hx₁⟩ := sealv_progress (n := n) (R := R₁) A hvu'.1 htu'.1
      obtain ⟨x₂, hx₂⟩ := sealv_progress (n := n) (R := R₂) A hvu'.2 htu'.2
      have hx := ihA.1 hu' hx₁ hx₂
      have hvx := lr_value hx
      have henv₁ : Value (.mrg (proxyEnv v₁) u₁') :=
        Value.vmrg (Value.vmrg Value.vunit (Value.vrcd hv₁)) hvu'.1
      have henv₂ : Value (.mrg (proxyEnv v₂) u₂') :=
        Value.vmrg (Value.vmrg Value.vunit (Value.vrcd hv₂)) hvu'.2
      obtain ⟨y₁, y₂, ry₁, ry₂, hy⟩ := CL x₁ x₂ hx _ _ henv₁ henv₂
      have hvy := lr_value hy
      have hty := lr_typed hy
      -- unseal the results (back into the representation view)
      obtain ⟨z₁, hz₁⟩ := unsealv_progress (n := n) (R := R₁) B hvy.1 hty.1
      obtain ⟨z₂, hz₂⟩ := unsealv_progress (n := n) (R := R₂) B hvy.2 hty.2
      have hz := ihB.2 hy hz₁ hz₂
      have hvz := lr_value hz
      have htz := lr_typed hz
      -- beta reseals the results at B[R]
      obtain ⟨z₁', cz₁⟩ := cast_progress hvz.1 htz.1 (sub_refl _)
      obtain ⟨z₂', cz₂⟩ := cast_progress hvz.2 htz.2 (sub_refl _)
      exact ⟨z₁', z₂',
        unseal_proxy_run hρ₁ hv₁ hvu.1 cu₁ hx₁ ry₁ hvy.1 hz₁ cz₁,
        unseal_proxy_run hρ₂ hv₂ hvu.2 cu₂ hx₂ ry₂ hvy.2 hz₂ cz₂,
        cast_lr hb.adm (sub_refl _) hz cz₁ cz₂⟩

-- ── Representation independence ──────────────────────────────────────────────────────

-- Two implementations of a signature S with an abstract type α_n, over representations
-- R₁ and R₂, related through an arbitrary admissible relation η n at α_n; then no client
-- typed against S (with α_n opaque, observing at Int) can tell the sealed units apart:
-- both runs compute the same literal.
theorem representation_independence {n : Nat} {R₁ R₂ : Typ}
    (hb : OpenBrand Δ₁ Δ₂ η n R₁ R₂)
    {S : Typ} (hwf₁ : WfSig n R₁ S) (hwf₂ : WfSig n R₂ S)
    {p₁ p₂ : Exp} (hrel : LRg Δ₁ Δ₂ η (some (n, R₁, R₂)) S p₁ p₂)
    {e : Exp} (hcl : HasType noBrands S e .int) (hfin : Finitary e)
    : ∃ i, MStep .unit (.box (.seal n R₁ S p₁) e) (.lit i)
         ∧ MStep .unit (.box (.seal n R₂ S p₂) e) (.lit i) := by
  have hvp := lr_value hrel
  have htp := lr_typed hrel
  obtain ⟨q₁, hq₁⟩ := sealv_progress (n := n) (R := R₁) S hvp.1 htp.1
  obtain ⟨q₂, hq₂⟩ := sealv_progress (n := n) (R := R₂) S hvp.2 htp.2
  have hq := (coe_lr hb S hwf₁ hwf₂).1 hrel hq₁ hq₂
  obtain ⟨i, r₁, r₂⟩ := sealing hq hcl hfin
  have hvq₁ : Value q₁ := sealv_value hvp.1 hq₁
  have hvq₂ : Value q₂ := sealv_value hvp.2 hq₂
  refine ⟨i, ?_, ?_⟩
  · refine MStep.step (Step.sboxl Value.vunit (Step.ssealv Value.vunit hvp.1 hq₁)) ?_
    exact mstep_trans (mstep_boxr Value.vunit hvq₁ r₁)
      (mstep_one (Step.sboxv Value.vunit hvq₁ Value.vint))
  · refine MStep.step (Step.sboxl Value.vunit (Step.ssealv Value.vunit hvp.2 hq₂)) ?_
    exact mstep_trans (mstep_boxr Value.vunit hvq₂ r₂)
      (mstep_one (Step.sboxv Value.vunit hvq₂ Value.vint))

-- ── Generic-client representation independence ───────────────────────────────────────

-- THE milestone-4 theorem.  A GENERIC client — typed ONCE at ∀β. Sig β → Int, with the
-- signature abstract in the brand it will be instantiated at — observes the same integer
-- against two sealed providers of that signature over different representations.  The
-- client instantiates at the provider's own allocated brand n: the ∀-clause is
-- instantiation-closed (no freshness guard), and η at n is exactly the relation between
-- the two representations, so `bapp · n` lands the client in the concrete-signature
-- world where `representation_independence` already lives.
theorem generic_client_representation_independence {n : Nat} {R₁ R₂ : Typ}
    (hb : OpenBrand Δ₁ Δ₂ η n R₁ R₂) {SigB : Typ}
    (hwf₁ : WfSig n R₁ (bsubst 0 n SigB)) (hwf₂ : WfSig n R₂ (bsubst 0 n SigB))
    {p₁ p₂ : Exp} (hrel : LRg Δ₁ Δ₂ η (some (n, R₁, R₂)) (bsubst 0 n SigB) p₁ p₂)
    {ct : Exp} (hct : HasType noBrands .top ct (.allb (.arr SigB .int)))
    (hfin : Finitary ct)
    : ∃ i, MStep .unit (.app (.bapp ct n) (.seal n R₁ (bsubst 0 n SigB) p₁)) (.lit i)
         ∧ MStep .unit (.app (.bapp ct n) (.seal n R₂ (bsubst 0 n SigB) p₂)) (.lit i) := by
  -- the client runs to a related pair of generic values
  obtain ⟨c₁, c₂, rc₁, rc₂, hc⟩ :=
    fundamental (Δ₁ := Δ₁) (Δ₂ := Δ₂) (η := η) hct hfin lr_top_unit
  simp only [LR, LRg] at hc
  obtain ⟨hvc₁, hvc₂, _, _, hinst⟩ := hc
  -- instantiate the ∀-clause at the provider brand
  obtain ⟨f₁, f₂, rf₁, rf₂, hf⟩ := hinst n .unit .unit Value.vunit Value.vunit
  simp only [bsubst, LRg] at hf
  obtain ⟨hvf₁, hvf₂, _, _, CL⟩ := hf
  -- seal the providers and carry their relation to the client-facing one
  have hvp := lr_value hrel
  have htp := lr_typed hrel
  obtain ⟨q₁, hq₁⟩ := sealv_progress (n := n) (R := R₁) _ hvp.1 htp.1
  obtain ⟨q₂, hq₂⟩ := sealv_progress (n := n) (R := R₂) _ hvp.2 htp.2
  have hq := (coe_lr hb _ hwf₁ hwf₂).1 hrel hq₁ hq₂
  -- apply the instantiated client to the sealed providers
  obtain ⟨r₁, r₂, rr₁, rr₂, hr⟩ := CL q₁ q₂ hq .unit .unit Value.vunit Value.vunit
  obtain ⟨i, e₁, e₂⟩ := hr
  subst e₁; subst e₂
  refine ⟨i, ?_, ?_⟩
  · refine mstep_trans (mstep_appl Value.vunit
      (mstep_trans (mstep_bapp Value.vunit rc₁) rf₁)) ?_
    refine mstep_trans (mstep_appr Value.vunit hvf₁
      (mstep_one (Step.ssealv Value.vunit hvp.1 hq₁))) ?_
    exact rr₁
  · refine mstep_trans (mstep_appl Value.vunit
      (mstep_trans (mstep_bapp Value.vunit rc₂) rf₂)) ?_
    refine mstep_trans (mstep_appr Value.vunit hvf₂
      (mstep_one (Step.ssealv Value.vunit hvp.2 hq₂))) ?_
    exact rr₂

end Seal
