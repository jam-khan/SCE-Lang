import LeanSce.Seal.Subtyping

-- Disjointness via Common Ordinary Super Types (Eᵢ Definition 1 / Appendix A.1), taken
-- algorithmically: A ∗ B := ¬(A ⊓ B).  The COST relation ports verbatim because the λE^≤
-- type grammar is exactly Eᵢ's.  Cost-arr ignoring input types is load-bearing: it makes
-- (A→C) ∗ (B→D) ↔ C ∗ D (Eᵢ Lemma 2.5), which the closure cases of consistency rely on.
namespace Seal

inductive Cost : Typ → Typ → Prop where
  | cint : Cost .int .int
  | candl {A B C} : Cost A C → Cost (.and A B) C
  | candr {A B C} : Cost B C → Cost (.and A B) C
  | crandl {A B C} : Cost A B → Cost A (.and B C)
  | crandr {A B C} : Cost A C → Cost A (.and B C)
  | carr {A B C D} : Cost B D → Cost (.arr A B) (.arr C D)
  | crcd {l A B} : Cost A B → Cost (.rcd l A) (.rcd l B)
  -- A brand's only ordinary supertype is itself, so α_n ∗ B iff α_n does not occur
  -- (as a leaf) in B.  Distinct brands are disjoint; a brand is disjoint from Int, from
  -- every arrow, from every record — regardless of its (hidden) representation.
  | cbrand {n} : Cost (.brand n) (.brand n)
  -- Any two union types share a common ordinary supertype UNCONDITIONALLY: an inl value
  -- of the one and an inr value of the other always cast (differently) at some common
  -- union target, so no two union-typed things may ever be merged.  (Wrap unions in
  -- records to merge them.)
  | coror {A B A' B'} : Cost (.or A B) (.or A' B')
  -- μ-types (and their bound variables) behave like brands: sole ordinary supertype is
  -- the type itself.
  | cvar {n} : Cost (.var n) (.var n)
  | cmu {T} : Cost (.mu T) (.mu T)
  -- Brand variables: CONSERVATIVE.  COST must only be lost, never gained, under the
  -- ∀β-instantiation bsubst — that is what makes `Disj A B → Disj (bsubst d n A)
  -- (bsubst d n B)` hold with no freshness side conditions.  A bvar may be instantiated
  -- to ANY brand, so it costs every bvar (nested binders can be instantiated alike) and
  -- every concrete brand (both directions, keeping cost_symm a permutation).  Against
  -- int/arr/rcd/or/var/mu/allb formers a bvar has NO cost: it always becomes a `brand`,
  -- and brands are disjoint from those formers.  Consequence: nothing typed at a bvar
  -- can be merged with anything brand- or bvar-typed — the `Cost.coror` wrap-in-records
  -- discipline again.  Module-land disjointness is label-driven, so signatures like
  -- {mk : Int→β} & {get : β→Int} are unaffected.
  | cbvar {i j} : Cost (.bvar i) (.bvar j)
  | cbvarbrand {i n} : Cost (.bvar i) (.brand n)
  | cbrandbvar {n i} : Cost (.brand n) (.bvar i)
  -- ∀-types are equality-keyed like μ — but two syntactically distinct bodies can become
  -- EQUAL after instantiation, so any bvar-containing ∀ conservatively costs every ∀;
  -- same for the equality-keyed cmu (mu (bvar 0) vs mu (brand 5) become equal at β:=5).
  | callb {A} : Cost (.allb A) (.allb A)
  | callbbv {A A'} : HasBVar A ∨ HasBVar A' → Cost (.allb A) (.allb A')
  | cmubv {T T'} : HasBVar T ∨ HasBVar T' → Cost (.mu T) (.mu T')

def Disj (A B : Typ) : Prop := ¬ Cost A B

theorem cost_symm : {A B : Typ} → Cost A B → Cost B A
  | _, _, .cint => .cint
  | _, _, .candl h => .crandl (cost_symm h)
  | _, _, .candr h => .crandr (cost_symm h)
  | _, _, .crandl h => .candl (cost_symm h)
  | _, _, .crandr h => .candr (cost_symm h)
  | _, _, .carr h => .carr (cost_symm h)
  | _, _, .crcd h => .crcd (cost_symm h)
  | _, _, .cbrand => .cbrand
  | _, _, .coror => .coror
  | _, _, .cvar => .cvar
  | _, _, .cmu => .cmu
  | _, _, .cbvar => .cbvar
  | _, _, .cbvarbrand => .cbrandbvar
  | _, _, .cbrandbvar => .cbvarbrand
  | _, _, .callb => .callb
  | _, _, .callbbv h => .callbbv h.symm
  | _, _, .cmubv h => .cmubv h.symm

theorem disj_symm {A B : Typ} (h : Disj A B) : Disj B A :=
  fun hc => h (cost_symm hc)

-- ε shares no common ordinary supertype with anything (its supertypes are all top-like).
theorem cost_top_l : {C : Typ} → ¬ Cost .top C
  | _, .crandl h => cost_top_l h
  | _, .crandr h => cost_top_l h

theorem disj_top {A : Typ} : Disj .top A := cost_top_l

theorem disj_top_r {A : Typ} : Disj A .top := fun hc => cost_top_l (cost_symm hc)

-- Two top-like types share no common ordinary supertype: COST's leaf rules all sit at
-- non-top-like formers (int/brand/or/var/mu), and top-likeness recurses through the
-- structural rules.
theorem toplike_disj {A B : Typ} (ha : TopLike A) (hb : TopLike B) : Disj A B := by
  intro hc
  induction hc with
  | cint => nomatch ha
  | candl _ ih => cases ha with | tland h₁ _ => exact ih h₁ hb
  | candr _ ih => cases ha with | tland _ h₂ => exact ih h₂ hb
  | crandl _ ih => cases hb with | tland h₁ _ => exact ih ha h₁
  | crandr _ ih => cases hb with | tland _ h₂ => exact ih ha h₂
  | carr _ ih => cases ha with | tlarr h₁ => cases hb with | tlarr h₂ => exact ih h₁ h₂
  | crcd _ ih => cases ha with | tlrcd h₁ => cases hb with | tlrcd h₂ => exact ih h₁ h₂
  | cbrand => nomatch ha
  | coror => nomatch ha
  | cvar => nomatch ha
  | cmu => nomatch ha
  | cbvar => nomatch ha
  | cbvarbrand => nomatch ha
  | cbrandbvar => nomatch ha
  | callb => nomatch ha
  | callbbv _ => nomatch ha
  | cmubv _ => nomatch ha

-- COST propagates down subtyping on the left (the engine of Eᵢ Lemma 2.6).
theorem cost_compose : {A B C : Typ} → Sub A B → Cost B C → Cost A C
  | _, _, _, .sint, h => h
  | _, _, _, .stop, h => absurd h cost_top_l
  | _, _, _, .sandl p, h => .candl (cost_compose p h)
  | _, _, _, .sandr p, h => .candr (cost_compose p h)
  | _, _, _, .sarr _ q, .carr h => .carr (cost_compose q h)
  | _, _, _, .sarr p q, .crandl h => .crandl (cost_compose (.sarr p q) h)
  | _, _, _, .sarr p q, .crandr h => .crandr (cost_compose (.sarr p q) h)
  | _, _, _, .srcd p, .crcd h => .crcd (cost_compose p h)
  | _, _, _, .srcd p, .crandl h => .crandl (cost_compose (.srcd p) h)
  | _, _, _, .srcd p, .crandr h => .crandr (cost_compose (.srcd p) h)
  | _, _, _, .sand p₁ _, .candl h => cost_compose p₁ h
  | _, _, _, .sand _ p₂, .candr h => cost_compose p₂ h
  | _, _, _, .sand p₁ p₂, .crandl h => .crandl (cost_compose (.sand p₁ p₂) h)
  | _, _, _, .sand p₁ p₂, .crandr h => .crandr (cost_compose (.sand p₁ p₂) h)
  | _, _, _, .sbrand, h => h
  | _, _, _, .sor _ _, .coror => .coror
  | _, _, _, .sor p q, .crandl h => .crandl (cost_compose (.sor p q) h)
  | _, _, _, .sor p q, .crandr h => .crandr (cost_compose (.sor p q) h)
  | _, _, _, .svar, h => h
  | _, _, _, .smu, h => h
  | _, _, _, .sbvar, h => h
  | _, _, _, .sallb, h => h

-- Eᵢ Lemma 2.6: disjointness is preserved by widening.
theorem sub_disj {A B C : Typ} (hs : Sub A B) (hd : Disj A C) : Disj B C :=
  fun hc => hd (cost_compose hs hc)

-- Disjointness with an intersection splits (Eᵢ Lemma 2.2, the directions used here).
theorem disj_and_inv_l {A B₁ B₂ : Typ} (h : Disj A (.and B₁ B₂)) : Disj A B₁ :=
  fun hc => h (.crandl hc)

theorem disj_and_inv_r {A B₁ B₂ : Typ} (h : Disj A (.and B₁ B₂)) : Disj A B₂ :=
  fun hc => h (.crandr hc)

-- Records with distinct labels are disjoint (Eᵢ Lemma 2.4's easy direction).
theorem disj_rcd_ne {l₁ l₂ : String} (hne : l₁ ≠ l₂) {A B : Typ}
    : Disj (.rcd l₁ A) (.rcd l₂ B) := fun hc => by
  cases hc with
  | crcd _ => exact hne rfl

-- Distinct brands are disjoint.
theorem disj_brand_ne {n m : Nat} (hne : n ≠ m) : Disj (.brand n) (.brand m) := fun hc => by
  cases hc with
  | cbrand => exact hne rfl

-- `BrandIn n B`: the brand α_n occurs somewhere in `B`.
inductive BrandIn (n : Nat) : Typ → Prop where
  | self          : BrandIn n (.brand n)
  | arrl {A B}    : BrandIn n A → BrandIn n (.arr A B)
  | arrr {A B}    : BrandIn n B → BrandIn n (.arr A B)
  | andl {A B}    : BrandIn n A → BrandIn n (.and A B)
  | andr {A B}    : BrandIn n B → BrandIn n (.and A B)
  | rcd {l A}     : BrandIn n A → BrandIn n (.rcd l A)
  | orl {A B}     : BrandIn n A → BrandIn n (.or A B)
  | orr {A B}     : BrandIn n B → BrandIn n (.or A B)
  | mu {T}        : BrandIn n T → BrandIn n (.mu T)
  -- Brand VARIABLES contain no concrete brand (a bvar is only ever replaced, never
  -- inspected), so BrandIn has no bvar case; ∀ recurses structurally.
  | allb {A}      : BrandIn n A → BrandIn n (.allb A)

-- A brand is disjoint from every bvar-free type it does not occur in — the abstraction
-- principle for disjointness: clients need no knowledge of α_n's representation to
-- discharge `α_n ∗ B`.  The bvar-freeness premise is forced by the conservative COST
-- rules: a brand costs every brand variable (the bvar might be instantiated to it).
theorem disj_brand_notin {n : Nat} : {B : Typ} → ¬ BrandIn n B → ¬ HasBVar B
    → Disj (.brand n) B
  | _, hnin, _, .cbrand => hnin BrandIn.self
  | _, _, hnb, .cbrandbvar => hnb HasBVar.bvar
  | _, hnin, hnb, .crandl h =>
    disj_brand_notin (fun h' => hnin (BrandIn.andl h')) (fun h' => hnb (HasBVar.andl h')) h
  | _, hnin, hnb, .crandr h =>
    disj_brand_notin (fun h' => hnin (BrandIn.andr h')) (fun h' => hnb (HasBVar.andr h')) h

-- Substitution is the identity on brand-free types (what makes the identity coercion at
-- brand-free μ signatures type-correct).
theorem substBrand_notin {n : Nat} {R : Typ} : {S : Typ} → ¬ BrandIn n S → substBrand n R S = S
  | .int, _ => rfl
  | .top, _ => rfl
  | .arr A B, h => by
    simp only [substBrand, substBrand_notin (fun h' => h (BrandIn.arrl h')),
      substBrand_notin (fun h' => h (BrandIn.arrr h'))]
  | .and A B, h => by
    simp only [substBrand, substBrand_notin (fun h' => h (BrandIn.andl h')),
      substBrand_notin (fun h' => h (BrandIn.andr h'))]
  | .rcd l A, h => by
    simp only [substBrand, substBrand_notin (fun h' => h (BrandIn.rcd h'))]
  | .or A B, h => by
    simp only [substBrand, substBrand_notin (fun h' => h (BrandIn.orl h')),
      substBrand_notin (fun h' => h (BrandIn.orr h'))]
  | .brand m, h => by
    by_cases hm : m = n
    · subst hm; exact absurd BrandIn.self h
    · simp only [substBrand, hm, if_false]
  | .var _, _ => rfl
  | .mu T, h => by
    simp only [substBrand, substBrand_notin (fun h' => h (BrandIn.mu h'))]
  | .bvar _, _ => rfl
  | .allb A, h => by
    simp only [substBrand, substBrand_notin (fun h' => h (BrandIn.allb h'))]

-- A subtype of a non-top-like type is COST-related to it.
theorem sub_cost {B D : Typ} (h : Sub B D) (hntl : ¬ TopLike D) : Cost B D := by
  induction h with
  | sint => exact Cost.cint
  | stop => exact absurd TopLike.tltop hntl
  | sarr _ _ _ ih₂ => exact Cost.carr (ih₂ (fun htl => hntl (TopLike.tlarr htl)))
  | sandl _ ih => exact Cost.candl (ih hntl)
  | sandr _ ih => exact Cost.candr (ih hntl)
  | sand _ _ ih₁ ih₂ =>
    rename_i D₁ D₂ _ _
    cases toplike_dec D₁ with
    | inl htl₁ =>
      exact Cost.crandr (ih₂ (fun htl₂ => hntl (TopLike.tland htl₁ htl₂)))
    | inr hntl₁ => exact Cost.crandl (ih₁ hntl₁)
  | srcd _ ih => exact Cost.crcd (ih (fun htl => hntl (TopLike.tlrcd htl)))
  | sbrand => exact Cost.cbrand
  | sor _ _ _ _ => exact Cost.coror
  | svar => exact Cost.cvar
  | smu => exact Cost.cmu
  | sbvar => exact Cost.cbvar
  | sallb => exact Cost.callb

-- Two types COST-related to Int are COST-related to each other.
theorem cost_int_compose : {B₁ B₂ : Typ} → Cost B₁ .int → Cost B₂ .int → Cost B₁ B₂
  | _, _, .cint, c₂ => cost_symm c₂
  | _, _, .candl h, c₂ => .candl (cost_int_compose h c₂)
  | _, _, .candr h, c₂ => .candr (cost_int_compose h c₂)

-- Peels for the refl-only leaves (brand/μ-var/μ/brand-variable/∀): Sub at such a leaf
-- reaches the target itself through an intersection chain, so composition arguments can
-- end in the leaf's reflexive COST.  (The former cost_{brand,var,mu}_compose lemmas are
-- replaced by these: with the conservative cmubv rule, "both cost μT" no longer composes
-- for ARBITRARY costs — two bvar-free μ's each cost `mu (bvar 0)` without costing each
-- other — but subtyping-derived costs always end in the exact leaf, where it does.)
theorem sub_brand_peel : {A : Typ} → {n : Nat} → {P : Typ → Prop} → Sub A (.brand n)
    → P (.brand n)
    → (∀ {X Y}, P X → P (.and X Y))
    → (∀ {X Y}, P Y → P (.and X Y))
    → P A
  | _, _, _, .sbrand, k, _, _ => k
  | _, _, _, .sandl t, k, kl, kr => kl (sub_brand_peel t k kl kr)
  | _, _, _, .sandr t, k, kl, kr => kr (sub_brand_peel t k kl kr)

theorem sub_var_peel : {A : Typ} → {n : Nat} → {P : Typ → Prop} → Sub A (.var n)
    → P (.var n)
    → (∀ {X Y}, P X → P (.and X Y))
    → (∀ {X Y}, P Y → P (.and X Y))
    → P A
  | _, _, _, .svar, k, _, _ => k
  | _, _, _, .sandl t, k, kl, kr => kl (sub_var_peel t k kl kr)
  | _, _, _, .sandr t, k, kl, kr => kr (sub_var_peel t k kl kr)

theorem sub_mu_peel : {A T : Typ} → {P : Typ → Prop} → Sub A (.mu T)
    → P (.mu T)
    → (∀ {X Y}, P X → P (.and X Y))
    → (∀ {X Y}, P Y → P (.and X Y))
    → P A
  | _, _, _, .smu, k, _, _ => k
  | _, _, _, .sandl t, k, kl, kr => kl (sub_mu_peel t k kl kr)
  | _, _, _, .sandr t, k, kl, kr => kr (sub_mu_peel t k kl kr)

theorem sub_bvar_peel : {A : Typ} → {i : Nat} → {P : Typ → Prop} → Sub A (.bvar i)
    → P (.bvar i)
    → (∀ {X Y}, P X → P (.and X Y))
    → (∀ {X Y}, P Y → P (.and X Y))
    → P A
  | _, _, _, .sbvar, k, _, _ => k
  | _, _, _, .sandl t, k, kl, kr => kl (sub_bvar_peel t k kl kr)
  | _, _, _, .sandr t, k, kl, kr => kr (sub_bvar_peel t k kl kr)

theorem sub_allb_peel : {A B' : Typ} → {P : Typ → Prop} → Sub A (.allb B')
    → P (.allb B')
    → (∀ {X Y}, P X → P (.and X Y))
    → (∀ {X Y}, P Y → P (.and X Y))
    → P A
  | _, _, _, .sallb, k, _, _ => k
  | _, _, _, .sandl t, k, kl, kr => kl (sub_allb_peel t k kl kr)
  | _, _, _, .sandr t, k, kl, kr => kr (sub_allb_peel t k kl kr)

-- Two subtypes of a common non-top-like type share a common ordinary supertype
-- (the compositional bridge behind "both casts succeeding refutes disjointness").
theorem sub_sub_cost : {D B₁ B₂ : Typ} → ¬ TopLike D → Sub B₁ D → Sub B₂ D → Cost B₁ B₂ := by
  intro D
  induction D with
  | top => intro _ _ hntl _; exact absurd TopLike.tltop hntl
  | int =>
    intro B₁ B₂ hntl h₁ h₂
    exact cost_int_compose (sub_cost h₁ hntl) (sub_cost h₂ hntl)
  | brand n =>
    intro B₁ B₂ _ h₁ h₂
    refine sub_brand_peel (P := fun X => Cost X B₂) h₁ ?_
      (fun t => Cost.candl t) (fun t => Cost.candr t)
    exact sub_brand_peel (P := fun Y => Cost (.brand n) Y) h₂ Cost.cbrand
      (fun t => Cost.crandl t) (fun t => Cost.crandr t)
  | var n =>
    intro B₁ B₂ _ h₁ h₂
    refine sub_var_peel (P := fun X => Cost X B₂) h₁ ?_
      (fun t => Cost.candl t) (fun t => Cost.candr t)
    exact sub_var_peel (P := fun Y => Cost (.var n) Y) h₂ Cost.cvar
      (fun t => Cost.crandl t) (fun t => Cost.crandr t)
  | mu T _ =>
    intro B₁ B₂ _ h₁ h₂
    refine sub_mu_peel (P := fun X => Cost X B₂) h₁ ?_
      (fun t => Cost.candl t) (fun t => Cost.candr t)
    exact sub_mu_peel (P := fun Y => Cost (.mu T) Y) h₂ Cost.cmu
      (fun t => Cost.crandl t) (fun t => Cost.crandr t)
  | bvar i =>
    intro B₁ B₂ _ h₁ h₂
    refine sub_bvar_peel (P := fun X => Cost X B₂) h₁ ?_
      (fun t => Cost.candl t) (fun t => Cost.candr t)
    exact sub_bvar_peel (P := fun Y => Cost (.bvar i) Y) h₂ Cost.cbvar
      (fun t => Cost.crandl t) (fun t => Cost.crandr t)
  | allb B' _ =>
    intro B₁ B₂ _ h₁ h₂
    refine sub_allb_peel (P := fun X => Cost X B₂) h₁ ?_
      (fun t => Cost.candl t) (fun t => Cost.candr t)
    exact sub_allb_peel (P := fun Y => Cost (.allb B') Y) h₂ Cost.callb
      (fun t => Cost.crandl t) (fun t => Cost.crandr t)
  | and D₁ D₂ ihD₁ ihD₂ =>
    intro B₁ B₂ hntl h₁ h₂
    cases toplike_dec D₁ with
    | inr hntl₁ => exact ihD₁ hntl₁ (sub_and_inv_l h₁) (sub_and_inv_l h₂)
    | inl htl₁ =>
      have hntl₂ : ¬ TopLike D₂ := fun htl₂ => hntl (TopLike.tland htl₁ htl₂)
      exact ihD₂ hntl₂ (sub_and_inv_r h₁) (sub_and_inv_r h₂)
  | arr C D' _ ihD' =>
    intro B₁ B₂ hntl h₁ h₂
    have hntl' : ¬ TopLike D' := fun htl => hntl (TopLike.tlarr htl)
    refine sub_arr_peel (P := fun X => Cost X B₂) h₁
      (fun {A₁ A₂} _ s₁ => ?_)
      (fun t => Cost.candl t) (fun t => Cost.candr t)
    exact sub_arr_peel (P := fun Y => Cost (.arr A₁ A₂) Y) h₂
      (fun _ s₂ => Cost.carr (ihD' hntl' s₁ s₂))
      (fun t => Cost.crandl t) (fun t => Cost.crandr t)
  | rcd l D' ihD' =>
    intro B₁ B₂ hntl h₁ h₂
    have hntl' : ¬ TopLike D' := fun htl => hntl (TopLike.tlrcd htl)
    refine sub_rcd_peel (P := fun X => Cost X B₂) h₁
      (fun {A'} s₁ => ?_)
      (fun t => Cost.candl t) (fun t => Cost.candr t)
    exact sub_rcd_peel (P := fun Y => Cost (.rcd l A') Y) h₂
      (fun s₂ => Cost.crcd (ihD' hntl' s₁ s₂))
      (fun t => Cost.crandl t) (fun t => Cost.crandr t)
  | or D₁ D₂ _ _ =>
    intro B₁ B₂ _ h₁ h₂
    refine sub_or_peel (P := fun X => Cost X B₂) h₁
      (fun {A₁ A₂} _ _ => ?_)
      (fun t => Cost.candl t) (fun t => Cost.candr t)
    exact sub_or_peel (P := fun Y => Cost (.or A₁ A₂) Y) h₂
      (fun _ _ => Cost.coror)
      (fun t => Cost.crandl t) (fun t => Cost.crandr t)

end Seal
