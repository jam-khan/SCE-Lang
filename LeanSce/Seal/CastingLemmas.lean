import LeanSce.Seal.SmallStep

-- The casting lemma layer ported from Eᵢ §4 (Lemmas 4–12), in dependency order:
-- generator lemmas → casts_not_disjoint → disjoint_consistent (L4) → value_weaken (L5) →
-- cast_determinism (L6) → cast_trans (L10) → consistent_after_cast (L11) →
-- cast_preservation (L12) → cast_progress (L9).
namespace Seal

variable {Δ : BrandStore}

-- Casting the unit value lands on the generator of a top-like target.
theorem cast_unit_gen : {T : Typ} → {w : Exp} → Cast .unit T w → w = genVal T ∧ TopLike T
  | _, _, .ctop => ⟨rfl, TopLike.tltop⟩
  | _, _, .cand c₁ c₂ =>
    have h₁ := cast_unit_gen c₁
    have h₂ := cast_unit_gen c₂
    ⟨by rw [h₁.1, h₂.1]; rfl, TopLike.tland h₁.2 h₂.2⟩

-- Casting a generator value lands on the generator of the target, and the target is
-- top-like.  (The agent of Eᵢ's Casting-arrowtl determinism story.)
theorem toplike_gen_cast_aux {g : Exp} {T : Typ} {w : Exp} (hc : Cast g T w)
    : ∀ {A : Typ}, g = genVal A → TopLike A → w = genVal T ∧ TopLike T := by
  induction hc with
  | cint =>
    intro A hg _
    cases A with
    | int => nomatch hg
    | top => nomatch hg
    | arr _ _ => nomatch hg
    | and _ _ => nomatch hg
    | rcd _ _ => nomatch hg
    | brand _ => nomatch hg
    | or _ _ => nomatch hg
    | var _ => nomatch hg
    | mu _ => nomatch hg
  | cwrap =>
    intro A hg _
    cases A with
    | int => nomatch hg
    | top => nomatch hg
    | arr _ _ => nomatch hg
    | and _ _ => nomatch hg
    | rcd _ _ => nomatch hg
    | brand _ => nomatch hg
    | or _ _ => nomatch hg
    | var _ => nomatch hg
    | mu _ => nomatch hg
  | ctop =>
    intro A _ _
    exact ⟨rfl, TopLike.tltop⟩
  | carrow hntl _ hsB =>
    intro A hg htl
    cases A with
    | int => nomatch hg
    | top => nomatch hg
    | and _ _ => nomatch hg
    | rcd _ _ => nomatch hg
    | brand _ => nomatch hg
    | or _ _ => nomatch hg
    | var _ => nomatch hg
    | mu _ => nomatch hg
    | arr C₀ D₀ =>
      injection hg with _ _ hB _
      cases htl with
      | tlarr hD₀ => exact absurd (sub_toplike hD₀ (hB ▸ hsB)) hntl
  | carrowtl htl' _ _ =>
    intro A _ _
    exact ⟨rfl, TopLike.tlarr htl'⟩
  | cfarrow _ _ _ =>
    intro A hg _
    cases A with
    | int => nomatch hg
    | top => nomatch hg
    | arr _ _ => nomatch hg
    | and _ _ => nomatch hg
    | rcd _ _ => nomatch hg
    | brand _ => nomatch hg
    | or _ _ => nomatch hg
    | var _ => nomatch hg
    | mu _ => nomatch hg
  | cfarrowtl _ _ _ =>
    intro A hg _
    cases A with
    | int => nomatch hg
    | top => nomatch hg
    | arr _ _ => nomatch hg
    | and _ _ => nomatch hg
    | rcd _ _ => nomatch hg
    | brand _ => nomatch hg
    | or _ _ => nomatch hg
    | var _ => nomatch hg
    | mu _ => nomatch hg
  | cinl _ _ =>
    intro A hg _
    cases A with
    | int => nomatch hg
    | top => nomatch hg
    | arr _ _ => nomatch hg
    | and _ _ => nomatch hg
    | rcd _ _ => nomatch hg
    | brand _ => nomatch hg
    | or _ _ => nomatch hg
    | var _ => nomatch hg
    | mu _ => nomatch hg
  | cinr _ _ =>
    intro A hg _
    cases A with
    | int => nomatch hg
    | top => nomatch hg
    | arr _ _ => nomatch hg
    | and _ _ => nomatch hg
    | rcd _ _ => nomatch hg
    | brand _ => nomatch hg
    | or _ _ => nomatch hg
    | var _ => nomatch hg
    | mu _ => nomatch hg
  | cfold =>
    intro A hg _
    cases A with
    | int => nomatch hg
    | top => nomatch hg
    | arr _ _ => nomatch hg
    | and _ _ => nomatch hg
    | rcd _ _ => nomatch hg
    | brand _ => nomatch hg
    | or _ _ => nomatch hg
    | var _ => nomatch hg
    | mu _ => nomatch hg
  | cmrgl _ _ ih =>
    intro A hg htl
    cases A with
    | int => nomatch hg
    | top => nomatch hg
    | arr _ _ => nomatch hg
    | rcd _ _ => nomatch hg
    | brand _ => nomatch hg
    | or _ _ => nomatch hg
    | var _ => nomatch hg
    | mu _ => nomatch hg
    | and A₁ A₂ =>
      injection hg with h₁ _
      cases htl with
      | tland htl₁ _ => exact ih h₁ htl₁
  | cmrgr _ _ ih =>
    intro A hg htl
    cases A with
    | int => nomatch hg
    | top => nomatch hg
    | arr _ _ => nomatch hg
    | rcd _ _ => nomatch hg
    | brand _ => nomatch hg
    | or _ _ => nomatch hg
    | var _ => nomatch hg
    | mu _ => nomatch hg
    | and A₁ A₂ =>
      injection hg with _ h₂
      cases htl with
      | tland _ htl₂ => exact ih h₂ htl₂
  | cand _ _ ih₁ ih₂ =>
    intro A hg htl
    have h₁ := ih₁ hg htl
    have h₂ := ih₂ hg htl
    exact ⟨by rw [h₁.1, h₂.1]; rfl, TopLike.tland h₁.2 h₂.2⟩
  | crcd _ ih =>
    intro A hg htl
    cases A with
    | int => nomatch hg
    | top => nomatch hg
    | arr _ _ => nomatch hg
    | and _ _ => nomatch hg
    | brand _ => nomatch hg
    | or _ _ => nomatch hg
    | var _ => nomatch hg
    | mu _ => nomatch hg
    | rcd l' A' =>
      injection hg with _ hA'
      cases htl with
      | tlrcd htl' =>
        have h' := ih hA' htl'
        exact ⟨by rw [h'.1]; rfl, TopLike.tlrcd h'.2⟩

-- Casting a generator value lands on the generator of the target, and the target is
-- top-like.  (The agent of Eᵢ's Casting-arrowtl determinism story.)
theorem toplike_gen_cast {A : Typ} (htl : TopLike A) {T : Typ} {w : Exp}
    (hc : Cast (genVal A) T w) : w = genVal T ∧ TopLike T :=
  toplike_gen_cast_aux hc rfl htl

-- Generators of top-like types are consistent with each other.
theorem gen_consistent {A B : Typ} (hA : TopLike A) (hB : TopLike B)
    : Consistent (genVal A) (genVal B) := by
  intro T w₁ w₂ c₁ c₂
  have h₁ := toplike_gen_cast hA c₁
  have h₂ := toplike_gen_cast hB c₂
  rw [h₁.1, h₂.1]

-- ⌉A⌈ → A↑ inhabits A in any context (needed for preservation of Casting-arrowtl).
theorem genVal_typed {A : Typ} (htl : TopLike A) : ∀ Γ, HasType Δ Γ (genVal A) A := by
  induction htl with
  | tltop => intro Γ; exact HasType.tunit
  | tland h₁ h₂ ih₁ ih₂ =>
    intro Γ
    exact HasType.tmergev (genVal_value _) (genVal_value _) (ih₁ .top) (ih₂ .top)
      (toplike_disj h₁ h₂) (gen_consistent h₁ h₂)
  | tlarr h ih =>
    intro Γ
    rename_i A₁ A₂
    exact HasType.tclos Value.vunit HasType.tunit disj_top (ih (.and .top A₁))
      (sub_refl A₂) (sub_refl A₁)
  | tlrcd h ih =>
    intro Γ
    exact HasType.trcd (ih Γ)

-- A value castable at Int has an Int leaf in its type.
theorem cast_int_cost : {v w : Exp} → Cast v .int w
    → ∀ {Γ B : Typ}, Value v → HasType Δ Γ v B → Cost B .int
  | _, _, .cint => by
    intro _ ht
    cases ht
    exact Cost.cint
  | _, _, .cmrgl _ hc => by
    intro hv ht
    cases hv with | vmrg hp _ =>
    cases ht with
    | tmrg hp' _ _ _ => exact Cost.candl (cast_int_cost hc hp hp')
    | tmergev _ _ hp' _ _ _ => exact Cost.candl (cast_int_cost hc hp hp')
    | tmergevc _ _ hp' _ _ _ _ _ _ => exact Cost.candl (cast_int_cost hc hp hp')
  | _, _, .cmrgr _ hc => by
    intro hv ht
    cases hv with | vmrg _ hq =>
    cases ht with
    | tmrg _ hq' _ _ => exact Cost.candr (cast_int_cost hc hq hq')
    | tmergev _ _ _ hq' _ _ => exact Cost.candr (cast_int_cost hc hq hq')
    | tmergevc _ _ _ hq' _ _ _ _ _ => exact Cost.candr (cast_int_cost hc hq hq')

-- A value castable at a non-top-like arrow type is COST-related to any arrow whose
-- codomain sits below the target codomain.
theorem cast_arr_cost : {v w : Exp} → {C D : Typ} → Cast v (.arr C D) w → ¬ TopLike D
    → ∀ {Γ B : Typ}, Value v → HasType Δ Γ v B
    → ∀ {E B₀ : Typ}, Sub B₀ D → Cost (.arr E B₀) B
  | _, _, _, _, .carrow _ _ hsB', hntlD => by
    intro _ ht
    intro E B₀ hsB₀
    cases ht with
    | tclos _ _ _ _ _ _ => exact Cost.carr (sub_sub_cost hntlD hsB₀ hsB')
  | _, _, _, _, .carrowtl htl _ _, hntlD => absurd htl hntlD
  | _, _, _, _, .cfarrow _ _ hsB', hntlD => by
    intro _ ht
    intro E B₀ hsB₀
    cases ht with
    | tfclos _ _ _ _ _ _ _ _ => exact Cost.carr (sub_sub_cost hntlD hsB₀ hsB')
  | _, _, _, _, .cfarrowtl htl _ _, hntlD => absurd htl hntlD
  | _, _, _, _, .cmrgl _ hc, hntlD => by
    intro hv ht
    intro E B₀ hsB₀
    cases hv with | vmrg hp _ =>
    cases ht with
    | tmrg hp' _ _ _ => exact Cost.crandl (cast_arr_cost hc hntlD hp hp' hsB₀)
    | tmergev _ _ hp' _ _ _ => exact Cost.crandl (cast_arr_cost hc hntlD hp hp' hsB₀)
    | tmergevc _ _ hp' _ _ _ _ _ _ => exact Cost.crandl (cast_arr_cost hc hntlD hp hp' hsB₀)
  | _, _, _, _, .cmrgr _ hc, hntlD => by
    intro hv ht
    intro E B₀ hsB₀
    cases hv with | vmrg _ hq =>
    cases ht with
    | tmrg _ hq' _ _ => exact Cost.crandr (cast_arr_cost hc hntlD hq hq' hsB₀)
    | tmergev _ _ _ hq' _ _ => exact Cost.crandr (cast_arr_cost hc hntlD hq hq' hsB₀)
    | tmergevc _ _ _ hq' _ _ _ _ _ => exact Cost.crandr (cast_arr_cost hc hntlD hq hq' hsB₀)

-- A value castable at a brand has that brand as a leaf of its type (only wrappers cast at
-- brands, and only twrap types wrappers).
theorem cast_brand_cost : {v w : Exp} → {n : Nat} → Cast v (.brand n) w
    → ∀ {Γ B : Typ}, Value v → HasType Δ Γ v B → Cost B (.brand n)
  | _, _, _, .cwrap => by
    intro _ ht
    cases ht
    exact Cost.cbrand
  | _, _, _, .cmrgl _ hc => by
    intro hv ht
    cases hv with | vmrg hp _ =>
    cases ht with
    | tmrg hp' _ _ _ => exact Cost.candl (cast_brand_cost hc hp hp')
    | tmergev _ _ hp' _ _ _ => exact Cost.candl (cast_brand_cost hc hp hp')
    | tmergevc _ _ hp' _ _ _ _ _ _ => exact Cost.candl (cast_brand_cost hc hp hp')
  | _, _, _, .cmrgr _ hc => by
    intro hv ht
    cases hv with | vmrg _ hq =>
    cases ht with
    | tmrg _ hq' _ _ => exact Cost.candr (cast_brand_cost hc hq hq')
    | tmergev _ _ _ hq' _ _ => exact Cost.candr (cast_brand_cost hc hq hq')
    | tmergevc _ _ _ hq' _ _ _ _ _ => exact Cost.candr (cast_brand_cost hc hq hq')

-- A value castable at a union target has a union leaf in its type; since any two union
-- types share a COST unconditionally (coror), the leaf is COST-related to EVERY union.
theorem cast_or_cost : {v w : Exp} → {A' B' : Typ} → Cast v (.or A' B') w
    → ∀ {Γ B X₁ X₂ : Typ}, Value v → HasType Δ Γ v B → Cost B (.or X₁ X₂)
  | _, _, _, _, .cinl _ => by
    intro _ ht
    cases ht with
    | tinl _ => exact Cost.coror
  | _, _, _, _, .cinr _ => by
    intro _ ht
    cases ht with
    | tinr _ => exact Cost.coror
  | _, _, _, _, .cmrgl _ hc => by
    intro hv ht
    cases hv with | vmrg hp _ =>
    cases ht with
    | tmrg hp' _ _ _ => exact Cost.candl (cast_or_cost hc hp hp')
    | tmergev _ _ hp' _ _ _ => exact Cost.candl (cast_or_cost hc hp hp')
    | tmergevc _ _ hp' _ _ _ _ _ _ => exact Cost.candl (cast_or_cost hc hp hp')
  | _, _, _, _, .cmrgr _ hc => by
    intro hv ht
    cases hv with | vmrg _ hq =>
    cases ht with
    | tmrg _ hq' _ _ => exact Cost.candr (cast_or_cost hc hq hq')
    | tmergev _ _ _ hq' _ _ => exact Cost.candr (cast_or_cost hc hq hq')
    | tmergevc _ _ _ hq' _ _ _ _ _ => exact Cost.candr (cast_or_cost hc hq hq')

-- A value castable at a μ-type has that μ-type as a leaf of its type (only same-body
-- folds cast at μ, and only tfold types folds) — the brand pattern.
theorem cast_mu_cost : {v w : Exp} → {T : Typ} → Cast v (.mu T) w
    → ∀ {Γ B : Typ}, Value v → HasType Δ Γ v B → Cost B (.mu T)
  | _, _, _, .cfold => by
    intro _ ht
    cases ht
    exact Cost.cmu
  | _, _, _, .cmrgl _ hc => by
    intro hv ht
    cases hv with | vmrg hp _ =>
    cases ht with
    | tmrg hp' _ _ _ => exact Cost.candl (cast_mu_cost hc hp hp')
    | tmergev _ _ hp' _ _ _ => exact Cost.candl (cast_mu_cost hc hp hp')
    | tmergevc _ _ hp' _ _ _ _ _ _ => exact Cost.candl (cast_mu_cost hc hp hp')
  | _, _, _, .cmrgr _ hc => by
    intro hv ht
    cases hv with | vmrg _ hq =>
    cases ht with
    | tmrg _ hq' _ _ => exact Cost.candr (cast_mu_cost hc hq hq')
    | tmergev _ _ _ hq' _ _ => exact Cost.candr (cast_mu_cost hc hq hq')
    | tmergevc _ _ _ hq' _ _ _ _ _ => exact Cost.candr (cast_mu_cost hc hq hq')

-- Peel the second cast at a record target down to its record leaf, handing the leaf to a
-- continuation (which will be the outer induction hypothesis of casts_not_disjoint).
theorem cast_rcd_cost_aux : {v w : Exp} → {l : String} → {T' : Typ} → Cast v (.rcd l T') w
    → ∀ {Γ B : Typ} {A' : Typ}, Value v → HasType Δ Γ v B
    → (∀ {p' : Exp} {Γ' B' : Typ} {w' : Exp},
        Value p' → HasType Δ Γ' p' B' → Cast p' T' w' → Cost A' B')
    → Cost (.rcd l A') B
  | _, _, _, _, .crcd hc' => by
    intro hv ht k
    cases hv with | vrcd hp =>
    cases ht with
    | trcd hp' => exact Cost.crcd (k hp hp' hc')
  | _, _, _, _, .cmrgl _ hc => by
    intro hv ht k
    cases hv with | vmrg hp _ =>
    cases ht with
    | tmrg hp' _ _ _ => exact Cost.crandl (cast_rcd_cost_aux hc hp hp' k)
    | tmergev _ _ hp' _ _ _ => exact Cost.crandl (cast_rcd_cost_aux hc hp hp' k)
    | tmergevc _ _ hp' _ _ _ _ _ _ => exact Cost.crandl (cast_rcd_cost_aux hc hp hp' k)
  | _, _, _, _, .cmrgr _ hc => by
    intro hv ht k
    cases hv with | vmrg _ hq =>
    cases ht with
    | tmrg _ hq' _ _ => exact Cost.crandr (cast_rcd_cost_aux hc hq hq' k)
    | tmergev _ _ _ hq' _ _ => exact Cost.crandr (cast_rcd_cost_aux hc hq hq' k)
    | tmergevc _ _ _ hq' _ _ _ _ _ => exact Cost.crandr (cast_rcd_cost_aux hc hq hq' k)

-- If two well-typed values both cast at a common non-top-like type, their types share a
-- common ordinary supertype.  This is the heart of Eᵢ Lemma 4: disjoint values simply have
-- no common non-top-like cast targets.
theorem casts_not_disjoint
    {v₁ : Exp} {T : Typ} {w₁ : Exp} (hc₁ : Cast v₁ T w₁)
    : ∀ {Γ₁ A : Typ}, Value v₁ → HasType Δ Γ₁ v₁ A
    → ∀ {v₂ : Exp} {Γ₂ B : Typ} {w₂ : Exp}, Value v₂ → HasType Δ Γ₂ v₂ B → Cast v₂ T w₂
    → ¬ TopLike T → Cost A B := by
  induction hc₁ with
  | ctop =>
    intro _ _ _ _ _ _ _ _ _ _ _ hntl
    exact absurd TopLike.tltop hntl
  | cint =>
    intro Γ₁ A _ ht₁ v₂ Γ₂ B w₂ hv₂ ht₂ hc₂ _
    cases ht₁
    exact cost_symm (cast_int_cost hc₂ hv₂ ht₂)
  | carrow hntlD _ hsB =>
    intro Γ₁ A _ ht₁ v₂ Γ₂ B w₂ hv₂ ht₂ hc₂ _
    cases ht₁ with
    | tclos _ _ _ _ _ _ => exact cast_arr_cost hc₂ hntlD hv₂ ht₂ hsB
  | carrowtl htlD _ _ =>
    intro _ _ _ _ _ _ _ _ _ _ _ hntl
    exact absurd (TopLike.tlarr htlD) hntl
  | cfarrow hntlD _ hsB =>
    intro Γ₁ A _ ht₁ v₂ Γ₂ B w₂ hv₂ ht₂ hc₂ _
    cases ht₁ with
    | tfclos _ _ _ _ _ _ _ _ => exact cast_arr_cost hc₂ hntlD hv₂ ht₂ hsB
  | cfarrowtl htlD _ _ =>
    intro _ _ _ _ _ _ _ _ _ _ _ hntl
    exact absurd (TopLike.tlarr htlD) hntl
  | cinl _ =>
    intro Γ₁ A _ ht₁ v₂ Γ₂ B w₂ hv₂ ht₂ hc₂ _
    cases ht₁ with
    | tinl _ => exact cost_symm (cast_or_cost hc₂ hv₂ ht₂)
  | cinr _ =>
    intro Γ₁ A _ ht₁ v₂ Γ₂ B w₂ hv₂ ht₂ hc₂ _
    cases ht₁ with
    | tinr _ => exact cost_symm (cast_or_cost hc₂ hv₂ ht₂)
  | cfold =>
    intro Γ₁ A _ ht₁ v₂ Γ₂ B w₂ hv₂ ht₂ hc₂ _
    cases ht₁
    exact cost_symm (cast_mu_cost hc₂ hv₂ ht₂)
  | cwrap =>
    intro Γ₁ A _ ht₁ v₂ Γ₂ B w₂ hv₂ ht₂ hc₂ _
    cases ht₁
    exact cost_symm (cast_brand_cost hc₂ hv₂ ht₂)
  | cmrgl _ _ ih =>
    intro Γ₁ A hv₁ ht₁ v₂ Γ₂ B w₂ hv₂ ht₂ hc₂ hntl
    cases hv₁ with | vmrg hp _ =>
    cases ht₁ with
    | tmrg hp' _ _ _ => exact Cost.candl (ih hp hp' hv₂ ht₂ hc₂ hntl)
    | tmergev _ _ hp' _ _ _ => exact Cost.candl (ih hp hp' hv₂ ht₂ hc₂ hntl)
    | tmergevc _ _ hp' _ _ _ _ _ _ => exact Cost.candl (ih hp hp' hv₂ ht₂ hc₂ hntl)
  | cmrgr _ _ ih =>
    intro Γ₁ A hv₁ ht₁ v₂ Γ₂ B w₂ hv₂ ht₂ hc₂ hntl
    cases hv₁ with | vmrg _ hq =>
    cases ht₁ with
    | tmrg _ hq' _ _ => exact Cost.candr (ih hq hq' hv₂ ht₂ hc₂ hntl)
    | tmergev _ _ _ hq' _ _ => exact Cost.candr (ih hq hq' hv₂ ht₂ hc₂ hntl)
    | tmergevc _ _ _ hq' _ _ _ _ _ => exact Cost.candr (ih hq hq' hv₂ ht₂ hc₂ hntl)
  | @cand _ T₁ T₂ _ _ _ _ ih₁ ih₂ =>
    intro Γ₁ A hv₁ ht₁ v₂ Γ₂ B w₂ hv₂ ht₂ hc₂ hntl
    cases hc₂ with
    | cmrgl hord _ => nomatch hord
    | cmrgr hord _ => nomatch hord
    | cand b₁ b₂ =>
      cases toplike_dec T₁ with
      | inr hntl₁ => exact ih₁ hv₁ ht₁ hv₂ ht₂ b₁ hntl₁
      | inl htl₁ =>
        exact ih₂ hv₁ ht₁ hv₂ ht₂ b₂ (fun h => hntl (TopLike.tland htl₁ h))
  | crcd _ ih =>
    intro Γ₁ A hv₁ ht₁ v₂ Γ₂ B w₂ hv₂ ht₂ hc₂ hntl
    cases hv₁ with | vrcd hp =>
    cases ht₁ with
    | trcd hp' =>
      exact cast_rcd_cost_aux hc₂ hv₂ ht₂
        (fun hvp' hp'' hc' => ih hp hp' hvp' hp'' hc' (fun h => hntl (TopLike.tlrcd h)))

-- Eᵢ Lemma 4: disjointness implies consistency.
theorem disjoint_consistent {v₁ v₂ : Exp} {Γ₁ Γ₂ A B : Typ}
    (hv₁ : Value v₁) (hv₂ : Value v₂) (ht₁ : HasType Δ Γ₁ v₁ A) (ht₂ : HasType Δ Γ₂ v₂ B)
    (hd : Disj A B) : Consistent v₁ v₂ := by
  intro T w₁ w₂ c₁ c₂
  induction T generalizing w₁ w₂ with
  | top =>
    cases c₁ with
    | ctop =>
      cases c₂ with
      | ctop => rfl
      | cmrgl hord _ => nomatch hord
      | cmrgr hord _ => nomatch hord
    | cmrgl hord _ => nomatch hord
    | cmrgr hord _ => nomatch hord
  | and T₁ T₂ ih₁ ih₂ =>
    cases c₁ with
    | cmrgl hord _ => nomatch hord
    | cmrgr hord _ => nomatch hord
    | cand a₁ a₂ =>
      cases c₂ with
      | cmrgl hord _ => nomatch hord
      | cmrgr hord _ => nomatch hord
      | cand b₁ b₂ => rw [ih₁ a₁ b₁, ih₂ a₂ b₂]
  | int =>
    cases toplike_dec .int with
    | inl htl => nomatch htl
    | inr hntl => exact absurd (casts_not_disjoint c₁ hv₁ ht₁ hv₂ ht₂ c₂ hntl) hd
  | brand n =>
    cases toplike_dec (.brand n) with
    | inl htl => nomatch htl
    | inr hntl => exact absurd (casts_not_disjoint c₁ hv₁ ht₁ hv₂ ht₂ c₂ hntl) hd
  | or T₁ T₂ _ _ =>
    cases toplike_dec (.or T₁ T₂) with
    | inl htl => nomatch htl
    | inr hntl => exact absurd (casts_not_disjoint c₁ hv₁ ht₁ hv₂ ht₂ c₂ hntl) hd
  | var n =>
    cases toplike_dec (.var n) with
    | inl htl => nomatch htl
    | inr hntl => exact absurd (casts_not_disjoint c₁ hv₁ ht₁ hv₂ ht₂ c₂ hntl) hd
  | mu T _ =>
    cases toplike_dec (.mu T) with
    | inl htl => nomatch htl
    | inr hntl => exact absurd (casts_not_disjoint c₁ hv₁ ht₁ hv₂ ht₂ c₂ hntl) hd
  | arr T₁ T₂ _ _ =>
    cases toplike_dec (.arr T₁ T₂) with
    | inl htl => rw [cast_toplike_gen htl c₁, cast_toplike_gen htl c₂]
    | inr hntl => exact absurd (casts_not_disjoint c₁ hv₁ ht₁ hv₂ ht₂ c₂ hntl) hd
  | rcd l T' _ =>
    cases toplike_dec (.rcd l T') with
    | inl htl => rw [cast_toplike_gen htl c₁, cast_toplike_gen htl c₂]
    | inr hntl => exact absurd (casts_not_disjoint c₁ hv₁ ht₁ hv₂ ht₂ c₂ hntl) hd

-- Value closedness (Eᵢ Lemma 5 / Core's value_weaken): a well-typed value is well-typed
-- under any context.  Merges typed by the context-sensitive tmrg re-type via tmergev,
-- with consistency supplied by disjointness of the branches.
theorem value_weaken {v : Exp} {Γ A : Typ} (ht : HasType Δ Γ v A)
    : ∀ {Γ' : Typ}, Value v → HasType Δ Γ' v A := by
  induction ht with
  | tquery => intro _ hv; nomatch hv
  | tint => intro _ _; exact HasType.tint
  | tunit => intro _ _; exact HasType.tunit
  | tapp _ _ _ _ => intro _ hv; nomatch hv
  | tbox _ _ _ _ => intro _ hv; nomatch hv
  | tproj _ _ _ => intro _ hv; nomatch hv
  | trcd _ ih => intro _ hv; cases hv with | vrcd hv' => exact HasType.trcd (ih hv')
  | trproj _ _ _ => intro _ hv; nomatch hv
  | tmrg hp hq hd₁ hd₂ ih₁ ih₂ =>
    intro Γ' hv
    cases hv with
    | vmrg hv₁ hv₂ =>
      exact HasType.tmergev hv₁ hv₂ (ih₁ hv₁) (ih₂ hv₂) hd₂
        (disjoint_consistent hv₁ hv₂ hp hq hd₂)
  | tmergev hv₁ hv₂ hp hq hd hcons _ _ =>
    intro Γ' _
    exact HasType.tmergev hv₁ hv₂ hp hq hd hcons
  | tmergevc hv₁ hv₂ hp hq hv' ht' hc₁ hc₂ hcons _ _ _ =>
    intro Γ' _
    exact HasType.tmergevc hv₁ hv₂ hp hq hv' ht' hc₁ hc₂ hcons
  | tlam _ _ _ => intro _ hv; nomatch hv
  | tclos hv' henv hd hb hs₁ hs₂ _ _ =>
    intro Γ' _
    exact HasType.tclos hv' henv hd hb hs₁ hs₂
  | tinl _ ih => intro _ hv; cases hv with | vinl hv' => exact HasType.tinl (ih hv')
  | tinr _ ih => intro _ hv; cases hv with | vinr hv' => exact HasType.tinr (ih hv')
  | tcase _ _ _ _ _ _ _ _ => intro _ hv; nomatch hv
  | tfold _ ih => intro _ hv; cases hv with | vfold hv' => exact HasType.tfold (ih hv')
  | tunfold _ _ _ => intro _ hv; nomatch hv
  | tflam _ _ _ _ => intro _ hv; nomatch hv
  | tfclos hv' henv hd₁ hd₂ hb hs₁ hs₂ hs₃ _ _ =>
    intro Γ' _
    exact HasType.tfclos hv' henv hd₁ hd₂ hb hs₁ hs₂ hs₃
  | tanno _ _ _ => intro _ hv; nomatch hv
  | twrap hΔ hv' hp _ => intro Γ' _; exact HasType.twrap hΔ hv' hp
  | tseal _ _ _ _ _ => intro _ hv; nomatch hv
  | tunseal _ _ _ _ _ _ => intro _ hv; nomatch hv

-- Eᵢ Lemma 6: determinism of casting for well-typed values.  The merge overlap
-- (cmrgl vs cmrgr) is resolved by disjointness of branches (tmrg) or the consistency
-- premise (tmergev).
theorem cast_determinism {v : Exp} {A : Typ} {w₁ : Exp} (c₁ : Cast v A w₁)
    : ∀ {Γ C : Typ}, Value v → HasType Δ Γ v C → ∀ {w₂ : Exp}, Cast v A w₂ → w₁ = w₂ := by
  induction c₁ with
  | cint =>
    intro _ _ _ _ _ c₂
    cases c₂
    rfl
  | ctop =>
    intro _ _ _ _ _ c₂
    cases c₂ with
    | ctop => rfl
    | cmrgl hord _ => nomatch hord
    | cmrgr hord _ => nomatch hord
  | carrow hntl _ _ =>
    intro _ _ _ _ _ c₂
    cases c₂ with
    | carrow _ _ _ => rfl
    | carrowtl htl _ _ => exact absurd htl hntl
  | carrowtl htl _ _ =>
    intro _ _ _ _ _ c₂
    cases c₂ with
    | carrow hntl _ _ => exact absurd htl hntl
    | carrowtl _ _ _ => rfl
  | cinl hc ih =>
    intro Γ C hv ht w₂ c₂
    cases hv with | vinl hv' =>
    cases c₂ with
    | cinl hc₂ =>
      cases ht with
      | tinl hp => rw [ih hv' hp hc₂]
  | cinr hc ih =>
    intro Γ C hv ht w₂ c₂
    cases hv with | vinr hv' =>
    cases c₂ with
    | cinr hc₂ =>
      cases ht with
      | tinr hp => rw [ih hv' hp hc₂]
  | cfold =>
    intro _ _ _ _ _ c₂
    cases c₂
    rfl
  | cfarrow hntl _ _ =>
    intro _ _ _ _ _ c₂
    cases c₂ with
    | cfarrow _ _ _ => rfl
    | cfarrowtl htl _ _ => exact absurd htl hntl
  | cfarrowtl htl _ _ =>
    intro _ _ _ _ _ c₂
    cases c₂ with
    | cfarrow hntl _ _ => exact absurd htl hntl
    | cfarrowtl _ _ _ => rfl
  | cwrap =>
    intro _ _ _ _ _ c₂
    cases c₂
    rfl
  | cmrgl hord hc ih =>
    intro Γ C hv ht w₂ c₂
    cases hv with | vmrg hv₁ hv₂ =>
    cases c₂ with
    | cmrgl _ hc₂ =>
      cases ht with
      | tmrg hp _ _ _ => exact ih hv₁ hp hc₂
      | tmergev _ _ hp _ _ _ => exact ih hv₁ hp hc₂
      | tmergevc _ _ hp _ _ _ _ _ _ => exact ih hv₁ hp hc₂
    | cmrgr _ hc₂ =>
      cases ht with
      | tmrg hp hq _ hd₂ => exact disjoint_consistent hv₁ hv₂ hp hq hd₂ hc hc₂
      | tmergev _ _ _ _ _ hcons => exact hcons hc hc₂
      | tmergevc _ _ _ _ _ _ _ _ hcons => exact hcons hc hc₂
    | cand _ _ => nomatch hord
    | ctop => nomatch hord
  | cmrgr hord hc ih =>
    intro Γ C hv ht w₂ c₂
    cases hv with | vmrg hv₁ hv₂ =>
    cases c₂ with
    | cmrgr _ hc₂ =>
      cases ht with
      | tmrg _ hq _ _ => exact ih hv₂ hq hc₂
      | tmergev _ _ _ hq _ _ => exact ih hv₂ hq hc₂
      | tmergevc _ _ _ hq _ _ _ _ _ => exact ih hv₂ hq hc₂
    | cmrgl _ hc₂ =>
      cases ht with
      | tmrg hp hq _ hd₂ => exact (disjoint_consistent hv₁ hv₂ hp hq hd₂ hc₂ hc).symm
      | tmergev _ _ _ _ _ hcons => exact (hcons hc₂ hc).symm
      | tmergevc _ _ _ _ _ _ _ _ hcons => exact (hcons hc₂ hc).symm
    | cand _ _ => nomatch hord
    | ctop => nomatch hord
  | cand _ _ ih₁ ih₂ =>
    intro Γ C hv ht w₂ c₂
    cases c₂ with
    | cand d₁ d₂ => rw [ih₁ hv ht d₁, ih₂ hv ht d₂]
    | cmrgl hord _ => nomatch hord
    | cmrgr hord _ => nomatch hord
  | crcd _ ih =>
    intro Γ C hv ht w₂ c₂
    cases hv with | vrcd hv' =>
    cases c₂ with
    | crcd d =>
      cases ht with
      | trcd hp => rw [ih hv' hp d]

-- Transitivity of casting (Eᵢ Lemma 10), via shape-directed helpers so the recursion
-- stays structural on the second cast.
theorem cast_trans_int : {v : Exp} → {A : Typ} → {i : Nat}
    → Cast v A (.lit i) → Cast v .int (.lit i)
  | _, _, _, .cint => .cint
  | _, _, _, .cmrgl _ h => .cmrgl .oint (cast_trans_int h)
  | _, _, _, .cmrgr _ h => .cmrgr .oint (cast_trans_int h)

theorem cast_trans_rcd : {v : Exp} → {A : Typ} → {l : String} → {u : Exp} → {B' : Typ}
    → {u' : Exp} → Cast v A (.lrec l u)
    → (∀ {v' : Exp} {A' : Typ}, Cast v' A' u → Cast v' B' u')
    → Cast v (.rcd l B') (.lrec l u')
  | _, _, _, _, _, _, .crcd h, k => .crcd (k h)
  | _, _, _, _, _, _, .cmrgl _ h, k => .cmrgl .orcd (cast_trans_rcd h k)
  | _, _, _, _, _, _, .cmrgr _ h, k => .cmrgr .orcd (cast_trans_rcd h k)

theorem cast_trans_arrow : {v : Exp} → {A : Typ} → {u : Exp} → {A₀ B₀ : Typ} → {e : Exp}
    → Cast v A (.clos u A₀ B₀ e)
    → ∀ {C' D' : Typ}, ¬ TopLike D' → Sub C' A₀ → Sub B₀ D'
    → Cast v (.arr C' D') (.clos u A₀ D' e)
  | _, _, _, _, _, _, .carrow _ _ hsB, _, _, hntl', hsC', hsB' =>
    .carrow hntl' hsC' (sub_trans hsB hsB')
  | _, _, _, _, _, _, .carrowtl htl _ _, _, _, hntl', _, hsB' =>
    absurd (sub_toplike htl hsB') hntl'
  | _, _, _, _, _, _, .cfarrowtl htl _ _, _, _, hntl', _, hsB' =>
    absurd (sub_toplike htl hsB') hntl'
  | _, _, _, _, _, _, .cmrgl _ h, _, _, hntl', hsC', hsB' =>
    .cmrgl .oarr (cast_trans_arrow h hntl' hsC' hsB')
  | _, _, _, _, _, _, .cmrgr _ h, _, _, hntl', hsC', hsB' =>
    .cmrgr .oarr (cast_trans_arrow h hntl' hsC' hsB')

theorem cast_trans_arrowtl : {v : Exp} → {A : Typ} → {u : Exp} → {A₀ B₀ : Typ} → {e : Exp}
    → Cast v A (.clos u A₀ B₀ e)
    → ∀ {C' D' : Typ}, TopLike D' → Sub C' A₀ → Sub B₀ D'
    → Cast v (.arr C' D') (.clos .unit C' D' (genVal D'))
  | _, _, _, _, _, _, .carrow _ _ hsB, _, _, htl', hsC', hsB' =>
    .carrowtl htl' hsC' (sub_trans hsB hsB')
  | _, _, _, _, _, _, .carrowtl _ hsC hsB, _, _, htl', hsC', hsB' =>
    .carrowtl htl' (sub_trans hsC' hsC) (sub_trans hsB hsB')
  | _, _, _, _, _, _, .cfarrowtl _ hsC hsB, _, _, htl', hsC', hsB' =>
    .cfarrowtl htl' (sub_trans hsC' hsC) (sub_trans hsB hsB')
  | _, _, _, _, _, _, .cmrgl _ h, _, _, htl', hsC', hsB' =>
    .cmrgl .oarr (cast_trans_arrowtl h htl' hsC' hsB')
  | _, _, _, _, _, _, .cmrgr _ h, _, _, htl', hsC', hsB' =>
    .cmrgr .oarr (cast_trans_arrowtl h htl' hsC' hsB')

theorem cast_trans_farrow : {v : Exp} → {A : Typ} → {u : Exp} → {A₀ B₀ Bx₀ : Typ} → {e : Exp}
    → Cast v A (.fclos u A₀ B₀ Bx₀ e)
    → ∀ {C' D' : Typ}, ¬ TopLike D' → Sub C' A₀ → Sub Bx₀ D'
    → Cast v (.arr C' D') (.fclos u A₀ B₀ D' e)
  | _, _, _, _, _, _, _, .cfarrow _ _ hsB, _, _, hntl', hsC', hsB' =>
    .cfarrow hntl' hsC' (sub_trans hsB hsB')
  | _, _, _, _, _, _, _, .cmrgl _ h, _, _, hntl', hsC', hsB' =>
    .cmrgl .oarr (cast_trans_farrow h hntl' hsC' hsB')
  | _, _, _, _, _, _, _, .cmrgr _ h, _, _, hntl', hsC', hsB' =>
    .cmrgr .oarr (cast_trans_farrow h hntl' hsC' hsB')

theorem cast_trans_farrowtl : {v : Exp} → {A : Typ} → {u : Exp} → {A₀ B₀ Bx₀ : Typ} → {e : Exp}
    → Cast v A (.fclos u A₀ B₀ Bx₀ e)
    → ∀ {C' D' : Typ}, TopLike D' → Sub C' A₀ → Sub Bx₀ D'
    → Cast v (.arr C' D') (.clos .unit C' D' (genVal D'))
  | _, _, _, _, _, _, _, .cfarrow _ _ hsB, _, _, htl', hsC', hsB' =>
    .cfarrowtl htl' hsC' (sub_trans hsB hsB')
  | _, _, _, _, _, _, _, .cmrgl _ h, _, _, htl', hsC', hsB' =>
    .cmrgl .oarr (cast_trans_farrowtl h htl' hsC' hsB')
  | _, _, _, _, _, _, _, .cmrgr _ h, _, _, htl', hsC', hsB' =>
    .cmrgr .oarr (cast_trans_farrowtl h htl' hsC' hsB')

theorem cast_trans_inl : {v : Exp} → {A Bt : Typ} → {u : Exp} → {A' B' : Typ} → {u' : Exp}
    → Cast v A (.inl Bt u)
    → (∀ {v' : Exp} {A'' : Typ}, Cast v' A'' u → Cast v' A' u')
    → Cast v (.or A' B') (.inl B' u')
  | _, _, _, _, _, _, _, .cinl h, k => .cinl (k h)
  | _, _, _, _, _, _, _, .cmrgl _ h, k => .cmrgl .oor (cast_trans_inl h k)
  | _, _, _, _, _, _, _, .cmrgr _ h, k => .cmrgr .oor (cast_trans_inl h k)

theorem cast_trans_inr : {v : Exp} → {A At : Typ} → {u : Exp} → {A' B' : Typ} → {u' : Exp}
    → Cast v A (.inr At u)
    → (∀ {v' : Exp} {A'' : Typ}, Cast v' A'' u → Cast v' B' u')
    → Cast v (.or A' B') (.inr A' u')
  | _, _, _, _, _, _, _, .cinr h, k => .cinr (k h)
  | _, _, _, _, _, _, _, .cmrgl _ h, k => .cmrgl .oor (cast_trans_inr h k)
  | _, _, _, _, _, _, _, .cmrgr _ h, k => .cmrgr .oor (cast_trans_inr h k)

theorem cast_trans_wrap : {v : Exp} → {A : Typ} → {n : Nat} → {u : Exp}
    → Cast v A (.wrap n u) → Cast v (.brand n) (.wrap n u)
  | _, _, _, _, .cwrap => .cwrap
  | _, _, _, _, .cmrgl _ h => .cmrgl .obrand (cast_trans_wrap h)
  | _, _, _, _, .cmrgr _ h => .cmrgr .obrand (cast_trans_wrap h)

theorem cast_trans_fold : {v : Exp} → {A : Typ} → {T : Typ} → {u : Exp}
    → Cast v A (.fold T u) → Cast v (.mu T) (.fold T u)
  | _, _, _, _, .cfold => .cfold
  | _, _, _, _, .cmrgl _ h => .cmrgl .omu (cast_trans_fold h)
  | _, _, _, _, .cmrgr _ h => .cmrgr .omu (cast_trans_fold h)

theorem cast_trans_mrgl : {v : Exp} → {A : Typ} → {x y : Exp}
    → Cast v A (.mrg x y)
    → ∀ {B : Typ} {v₂ : Exp}, Ordinary B
    → (∀ {v' : Exp} {A' : Typ}, Cast v' A' x → Cast v' B v₂)
    → Cast v B v₂
  | _, _, _, _, .cand f₁ _, _, _, _, k => k f₁
  | _, _, _, _, .cmrgl _ h, _, _, hord, k => .cmrgl hord (cast_trans_mrgl h hord k)
  | _, _, _, _, .cmrgr _ h, _, _, hord, k => .cmrgr hord (cast_trans_mrgl h hord k)

theorem cast_trans_mrgr : {v : Exp} → {A : Typ} → {x y : Exp}
    → Cast v A (.mrg x y)
    → ∀ {B : Typ} {v₂ : Exp}, Ordinary B
    → (∀ {v' : Exp} {A' : Typ}, Cast v' A' y → Cast v' B v₂)
    → Cast v B v₂
  | _, _, _, _, .cand _ f₂, _, _, _, k => k f₂
  | _, _, _, _, .cmrgl _ h, _, _, hord, k => .cmrgl hord (cast_trans_mrgr h hord k)
  | _, _, _, _, .cmrgr _ h, _, _, hord, k => .cmrgr hord (cast_trans_mrgr h hord k)

theorem cast_trans : {v : Exp} → {A : Typ} → {v₁ : Exp} → {B : Typ} → {v₂ : Exp}
    → Cast v A v₁ → Cast v₁ B v₂ → Cast v B v₂
  | _, _, _, _, _, _, .ctop => .ctop
  | _, _, _, _, _, f, .cint => cast_trans_int f
  | _, _, _, _, _, f, .cand s₁ s₂ => .cand (cast_trans f s₁) (cast_trans f s₂)
  | _, _, _, _, _, f, .crcd s => cast_trans_rcd f (fun f' => cast_trans f' s)
  | _, _, _, _, _, f, .carrow hntl hsC hsB => cast_trans_arrow f hntl hsC hsB
  | _, _, _, _, _, f, .carrowtl htl hsC hsB => cast_trans_arrowtl f htl hsC hsB
  | _, _, _, _, _, f, .cmrgl hord s => cast_trans_mrgl f hord (fun f' => cast_trans f' s)
  | _, _, _, _, _, f, .cmrgr hord s => cast_trans_mrgr f hord (fun f' => cast_trans f' s)
  | _, _, _, _, _, f, .cwrap => cast_trans_wrap f
  | _, _, _, _, _, f, .cfarrow hntl hsC hsB => cast_trans_farrow f hntl hsC hsB
  | _, _, _, _, _, f, .cfarrowtl htl hsC hsB => cast_trans_farrowtl f htl hsC hsB
  | _, _, _, _, _, f, .cinl s => cast_trans_inl f (fun f' => cast_trans f' s)
  | _, _, _, _, _, f, .cinr s => cast_trans_inr f (fun f' => cast_trans f' s)
  | _, _, _, _, _, f, .cfold => cast_trans_fold f

-- Eᵢ Lemma 11: the results of casting one well-typed value are consistent.
theorem consistent_after_cast {v : Exp} {Γ C A B : Typ} {v₁ v₂ : Exp}
    (hv : Value v) (ht : HasType Δ Γ v C) (c₁ : Cast v A v₁) (c₂ : Cast v B v₂)
    : Consistent v₁ v₂ := by
  intro T w₁ w₂ d₁ d₂
  exact cast_determinism (cast_trans c₁ d₁) hv ht (cast_trans c₂ d₂)

-- Eᵢ Lemma 12: casting preserves types — the result inhabits the cast type.
theorem cast_preservation : {v : Exp} → {A : Typ} → {w : Exp} → Cast v A w
    → ∀ {Γ B : Typ}, Value v → HasType Δ Γ v B → HasType Δ Γ w A
  | _, _, _, .cint => by
    intro _ ht
    cases ht
    exact HasType.tint
  | _, _, _, .ctop => by
    intro _ _
    exact HasType.tunit
  | _, _, _, .carrow _ hsC hsB => by
    intro _ ht
    cases ht with
    | tclos hv' henv hd hb hs₁ _ =>
      exact HasType.tclos hv' henv hd hb (sub_trans hs₁ hsB) hsC
  | _, _, _, .carrowtl htl _ _ => by
    intro _ _
    exact HasType.tclos Value.vunit HasType.tunit disj_top
      (genVal_typed htl (.and .top _)) (sub_refl _) (sub_refl _)
  | _, _, _, .cmrgl _ hc => by
    intro hv ht
    cases hv with | vmrg hv₁ hv₂ =>
    cases ht with
    | tmrg hp _ _ _ => exact cast_preservation hc hv₁ hp
    | tmergev _ _ hp _ _ _ =>
      exact value_weaken (cast_preservation hc hv₁ hp) (cast_value hv₁ hc)
    | tmergevc _ _ hp _ _ _ _ _ _ =>
      exact value_weaken (cast_preservation hc hv₁ hp) (cast_value hv₁ hc)
  | _, _, _, .cmrgr _ hc => by
    intro hv ht
    cases hv with | vmrg hv₁ hv₂ =>
    cases ht with
    | tmrg _ hq _ _ =>
      exact value_weaken (cast_preservation hc hv₂ hq) (cast_value hv₂ hc)
    | tmergev _ _ _ hq _ _ =>
      exact value_weaken (cast_preservation hc hv₂ hq) (cast_value hv₂ hc)
    | tmergevc _ _ _ hq _ _ _ _ _ =>
      exact value_weaken (cast_preservation hc hv₂ hq) (cast_value hv₂ hc)
  | _, _, _, .cand hc₁ hc₂ => by
    intro hv ht
    -- The components are the two casts of the common origin v — the tmergevc shape;
    -- their types need not be disjoint (casting at Int & Int duplicates).
    exact HasType.tmergevc (cast_value hv hc₁) (cast_value hv hc₂)
      (value_weaken (cast_preservation hc₁ hv ht) (cast_value hv hc₁))
      (value_weaken (cast_preservation hc₂ hv ht) (cast_value hv hc₂))
      hv (value_weaken ht hv) hc₁ hc₂
      (consistent_after_cast hv ht hc₁ hc₂)
  | _, _, _, .crcd hc => by
    intro hv ht
    cases hv with | vrcd hv' =>
    cases ht with
    | trcd hp => exact HasType.trcd (cast_preservation hc hv' hp)
  | _, _, _, .cwrap => by
    intro _ ht
    cases ht with
    | twrap hΔ hv' hp => exact HasType.twrap hΔ hv' hp
  | _, _, _, .cinl hc => by
    intro hv ht
    cases hv with | vinl hv' =>
    cases ht with
    | tinl hp => exact HasType.tinl (cast_preservation hc hv' hp)
  | _, _, _, .cinr hc => by
    intro hv ht
    cases hv with | vinr hv' =>
    cases ht with
    | tinr hp => exact HasType.tinr (cast_preservation hc hv' hp)
  | _, _, _, .cfold => by
    intro _ ht
    cases ht with
    | tfold hp => exact HasType.tfold hp
  | _, _, _, .cfarrow _ hsC hsB => by
    intro _ ht
    cases ht with
    | tfclos hv' henv hd₁ hd₂ hb hs₁ hs₂ _ =>
      exact HasType.tfclos hv' henv hd₁ hd₂ hb hs₁ (sub_trans hs₂ hsB) hsC
  | _, _, _, .cfarrowtl htl _ _ => by
    intro _ _
    exact HasType.tclos Value.vunit HasType.tunit disj_top
      (genVal_typed htl (.and .top _)) (sub_refl _) (sub_refl _)

-- Eᵢ Lemma 9: a well-typed value casts at any supertype of its type.
theorem cast_progress {A : Typ}
    : ∀ {v : Exp} {Γ B : Typ}, Value v → HasType Δ Γ v B → Sub B A → ∃ w, Cast v A w := by
  induction A with
  | top =>
    intro v Γ B _ _ _
    exact ⟨.unit, Cast.ctop⟩
  | and A₁ A₂ ih₁ ih₂ =>
    intro v Γ B hv ht hs
    obtain ⟨w₁, hc₁⟩ := ih₁ hv ht (sub_and_inv_l hs)
    obtain ⟨w₂, hc₂⟩ := ih₂ hv ht (sub_and_inv_r hs)
    exact ⟨.mrg w₁ w₂, Cast.cand hc₁ hc₂⟩
  | int =>
    intro v Γ B hv ht hs
    revert hv hs
    induction ht with
    | tquery => intro hv _; nomatch hv
    | tint => intro _ _; exact ⟨_, Cast.cint⟩
    | tunit => intro _ hs; nomatch hs
    | tapp _ _ _ _ => intro hv _; nomatch hv
    | tbox _ _ _ _ => intro hv _; nomatch hv
    | tproj _ _ _ => intro hv _; nomatch hv
    | trcd _ _ => intro _ hs; nomatch hs
    | trproj _ _ _ => intro hv _; nomatch hv
    | tmrg _ _ _ _ ih₁ ih₂ =>
      intro hv hs
      cases hv with | vmrg hv₁ hv₂ =>
      cases hs with
      | sandl hs' =>
        obtain ⟨w, hc⟩ := ih₁ hv₁ hs'
        exact ⟨w, Cast.cmrgl Ordinary.oint hc⟩
      | sandr hs' =>
        obtain ⟨w, hc⟩ := ih₂ hv₂ hs'
        exact ⟨w, Cast.cmrgr Ordinary.oint hc⟩
    | tmergev _ _ _ _ _ _ ih₁ ih₂ =>
      intro hv hs
      cases hv with | vmrg hv₁ hv₂ =>
      cases hs with
      | sandl hs' =>
        obtain ⟨w, hc⟩ := ih₁ hv₁ hs'
        exact ⟨w, Cast.cmrgl Ordinary.oint hc⟩
      | sandr hs' =>
        obtain ⟨w, hc⟩ := ih₂ hv₂ hs'
        exact ⟨w, Cast.cmrgr Ordinary.oint hc⟩
    | tmergevc _ _ _ _ _ _ _ _ _ ih₁ ih₂ _ =>
      intro hv hs
      cases hv with | vmrg hv₁ hv₂ =>
      cases hs with
      | sandl hs' =>
        obtain ⟨w, hc⟩ := ih₁ hv₁ hs'
        exact ⟨w, Cast.cmrgl Ordinary.oint hc⟩
      | sandr hs' =>
        obtain ⟨w, hc⟩ := ih₂ hv₂ hs'
        exact ⟨w, Cast.cmrgr Ordinary.oint hc⟩
    | tlam _ _ _ => intro hv _; nomatch hv
    | tclos _ _ _ _ _ _ _ _ => intro _ hs; nomatch hs
    | tanno _ _ _ => intro hv _; nomatch hv
    | twrap _ _ _ _ => intro _ hs; nomatch hs
    | tseal _ _ _ _ _ => intro hv _; nomatch hv
    | tunseal _ _ _ _ _ _ => intro hv _; nomatch hv
    | tinl _ _ => intro _ hs; nomatch hs
    | tinr _ _ => intro _ hs; nomatch hs
    | tcase _ _ _ _ _ _ _ _ => intro hv _; nomatch hv
    | tfold _ _ => intro _ hs; nomatch hs
    | tunfold _ _ _ => intro hv _; nomatch hv
    | tflam _ _ _ _ => intro hv _; nomatch hv
    | tfclos _ _ _ _ _ _ _ _ _ _ => intro _ hs; nomatch hs
  | brand n =>
    intro v Γ B hv ht hs
    revert hv hs
    induction ht with
    | tquery => intro hv _; nomatch hv
    | tint => intro _ hs; nomatch hs
    | tunit => intro _ hs; nomatch hs
    | tapp _ _ _ _ => intro hv _; nomatch hv
    | tbox _ _ _ _ => intro hv _; nomatch hv
    | tproj _ _ _ => intro hv _; nomatch hv
    | trcd _ _ => intro _ hs; nomatch hs
    | trproj _ _ _ => intro hv _; nomatch hv
    | tmrg _ _ _ _ ih₁ ih₂ =>
      intro hv hs
      cases hv with | vmrg hv₁ hv₂ =>
      cases hs with
      | sandl hs' =>
        obtain ⟨w, hc⟩ := ih₁ hv₁ hs'
        exact ⟨w, Cast.cmrgl Ordinary.obrand hc⟩
      | sandr hs' =>
        obtain ⟨w, hc⟩ := ih₂ hv₂ hs'
        exact ⟨w, Cast.cmrgr Ordinary.obrand hc⟩
    | tmergev _ _ _ _ _ _ ih₁ ih₂ =>
      intro hv hs
      cases hv with | vmrg hv₁ hv₂ =>
      cases hs with
      | sandl hs' =>
        obtain ⟨w, hc⟩ := ih₁ hv₁ hs'
        exact ⟨w, Cast.cmrgl Ordinary.obrand hc⟩
      | sandr hs' =>
        obtain ⟨w, hc⟩ := ih₂ hv₂ hs'
        exact ⟨w, Cast.cmrgr Ordinary.obrand hc⟩
    | tmergevc _ _ _ _ _ _ _ _ _ ih₁ ih₂ _ =>
      intro hv hs
      cases hv with | vmrg hv₁ hv₂ =>
      cases hs with
      | sandl hs' =>
        obtain ⟨w, hc⟩ := ih₁ hv₁ hs'
        exact ⟨w, Cast.cmrgl Ordinary.obrand hc⟩
      | sandr hs' =>
        obtain ⟨w, hc⟩ := ih₂ hv₂ hs'
        exact ⟨w, Cast.cmrgr Ordinary.obrand hc⟩
    | tlam _ _ _ => intro hv _; nomatch hv
    | tclos _ _ _ _ _ _ _ _ => intro _ hs; nomatch hs
    | tanno _ _ _ => intro hv _; nomatch hv
    | twrap _ _ _ _ =>
      intro _ hs
      cases hs with
      | sbrand => exact ⟨_, Cast.cwrap⟩
    | tseal _ _ _ _ _ => intro hv _; nomatch hv
    | tunseal _ _ _ _ _ _ => intro hv _; nomatch hv
    | tinl _ _ => intro _ hs; nomatch hs
    | tinr _ _ => intro _ hs; nomatch hs
    | tcase _ _ _ _ _ _ _ _ => intro hv _; nomatch hv
    | tfold _ _ => intro _ hs; nomatch hs
    | tunfold _ _ _ => intro hv _; nomatch hv
    | tflam _ _ _ _ => intro hv _; nomatch hv
    | tfclos _ _ _ _ _ _ _ _ _ _ => intro _ hs; nomatch hs
  | arr C D _ _ =>
    intro v Γ B hv ht hs
    revert hv hs
    induction ht with
    | tquery => intro hv _; nomatch hv
    | tint => intro _ hs; nomatch hs
    | tunit => intro _ hs; nomatch hs
    | tapp _ _ _ _ => intro hv _; nomatch hv
    | tbox _ _ _ _ => intro hv _; nomatch hv
    | tproj _ _ _ => intro hv _; nomatch hv
    | trcd _ _ => intro _ hs; nomatch hs
    | trproj _ _ _ => intro hv _; nomatch hv
    | tmrg _ _ _ _ ih₁ ih₂ =>
      intro hv hs
      cases hv with | vmrg hv₁ hv₂ =>
      cases hs with
      | sandl hs' =>
        obtain ⟨w, hc⟩ := ih₁ hv₁ hs'
        exact ⟨w, Cast.cmrgl Ordinary.oarr hc⟩
      | sandr hs' =>
        obtain ⟨w, hc⟩ := ih₂ hv₂ hs'
        exact ⟨w, Cast.cmrgr Ordinary.oarr hc⟩
    | tmergev _ _ _ _ _ _ ih₁ ih₂ =>
      intro hv hs
      cases hv with | vmrg hv₁ hv₂ =>
      cases hs with
      | sandl hs' =>
        obtain ⟨w, hc⟩ := ih₁ hv₁ hs'
        exact ⟨w, Cast.cmrgl Ordinary.oarr hc⟩
      | sandr hs' =>
        obtain ⟨w, hc⟩ := ih₂ hv₂ hs'
        exact ⟨w, Cast.cmrgr Ordinary.oarr hc⟩
    | tmergevc _ _ _ _ _ _ _ _ _ ih₁ ih₂ _ =>
      intro hv hs
      cases hv with | vmrg hv₁ hv₂ =>
      cases hs with
      | sandl hs' =>
        obtain ⟨w, hc⟩ := ih₁ hv₁ hs'
        exact ⟨w, Cast.cmrgl Ordinary.oarr hc⟩
      | sandr hs' =>
        obtain ⟨w, hc⟩ := ih₂ hv₂ hs'
        exact ⟨w, Cast.cmrgr Ordinary.oarr hc⟩
    | tlam _ _ _ => intro hv _; nomatch hv
    | tclos _ _ _ _ _ hs₂ _ _ =>
      intro _ hs
      cases hs with
      | sarr hsC hsD =>
        cases toplike_dec D with
        | inl htl => exact ⟨_, Cast.carrowtl htl (sub_trans hsC hs₂) hsD⟩
        | inr hntl => exact ⟨_, Cast.carrow hntl (sub_trans hsC hs₂) hsD⟩
    | tanno _ _ _ => intro hv _; nomatch hv
    | twrap _ _ _ _ => intro _ hs; nomatch hs
    | tseal _ _ _ _ _ => intro hv _; nomatch hv
    | tunseal _ _ _ _ _ _ => intro hv _; nomatch hv
    | tinl _ _ => intro _ hs; nomatch hs
    | tinr _ _ => intro _ hs; nomatch hs
    | tcase _ _ _ _ _ _ _ _ => intro hv _; nomatch hv
    | tfold _ _ => intro _ hs; nomatch hs
    | tunfold _ _ _ => intro hv _; nomatch hv
    | tflam _ _ _ _ => intro hv _; nomatch hv
    | tfclos _ _ _ _ _ _ _ hs₃ _ _ =>
      intro _ hs
      cases hs with
      | sarr hsC hsD =>
        cases toplike_dec D with
        | inl htl => exact ⟨_, Cast.cfarrowtl htl (sub_trans hsC hs₃) hsD⟩
        | inr hntl => exact ⟨_, Cast.cfarrow hntl (sub_trans hsC hs₃) hsD⟩
  | rcd l A' ihA' =>
    intro v Γ B hv ht hs
    revert hv hs
    induction ht with
    | tquery => intro hv _; nomatch hv
    | tint => intro _ hs; nomatch hs
    | tunit => intro _ hs; nomatch hs
    | tapp _ _ _ _ => intro hv _; nomatch hv
    | tbox _ _ _ _ => intro hv _; nomatch hv
    | tproj _ _ _ => intro hv _; nomatch hv
    | trcd hp _ =>
      intro hv hs
      cases hv with | vrcd hv' =>
      cases hs with
      | srcd hs' =>
        obtain ⟨w', hc'⟩ := ihA' hv' hp hs'
        exact ⟨.lrec l w', Cast.crcd hc'⟩
    | trproj _ _ _ => intro hv _; nomatch hv
    | tmrg _ _ _ _ ih₁ ih₂ =>
      intro hv hs
      cases hv with | vmrg hv₁ hv₂ =>
      cases hs with
      | sandl hs' =>
        obtain ⟨w, hc⟩ := ih₁ hv₁ hs'
        exact ⟨w, Cast.cmrgl Ordinary.orcd hc⟩
      | sandr hs' =>
        obtain ⟨w, hc⟩ := ih₂ hv₂ hs'
        exact ⟨w, Cast.cmrgr Ordinary.orcd hc⟩
    | tmergev _ _ _ _ _ _ ih₁ ih₂ =>
      intro hv hs
      cases hv with | vmrg hv₁ hv₂ =>
      cases hs with
      | sandl hs' =>
        obtain ⟨w, hc⟩ := ih₁ hv₁ hs'
        exact ⟨w, Cast.cmrgl Ordinary.orcd hc⟩
      | sandr hs' =>
        obtain ⟨w, hc⟩ := ih₂ hv₂ hs'
        exact ⟨w, Cast.cmrgr Ordinary.orcd hc⟩
    | tmergevc _ _ _ _ _ _ _ _ _ ih₁ ih₂ _ =>
      intro hv hs
      cases hv with | vmrg hv₁ hv₂ =>
      cases hs with
      | sandl hs' =>
        obtain ⟨w, hc⟩ := ih₁ hv₁ hs'
        exact ⟨w, Cast.cmrgl Ordinary.orcd hc⟩
      | sandr hs' =>
        obtain ⟨w, hc⟩ := ih₂ hv₂ hs'
        exact ⟨w, Cast.cmrgr Ordinary.orcd hc⟩
    | tlam _ _ _ => intro hv _; nomatch hv
    | tclos _ _ _ _ _ _ _ _ => intro _ hs; nomatch hs
    | tanno _ _ _ => intro hv _; nomatch hv
    | twrap _ _ _ _ => intro _ hs; nomatch hs
    | tseal _ _ _ _ _ => intro hv _; nomatch hv
    | tunseal _ _ _ _ _ _ => intro hv _; nomatch hv
    | tinl _ _ => intro _ hs; nomatch hs
    | tinr _ _ => intro _ hs; nomatch hs
    | tcase _ _ _ _ _ _ _ _ => intro hv _; nomatch hv
    | tfold _ _ => intro _ hs; nomatch hs
    | tunfold _ _ _ => intro hv _; nomatch hv
    | tflam _ _ _ _ => intro hv _; nomatch hv
    | tfclos _ _ _ _ _ _ _ _ _ _ => intro _ hs; nomatch hs
  | or A₁ B₁ ihA₁ ihB₁ =>
    intro v Γ B hv ht hs
    revert hv hs
    induction ht with
    | tquery => intro hv _; nomatch hv
    | tint => intro _ hs; nomatch hs
    | tunit => intro _ hs; nomatch hs
    | tapp _ _ _ _ => intro hv _; nomatch hv
    | tbox _ _ _ _ => intro hv _; nomatch hv
    | tproj _ _ _ => intro hv _; nomatch hv
    | trcd _ _ => intro _ hs; nomatch hs
    | trproj _ _ _ => intro hv _; nomatch hv
    | tmrg _ _ _ _ ihm₁ ihm₂ =>
      intro hv hs
      cases hv with | vmrg hv₁ hv₂ =>
      cases hs with
      | sandl hs' =>
        obtain ⟨w, hc⟩ := ihm₁ hv₁ hs'
        exact ⟨w, Cast.cmrgl Ordinary.oor hc⟩
      | sandr hs' =>
        obtain ⟨w, hc⟩ := ihm₂ hv₂ hs'
        exact ⟨w, Cast.cmrgr Ordinary.oor hc⟩
    | tmergev _ _ _ _ _ _ ihm₁ ihm₂ =>
      intro hv hs
      cases hv with | vmrg hv₁ hv₂ =>
      cases hs with
      | sandl hs' =>
        obtain ⟨w, hc⟩ := ihm₁ hv₁ hs'
        exact ⟨w, Cast.cmrgl Ordinary.oor hc⟩
      | sandr hs' =>
        obtain ⟨w, hc⟩ := ihm₂ hv₂ hs'
        exact ⟨w, Cast.cmrgr Ordinary.oor hc⟩
    | tmergevc _ _ _ _ _ _ _ _ _ ihm₁ ihm₂ _ =>
      intro hv hs
      cases hv with | vmrg hv₁ hv₂ =>
      cases hs with
      | sandl hs' =>
        obtain ⟨w, hc⟩ := ihm₁ hv₁ hs'
        exact ⟨w, Cast.cmrgl Ordinary.oor hc⟩
      | sandr hs' =>
        obtain ⟨w, hc⟩ := ihm₂ hv₂ hs'
        exact ⟨w, Cast.cmrgr Ordinary.oor hc⟩
    | tlam _ _ _ => intro hv _; nomatch hv
    | tclos _ _ _ _ _ _ _ _ => intro _ hs; nomatch hs
    | tanno _ _ _ => intro hv _; nomatch hv
    | twrap _ _ _ _ => intro _ hs; nomatch hs
    | tseal _ _ _ _ _ => intro hv _; nomatch hv
    | tunseal _ _ _ _ _ _ => intro hv _; nomatch hv
    | tflam _ _ _ _ => intro hv _; nomatch hv
    | tfclos _ _ _ _ _ _ _ _ _ _ => intro _ hs; nomatch hs
    | tinl hp _ =>
      intro hv hs
      cases hv with | vinl hv' =>
      cases hs with
      | sor hs₁ _ =>
        obtain ⟨w, hc⟩ := ihA₁ hv' hp hs₁
        exact ⟨.inl B₁ w, Cast.cinl hc⟩
    | tinr hp _ =>
      intro hv hs
      cases hv with | vinr hv' =>
      cases hs with
      | sor _ hs₂ =>
        obtain ⟨w, hc⟩ := ihB₁ hv' hp hs₂
        exact ⟨.inr A₁ w, Cast.cinr hc⟩
    | tcase _ _ _ _ _ _ _ _ => intro hv _; nomatch hv
    | tfold _ _ => intro _ hs; nomatch hs
    | tunfold _ _ _ => intro hv _; nomatch hv
  | var m =>
    intro v Γ B hv ht hs
    revert hv hs
    induction ht with
    | tquery => intro hv _; nomatch hv
    | tint => intro _ hs; nomatch hs
    | tunit => intro _ hs; nomatch hs
    | tapp _ _ _ _ => intro hv _; nomatch hv
    | tbox _ _ _ _ => intro hv _; nomatch hv
    | tproj _ _ _ => intro hv _; nomatch hv
    | trcd _ _ => intro _ hs; nomatch hs
    | trproj _ _ _ => intro hv _; nomatch hv
    | tmrg _ _ _ _ ihm₁ ihm₂ =>
      intro hv hs
      cases hv with | vmrg hv₁ hv₂ =>
      cases hs with
      | sandl hs' =>
        obtain ⟨w, hc⟩ := ihm₁ hv₁ hs'
        exact ⟨w, Cast.cmrgl Ordinary.ovar hc⟩
      | sandr hs' =>
        obtain ⟨w, hc⟩ := ihm₂ hv₂ hs'
        exact ⟨w, Cast.cmrgr Ordinary.ovar hc⟩
    | tmergev _ _ _ _ _ _ ihm₁ ihm₂ =>
      intro hv hs
      cases hv with | vmrg hv₁ hv₂ =>
      cases hs with
      | sandl hs' =>
        obtain ⟨w, hc⟩ := ihm₁ hv₁ hs'
        exact ⟨w, Cast.cmrgl Ordinary.ovar hc⟩
      | sandr hs' =>
        obtain ⟨w, hc⟩ := ihm₂ hv₂ hs'
        exact ⟨w, Cast.cmrgr Ordinary.ovar hc⟩
    | tmergevc _ _ _ _ _ _ _ _ _ ihm₁ ihm₂ _ =>
      intro hv hs
      cases hv with | vmrg hv₁ hv₂ =>
      cases hs with
      | sandl hs' =>
        obtain ⟨w, hc⟩ := ihm₁ hv₁ hs'
        exact ⟨w, Cast.cmrgl Ordinary.ovar hc⟩
      | sandr hs' =>
        obtain ⟨w, hc⟩ := ihm₂ hv₂ hs'
        exact ⟨w, Cast.cmrgr Ordinary.ovar hc⟩
    | tlam _ _ _ => intro hv _; nomatch hv
    | tclos _ _ _ _ _ _ _ _ => intro _ hs; nomatch hs
    | tanno _ _ _ => intro hv _; nomatch hv
    | twrap _ _ _ _ => intro _ hs; nomatch hs
    | tseal _ _ _ _ _ => intro hv _; nomatch hv
    | tunseal _ _ _ _ _ _ => intro hv _; nomatch hv
    | tflam _ _ _ _ => intro hv _; nomatch hv
    | tfclos _ _ _ _ _ _ _ _ _ _ => intro _ hs; nomatch hs
    | tinl _ _ => intro _ hs; nomatch hs
    | tinr _ _ => intro _ hs; nomatch hs
    | tcase _ _ _ _ _ _ _ _ => intro hv _; nomatch hv
    | tfold _ _ => intro _ hs; nomatch hs
    | tunfold _ _ _ => intro hv _; nomatch hv
  | mu T _ =>
    intro v Γ B hv ht hs
    revert hv hs
    induction ht with
    | tquery => intro hv _; nomatch hv
    | tint => intro _ hs; nomatch hs
    | tunit => intro _ hs; nomatch hs
    | tapp _ _ _ _ => intro hv _; nomatch hv
    | tbox _ _ _ _ => intro hv _; nomatch hv
    | tproj _ _ _ => intro hv _; nomatch hv
    | trcd _ _ => intro _ hs; nomatch hs
    | trproj _ _ _ => intro hv _; nomatch hv
    | tmrg _ _ _ _ ihm₁ ihm₂ =>
      intro hv hs
      cases hv with | vmrg hv₁ hv₂ =>
      cases hs with
      | sandl hs' =>
        obtain ⟨w, hc⟩ := ihm₁ hv₁ hs'
        exact ⟨w, Cast.cmrgl Ordinary.omu hc⟩
      | sandr hs' =>
        obtain ⟨w, hc⟩ := ihm₂ hv₂ hs'
        exact ⟨w, Cast.cmrgr Ordinary.omu hc⟩
    | tmergev _ _ _ _ _ _ ihm₁ ihm₂ =>
      intro hv hs
      cases hv with | vmrg hv₁ hv₂ =>
      cases hs with
      | sandl hs' =>
        obtain ⟨w, hc⟩ := ihm₁ hv₁ hs'
        exact ⟨w, Cast.cmrgl Ordinary.omu hc⟩
      | sandr hs' =>
        obtain ⟨w, hc⟩ := ihm₂ hv₂ hs'
        exact ⟨w, Cast.cmrgr Ordinary.omu hc⟩
    | tmergevc _ _ _ _ _ _ _ _ _ ihm₁ ihm₂ _ =>
      intro hv hs
      cases hv with | vmrg hv₁ hv₂ =>
      cases hs with
      | sandl hs' =>
        obtain ⟨w, hc⟩ := ihm₁ hv₁ hs'
        exact ⟨w, Cast.cmrgl Ordinary.omu hc⟩
      | sandr hs' =>
        obtain ⟨w, hc⟩ := ihm₂ hv₂ hs'
        exact ⟨w, Cast.cmrgr Ordinary.omu hc⟩
    | tlam _ _ _ => intro hv _; nomatch hv
    | tclos _ _ _ _ _ _ _ _ => intro _ hs; nomatch hs
    | tanno _ _ _ => intro hv _; nomatch hv
    | twrap _ _ _ _ => intro _ hs; nomatch hs
    | tseal _ _ _ _ _ => intro hv _; nomatch hv
    | tunseal _ _ _ _ _ _ => intro hv _; nomatch hv
    | tflam _ _ _ _ => intro hv _; nomatch hv
    | tfclos _ _ _ _ _ _ _ _ _ _ => intro _ hs; nomatch hs
    | tinl _ _ => intro _ hs; nomatch hs
    | tinr _ _ => intro _ hs; nomatch hs
    | tcase _ _ _ _ _ _ _ _ => intro hv _; nomatch hv
    | tfold hp _ =>
      intro hv hs
      cases hs with
      | smu => exact ⟨_, Cast.cfold⟩
    | tunfold _ _ _ => intro hv _; nomatch hv

end Seal
