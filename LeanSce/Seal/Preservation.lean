import LeanSce.Seal.Lookup

-- Generalized preservation for λE^≤ (λE Theorem 4.9 + the casting premises of Eᵢ
-- Theorem 14).  The genuinely new cases: sbeta re-types the extended closure environment
-- via tmergev + disjointness-implies-consistency (never via tmrg), and sannov is exactly
-- preservation of casting.
namespace Seal

variable {Δ : BrandStore}

-- ── Reserved-label bookkeeping for the coercion proxies ──────────────────────────────

theorem wfsig_nores {n : Nat} {R S : Typ} (h : WfSig n R S) : NoRes S := by
  induction h with
  | int => exact NoRes.int
  | top => exact NoRes.top
  | brand => exact NoRes.brand
  | arr _ _ ih₁ ih₂ => exact NoRes.arr ih₁ ih₂
  | rcd hne _ ih => exact NoRes.rcd hne ih
  | and _ _ _ _ ih₁ ih₂ => exact NoRes.and ih₁ ih₂
  | or _ _ ih₁ ih₂ => exact NoRes.or ih₁ ih₂
  | mu _ hnr _ => exact hnr
  | allb _ hnr _ => exact hnr

theorem nores_subst {n : Nat} {R S : Typ} (hR : NoRes R) (hS : NoRes S)
    : NoRes (substBrand n R S) := by
  induction hS with
  | int => exact NoRes.int
  | top => exact NoRes.top
  | brand =>
    rename_i m
    by_cases h : m = n
    · simp only [substBrand, h, if_true]; exact hR
    · simp only [substBrand, h, if_false]; exact NoRes.brand
  | arr _ _ ih₁ ih₂ => exact NoRes.arr ih₁ ih₂
  | rcd hne _ ih => exact NoRes.rcd hne ih
  | and _ _ ih₁ ih₂ => exact NoRes.and ih₁ ih₂
  | or _ _ ih₁ ih₂ => exact NoRes.or ih₁ ih₂
  | var => exact NoRes.var
  | mu _ ih => exact NoRes.mu ih
  | bvar => exact NoRes.bvar
  | allb _ ih => exact NoRes.allb ih

-- A record under the reserved label is disjoint from every type that avoids the label.
theorem cost_reserved {T X : Typ} (hX : NoRes X) (hc : Cost (.rcd reservedLabel T) X) : False := by
  induction hX with
  | int => nomatch hc
  | top => nomatch hc
  | brand => nomatch hc
  | arr _ _ _ _ => nomatch hc
  | rcd hne _ _ => cases hc with | crcd _ => exact hne rfl
  | or _ _ _ _ => nomatch hc
  | var => nomatch hc
  | mu _ _ => nomatch hc
  | bvar => nomatch hc
  | allb _ _ => nomatch hc
  | and _ _ ih₁ ih₂ =>
    cases hc with
    | crandl h => exact ih₁ h
    | crandr h => exact ih₂ h

theorem cost_proxyEnv {T X : Typ} (hX : NoRes X) (hc : Cost (.and .top (.rcd reservedLabel T)) X)
    : False := by
  induction hX with
  | int => cases hc with | candl h => exact cost_top_l h | candr h => exact cost_reserved NoRes.int h
  | top => cases hc with | candl h => exact cost_top_l h | candr h => exact cost_reserved NoRes.top h
  | brand => cases hc with | candl h => exact cost_top_l h | candr h => exact cost_reserved NoRes.brand h
  | arr h₁ h₂ _ _ =>
    cases hc with
    | candl h => exact cost_top_l h
    | candr h => exact cost_reserved (NoRes.arr h₁ h₂) h
  | rcd hne h _ =>
    cases hc with
    | candl h' => exact cost_top_l h'
    | candr h' => exact cost_reserved (NoRes.rcd hne h) h'
  | or h₁ h₂ _ _ =>
    cases hc with
    | candl h => exact cost_top_l h
    | candr h => exact cost_reserved (NoRes.or h₁ h₂) h
  | var =>
    cases hc with
    | candl h => exact cost_top_l h
    | candr h => exact cost_reserved NoRes.var h
  | mu h _ =>
    cases hc with
    | candl h' => exact cost_top_l h'
    | candr h' => exact cost_reserved (NoRes.mu h) h'
  | bvar =>
    cases hc with
    | candl h => exact cost_top_l h
    | candr h => exact cost_reserved NoRes.bvar h
  | allb h _ =>
    cases hc with
    | candl h' => exact cost_top_l h'
    | candr h' => exact cost_reserved (NoRes.allb h) h'
  | and h₁ h₂ ih₁ ih₂ =>
    cases hc with
    | candl h => exact cost_top_l h
    | candr h => exact cost_reserved (NoRes.and h₁ h₂) h
    | crandl h => exact ih₁ h
    | crandr h => exact ih₂ h

theorem disj_proxyEnv {T X : Typ} (hX : NoRes X) : Disj (.and .top (.rcd reservedLabel T)) X :=
  fun hc => cost_proxyEnv hX hc

-- The proxy environment is a well-typed closed value at its (record-wrapped) type.
theorem proxyEnv_typed {c : Exp} {T : Typ} (hc : Value c) (ht : HasType Δ .top c T)
    : HasType Δ .top (proxyEnv c) (.and .top (.rcd reservedLabel T)) :=
  HasType.tmrg HasType.tunit (HasType.trcd (value_weaken ht hc)) disj_top disj_top

theorem proxyEnv_value {c : Exp} (hc : Value c) : Value (proxyEnv c) :=
  Value.vmrg Value.vunit (Value.vrcd hc)

-- ── Preservation of the coercions ────────────────────────────────────────────────────

-- Sealing preserves types: a value of the representation view S[n:=R] seals to a value
-- of the abstract view S.  The arrow case types the proxy closure with tclos: its
-- environment is disjoint from the input type because signatures avoid the reserved
-- label, and its body is typed by the very rules tseal/tunseal.
theorem sealv_preservation {n : Nat} {R : Typ} (hΔ : Δ n = some R) (hR : NoRes R)
    (hRb : ¬ HasBVar R) {S : Typ} {v w : Exp} (hsv : SealV n R S v w)
    : ∀ {Γ : Typ}, WfSig n R S → Value v → HasType Δ Γ v (substBrand n R S)
    → HasType Δ Γ w S := by
  induction hsv with
  | brand_eq =>
    intro Γ _ hv ht
    simp only [substBrand, if_true] at ht
    exact HasType.twrap hΔ hv (value_weaken ht hv)
  | brand_ne hne =>
    intro Γ _ hv ht
    simp only [substBrand, hne, if_false] at ht
    exact ht
  | int => intro Γ _ _ _; exact HasType.tint
  | top => intro Γ _ _ _; exact HasType.tunit
  | and h₁ h₂ ih₁ ih₂ =>
    intro Γ hwf hv ht
    cases hwf with
    | and hwfA hwfB hdAB _ =>
      cases hv with
      | vmrg hv₁ hv₂ =>
        have hw₁ := sealv_value hv₁ h₁
        have hw₂ := sealv_value hv₂ h₂
        simp only [substBrand] at ht
        cases ht with
        | tmrg ht₁ ht₂ _ _ =>
          have hA := value_weaken (ih₁ hwfA hv₁ ht₁) hw₁ (Γ' := .top)
          have hB := value_weaken (ih₂ hwfB hv₂ ht₂) hw₂ (Γ' := .top)
          exact HasType.tmergev hw₁ hw₂ hA hB hdAB (disjoint_consistent hw₁ hw₂ hA hB hdAB)
        | tmergev _ _ ht₁ ht₂ _ _ =>
          have hA := ih₁ hwfA hv₁ ht₁
          have hB := ih₂ hwfB hv₂ ht₂
          exact HasType.tmergev hw₁ hw₂ hA hB hdAB (disjoint_consistent hw₁ hw₂ hA hB hdAB)
        | tmergevc _ _ ht₁ ht₂ _ _ _ _ _ =>
          have hA := ih₁ hwfA hv₁ ht₁
          have hB := ih₂ hwfB hv₂ ht₂
          exact HasType.tmergev hw₁ hw₂ hA hB hdAB (disjoint_consistent hw₁ hw₂ hA hB hdAB)
  | rcd h ih =>
    intro Γ hwf hv ht
    cases hwf with
    | rcd _ hwfA =>
      cases hv with
      | vrcd hv' =>
        simp only [substBrand] at ht
        cases ht with
        | trcd ht' => exact HasType.trcd (ih hwfA hv' ht')
  | inl h ih =>
    intro Γ hwf hv ht
    cases hwf with
    | or hwfA hwfB =>
      cases hv with
      | vinl hv' =>
        simp only [substBrand] at ht
        cases ht with
        | tinl ht' => exact HasType.tinl (ih hwfA hv' ht')
  | inr h ih =>
    intro Γ hwf hv ht
    cases hwf with
    | or hwfA hwfB =>
      cases hv with
      | vinr hv' =>
        simp only [substBrand] at ht
        cases ht with
        | tinr ht' => exact HasType.tinr (ih hwfB hv' ht')
  | var =>
    intro Γ hwf _ _
    nomatch hwf
  -- WfSig has no bvar case (signatures are bvar-free), and no allb case yet.
  | bvar =>
    intro Γ hwf _ _
    nomatch hwf
  | allb =>
    intro Γ hwf hv ht
    cases hwf with
    | allb hnin _ _ => rwa [substBrand_notin hnin] at ht
  | mu =>
    intro Γ hwf hv ht
    cases hwf with
    | mu hnin _ _ => rwa [substBrand_notin hnin] at ht
  | arr =>
    intro Γ hwf hv ht
    cases hwf with
    | arr hwfA hwfB =>
      simp only [substBrand] at ht
      apply HasType.tclos (proxyEnv_value hv) (proxyEnv_typed hv (value_weaken ht hv))
        (disj_proxyEnv (wfsig_nores hwfA)) _ (sub_refl _) (sub_refl _)
      apply HasType.tseal hΔ hR hRb hwfB
      apply HasType.tapp
      · exact HasType.trproj (HasType.tproj HasType.tquery (Lookup.succ Lookup.zero))
          RLookup.zero
      · exact HasType.tunseal hΔ hR hRb hwfA (HasType.tproj HasType.tquery Lookup.zero) rfl

-- Unsealing preserves types: a value of the abstract view S unseals to a value of the
-- representation view S[n:=R].
theorem unsealv_preservation {n : Nat} {R : Typ} (hΔ : Δ n = some R) (hR : NoRes R)
    (hRb : ¬ HasBVar R) {S : Typ} {v w : Exp} (hsv : UnsealV n R S v w)
    : ∀ {Γ : Typ}, WfSig n R S → Value v → HasType Δ Γ v S
    → HasType Δ Γ w (substBrand n R S) := by
  induction hsv with
  | brand_eq =>
    intro Γ _ hv ht
    simp only [substBrand, if_true]
    cases ht with
    | twrap hΔ' hv' hp =>
      rw [hΔ] at hΔ'
      cases hΔ'
      exact value_weaken hp hv'
  | brand_ne hne =>
    intro Γ _ hv ht
    simp only [substBrand, hne, if_false]
    exact ht
  | int => intro Γ _ _ _; exact HasType.tint
  | top => intro Γ _ _ _; exact HasType.tunit
  | and h₁ h₂ ih₁ ih₂ =>
    intro Γ hwf hv ht
    cases hwf with
    | and hwfA hwfB _ hdAB' =>
      cases hv with
      | vmrg hv₁ hv₂ =>
        have hw₁ := unsealv_value hv₁ h₁
        have hw₂ := unsealv_value hv₂ h₂
        simp only [substBrand]
        cases ht with
        | tmrg ht₁ ht₂ _ _ =>
          have hA := value_weaken (ih₁ hwfA hv₁ ht₁) hw₁ (Γ' := .top)
          have hB := value_weaken (ih₂ hwfB hv₂ ht₂) hw₂ (Γ' := .top)
          exact HasType.tmergev hw₁ hw₂ hA hB hdAB' (disjoint_consistent hw₁ hw₂ hA hB hdAB')
        | tmergev _ _ ht₁ ht₂ _ _ =>
          have hA := ih₁ hwfA hv₁ ht₁
          have hB := ih₂ hwfB hv₂ ht₂
          exact HasType.tmergev hw₁ hw₂ hA hB hdAB' (disjoint_consistent hw₁ hw₂ hA hB hdAB')
        | tmergevc _ _ ht₁ ht₂ _ _ _ _ _ =>
          have hA := ih₁ hwfA hv₁ ht₁
          have hB := ih₂ hwfB hv₂ ht₂
          exact HasType.tmergev hw₁ hw₂ hA hB hdAB' (disjoint_consistent hw₁ hw₂ hA hB hdAB')
  | rcd h ih =>
    intro Γ hwf hv ht
    cases hwf with
    | rcd _ hwfA =>
      cases hv with
      | vrcd hv' =>
        simp only [substBrand]
        cases ht with
        | trcd ht' => exact HasType.trcd (ih hwfA hv' ht')
  | inl h ih =>
    intro Γ hwf hv ht
    cases hwf with
    | or hwfA hwfB =>
      cases hv with
      | vinl hv' =>
        simp only [substBrand]
        cases ht with
        | tinl ht' => exact HasType.tinl (ih hwfA hv' ht')
  | inr h ih =>
    intro Γ hwf hv ht
    cases hwf with
    | or hwfA hwfB =>
      cases hv with
      | vinr hv' =>
        simp only [substBrand]
        cases ht with
        | tinr ht' => exact HasType.tinr (ih hwfB hv' ht')
  | var =>
    intro Γ hwf _ _
    nomatch hwf
  -- WfSig has no bvar case (signatures are bvar-free); ∀ is opaque — identity coercion.
  | bvar =>
    intro Γ hwf _ _
    nomatch hwf
  | allb =>
    intro Γ hwf hv ht
    cases hwf with
    | allb hnin _ _ => rw [substBrand_notin hnin]; exact ht
  | mu =>
    intro Γ hwf hv ht
    cases hwf with
    | mu hnin _ _ => rw [substBrand_notin hnin]; exact ht
  | arr =>
    intro Γ hwf hv ht
    cases hwf with
    | arr hwfA hwfB =>
      simp only [substBrand]
      apply HasType.tclos (proxyEnv_value hv) (proxyEnv_typed hv (value_weaken ht hv))
        (disj_proxyEnv (nores_subst hR (wfsig_nores hwfA))) _ (sub_refl _) (sub_refl _)
      apply HasType.tunseal hΔ hR hRb hwfB _ rfl
      apply HasType.tapp
      · exact HasType.trproj (HasType.tproj HasType.tquery (Lookup.succ Lookup.zero))
          RLookup.zero
      · exact HasType.tseal hΔ hR hRb hwfA (HasType.tproj HasType.tquery Lookup.zero)

theorem gpreservation {venv e e' : Exp} (hstep : Step venv e e')
    {Γ A : Typ} (ht : HasType Δ Γ e A) (henv : HasType Δ .top venv Γ)
    : HasType Δ Γ e' A := by
  induction hstep generalizing Γ A with
  | squery hv =>
    cases ht
    exact value_weaken henv hv
  | sappl _ _ ih =>
    cases ht with
    | tapp h₁ h₂ => exact HasType.tapp (ih h₁ henv) h₂
  | sappr _ _ _ ih =>
    cases ht with
    | tapp h₁ h₂ => exact HasType.tapp h₁ (ih h₂ henv)
  | sbeta _ _ hv₂ hc =>
    cases ht with
    | tapp h₁ h₂ =>
      cases h₁ with
      | tclos hu henv₁ hd hb hs₁ _ =>
        have hv₂' := cast_value hv₂ hc
        have ht₂' : HasType Δ .top _ _ := value_weaken (cast_preservation hc hv₂ h₂) hv₂'
        exact HasType.tbox
          (HasType.tmergev hu hv₂' henv₁ ht₂' hd
            (disjoint_consistent hu hv₂' henv₁ ht₂' hd))
          (HasType.tanno hb hs₁)
  | sclos hv =>
    cases ht with
    | tlam hd hb =>
      exact HasType.tclos hv (value_weaken henv hv) hd hb (sub_refl _) (sub_refl _)
  | sinl _ _ ih =>
    cases ht with
    | tinl h => exact HasType.tinl (ih h henv)
  | sinr _ _ ih =>
    cases ht with
    | tinr h => exact HasType.tinr (ih h henv)
  | scase _ _ ih =>
    cases ht with
    | tcase h hd₁ hd₂ h₁ h₂ => exact HasType.tcase (ih h henv) hd₁ hd₂ h₁ h₂
  -- Case beta: the branch environment (venv # payload) re-types via tmergev, with
  -- consistency from tcase's per-branch disjointness premise.
  | scasel hv hv₁ =>
    cases ht with
    | tcase h hd₁ hd₂ h₁ h₂ =>
      cases h with
      | tinl hp =>
        have hp' : HasType Δ .top _ _ := value_weaken hp hv₁
        exact HasType.tbox
          (HasType.tmergev hv hv₁ henv hp' hd₁ (disjoint_consistent hv hv₁ henv hp' hd₁)) h₁
  | scaser hv hv₁ =>
    cases ht with
    | tcase h hd₁ hd₂ h₁ h₂ =>
      cases h with
      | tinr hp =>
        have hp' : HasType Δ .top _ _ := value_weaken hp hv₁
        exact HasType.tbox
          (HasType.tmergev hv hv₁ henv hp' hd₂ (disjoint_consistent hv hv₁ henv hp' hd₂)) h₂
  | sfold _ _ ih =>
    cases ht with
    | tfold h => exact HasType.tfold (ih h henv)
  | sunfold _ _ ih =>
    cases ht with
    | tunfold h heq => exact HasType.tunfold (ih h henv) heq
  | sunfoldv _ _ =>
    cases ht with
    | tunfold h heq =>
      subst heq
      cases h with
      | tfold hp => exact hp
  | sflam hv =>
    cases ht with
    | tflam hd₁ hd₂ hb =>
      exact HasType.tfclos hv (value_weaken henv hv) hd₁ hd₂ hb (sub_refl _) (sub_refl _)
        (sub_refl _)
  -- Fixpoint beta: the environment (v₁ # self) # v₂' re-types via two tmergev's, with
  -- consistency supplied by the two disjointness premises tfclos carries; the body is
  -- resealed at the external codomain, reached through B' <: B <: Bx.
  | sfbeta _ _ hv₂ hc =>
    cases ht with
    | tapp h₁ h₂ =>
      cases h₁ with
      | tfclos hu henv₁ hd₁ hd₂ hb hs₁ hs₂ _ =>
        have hself : HasType Δ .top _ _ :=
          HasType.tfclos hu henv₁ hd₁ hd₂ hb hs₁ (sub_refl _) (sub_refl _)
        have hv₂' := cast_value hv₂ hc
        have ht₂' : HasType Δ .top _ _ := value_weaken (cast_preservation hc hv₂ h₂) hv₂'
        have hinner : HasType Δ .top _ _ :=
          HasType.tmergev hu (Value.vfclos hu) henv₁ hself hd₁
            (disjoint_consistent hu (Value.vfclos hu) henv₁ hself hd₁)
        exact HasType.tbox
          (HasType.tmergev (Value.vmrg hu (Value.vfclos hu)) hv₂' hinner ht₂' hd₂
            (disjoint_consistent (Value.vmrg hu (Value.vfclos hu)) hv₂' hinner ht₂' hd₂))
          (HasType.tanno hb (sub_trans hs₁ hs₂))
  | sboxl _ _ ih =>
    cases ht with
    | tbox h₁ h₂ => exact HasType.tbox (ih h₁ henv) h₂
  | sboxr _ hv₁ _ ih =>
    cases ht with
    | tbox h₁ h₂ => exact HasType.tbox h₁ (ih h₂ (value_weaken h₁ hv₁))
  | sboxv _ _ hv₂ =>
    cases ht with
    | tbox h₁ h₂ => exact value_weaken h₂ hv₂
  | smrgl _ hs ih =>
    cases ht with
    | tmrg h₁ h₂ hd₁ hd₂ => exact HasType.tmrg (ih h₁ henv) h₂ hd₁ hd₂
    | tmergev hva _ _ _ _ _ => exact (value_not_step hva hs).elim
    | tmergevc hva _ _ _ _ _ _ _ _ => exact (value_not_step hva hs).elim
  | smrgr hv hv₁ hs ih =>
    cases ht with
    | tmrg h₁ h₂ hd₁ hd₂ =>
      exact HasType.tmrg h₁ (ih h₂ (env_extend_typing hv hv₁ henv h₁ hd₁)) hd₁ hd₂
    | tmergev _ hvb _ _ _ _ => exact (value_not_step hvb hs).elim
    | tmergevc _ hvb _ _ _ _ _ _ _ => exact (value_not_step hvb hs).elim
  | sproj _ _ ih =>
    cases ht with
    | tproj h hl => exact HasType.tproj (ih h henv) hl
  | sprojv _ hv₁ hlv =>
    cases ht with
    | tproj h hl => exact lookup_pres hl hv₁ h hlv
  | slrec _ _ ih =>
    cases ht with
    | trcd h => exact HasType.trcd (ih h henv)
  | srproj _ _ ih =>
    cases ht with
    | trproj h hl => exact HasType.trproj (ih h henv) hl
  | srprojv _ hv₁ hlv =>
    cases ht with
    | trproj h hl => exact rlookup_pres hl hv₁ h hlv
  | sanno _ _ ih =>
    cases ht with
    | tanno h hsub => exact HasType.tanno (ih h henv) hsub
  | sannov _ hv₁ hc =>
    cases ht with
    | tanno h _ => exact cast_preservation hc hv₁ h
  | swrap _ hs _ =>
    cases ht with
    | twrap _ hv _ => exact (value_not_step hv hs).elim
  | sseal _ _ ih =>
    cases ht with
    | tseal hΔ hnr hnb hwf h => exact HasType.tseal hΔ hnr hnb hwf (ih h henv)
  | ssealv _ hv₁ hsv =>
    cases ht with
    | tseal hΔ hnr hnb hwf h => exact sealv_preservation hΔ hnr hnb hsv hwf hv₁ h
  | sunseal _ _ ih =>
    cases ht with
    | tunseal hΔ hnr hnb hwf h heq => exact HasType.tunseal hΔ hnr hnb hwf (ih h henv) heq
  | sunsealv _ hv₁ hsv =>
    cases ht with
    | tunseal hΔ hnr hnb hwf h heq =>
      subst heq
      exact unsealv_preservation hΔ hnr hnb hsv hwf hv₁ h

-- Whole-program corollary.
theorem preservation {e e' : Exp} {A : Typ} (ht : HasType Δ .top e A)
    (hstep : Step .unit e e') : HasType Δ .top e' A :=
  gpreservation hstep ht HasType.tunit

theorem mstep_preservation {venv e e' : Exp} (hstep : MStep venv e e')
    {Γ A : Typ} (ht : HasType Δ Γ e A) (henv : HasType Δ .top venv Γ)
    : HasType Δ Γ e' A := by
  induction hstep generalizing A with
  | refl => exact ht
  | step hs _ ih => exact ih (gpreservation hs ht henv)

end Seal
