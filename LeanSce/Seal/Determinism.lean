import LeanSce.Seal.Lookup

-- Generalized determinism for λE^≤ (λE Theorem 4.2 + Eᵢ Theorem 7).  Both sources of raw
-- nondeterminism — value-level selection (sel-mrgl/sel-mrgr) and casting (mergevl/mergevr)
-- — are tamed by the single typing hypothesis, via sel_determinism (λE Lemma 4.1) and
-- cast_determinism (Eᵢ Lemma 6) respectively.  Core has no small-step determinism theorem;
-- this one is central to the TDOS story.
namespace Seal

variable {Δ : BrandStore}

theorem gdeterminism {venv e e₁ : Exp} (h₁ : Step venv e e₁)
    {Γ A : Typ} (ht : HasType Δ Γ e A) (henv : HasType Δ .top venv Γ)
    {e₂ : Exp} (h₂ : Step venv e e₂) : e₁ = e₂ := by
  induction h₁ generalizing Γ A e₂ with
  | squery _ =>
    cases h₂ with
    | squery _ => rfl
  | sappl _ hs ih =>
    cases h₂ with
    | sappl _ hs₂ =>
      cases ht with
      | tapp ha _ => rw [ih ha henv hs₂]
    | sappr _ hv₁ _ => exact (value_not_step hv₁ hs).elim
    | sbeta _ hu _ _ => exact (value_not_step (Value.vclos hu) hs).elim
    | sfbeta _ hu _ _ => exact (value_not_step (Value.vfclos hu) hs).elim
  | sappr _ hv₁ hs ih =>
    cases h₂ with
    | sappl _ hs₂ => exact (value_not_step hv₁ hs₂).elim
    | sappr _ _ hs₂ =>
      cases ht with
      | tapp _ hb => rw [ih hb henv hs₂]
    | sbeta _ _ hv₂ _ => exact (value_not_step hv₂ hs).elim
    | sfbeta _ _ hv₂ _ => exact (value_not_step hv₂ hs).elim
  | sbeta _ hv₁ hv₂ hc =>
    cases h₂ with
    | sappl _ hs₂ => exact (value_not_step (Value.vclos hv₁) hs₂).elim
    | sappr _ _ hs₂ => exact (value_not_step hv₂ hs₂).elim
    | sbeta _ _ _ hc₂ =>
      cases ht with
      | tapp _ hb => rw [cast_determinism hc hv₂ hb hc₂]
  | sinl _ hs ih =>
    cases h₂ with
    | sinl _ hs₂ =>
      cases ht with
      | tinl ha => rw [ih ha henv hs₂]
  | sinr _ hs ih =>
    cases h₂ with
    | sinr _ hs₂ =>
      cases ht with
      | tinr ha => rw [ih ha henv hs₂]
  | scase _ hs ih =>
    cases h₂ with
    | scase _ hs₂ =>
      cases ht with
      | tcase ha _ _ _ _ => rw [ih ha henv hs₂]
    | scasel _ hv₁ => exact (value_not_step (Value.vinl hv₁) hs).elim
    | scaser _ hv₁ => exact (value_not_step (Value.vinr hv₁) hs).elim
  | scasel _ hv₁ =>
    cases h₂ with
    | scase _ hs₂ => exact (value_not_step (Value.vinl hv₁) hs₂).elim
    | scasel _ _ => rfl
  | scaser _ hv₁ =>
    cases h₂ with
    | scase _ hs₂ => exact (value_not_step (Value.vinr hv₁) hs₂).elim
    | scaser _ _ => rfl
  | sfold _ hs ih =>
    cases h₂ with
    | sfold _ hs₂ =>
      cases ht with
      | tfold _ ha => rw [ih ha henv hs₂]
  | sunfold _ hs ih =>
    cases h₂ with
    | sunfold _ hs₂ =>
      cases ht with
      | tunfold _ ha _ => rw [ih ha henv hs₂]
    | sunfoldv _ hv₁ => exact (value_not_step (Value.vfold hv₁) hs).elim
  | sunfoldv _ hv₁ =>
    cases h₂ with
    | sunfold _ hs₂ => exact (value_not_step (Value.vfold hv₁) hs₂).elim
    | sunfoldv _ _ => rfl
  | sflam _ =>
    cases h₂ with
    | sflam _ => rfl
  | sblam _ =>
    cases h₂ with
    | sblam _ => rfl
  | sbappl _ hs ih =>
    cases h₂ with
    | sbappl _ hs₂ =>
      cases ht with
      | tbapp ha _ _ => rw [ih ha henv hs₂]
    | sbappbeta _ hρ => exact (value_not_step (Value.vbclos hρ) hs).elim
  | sbappbeta _ hρ =>
    cases h₂ with
    | sbappl _ hs₂ => exact (value_not_step (Value.vbclos hρ) hs₂).elim
    | sbappbeta _ _ => rfl
  | sfbeta _ hv₁ hv₂ hc =>
    cases h₂ with
    | sappl _ hs₂ => exact (value_not_step (Value.vfclos hv₁) hs₂).elim
    | sappr _ _ hs₂ => exact (value_not_step hv₂ hs₂).elim
    | sfbeta _ _ _ hc₂ =>
      cases ht with
      | tapp _ hb => rw [cast_determinism hc hv₂ hb hc₂]
  | sclos _ =>
    cases h₂ with
    | sclos _ => rfl
  | sboxl _ hs ih =>
    cases h₂ with
    | sboxl _ hs₂ =>
      cases ht with
      | tbox ha _ => rw [ih ha henv hs₂]
    | sboxr _ hv₁ _ => exact (value_not_step hv₁ hs).elim
    | sboxv _ hv₁ _ => exact (value_not_step hv₁ hs).elim
  | sboxr _ hv₁ hs ih =>
    cases h₂ with
    | sboxl _ hs₂ => exact (value_not_step hv₁ hs₂).elim
    | sboxr _ _ hs₂ =>
      cases ht with
      | tbox ha hb => rw [ih hb (value_weaken ha hv₁) hs₂]
    | sboxv _ _ hv₂ => exact (value_not_step hv₂ hs).elim
  | sboxv _ hv₁ hv₂ =>
    cases h₂ with
    | sboxl _ hs₂ => exact (value_not_step hv₁ hs₂).elim
    | sboxr _ _ hs₂ => exact (value_not_step hv₂ hs₂).elim
    | sboxv _ _ _ => rfl
  | smrgl _ hs ih =>
    cases h₂ with
    | smrgl _ hs₂ =>
      cases ht with
      | tmrg ha _ _ _ => rw [ih ha henv hs₂]
      | tmergev hva _ _ _ _ _ => exact (value_not_step hva hs).elim
      | tmergevc hva _ _ _ _ _ _ _ _ => exact (value_not_step hva hs).elim
    | smrgr _ hv₁ _ => exact (value_not_step hv₁ hs).elim
  | smrgr hv hv₁ hs ih =>
    cases h₂ with
    | smrgl _ hs₂ => exact (value_not_step hv₁ hs₂).elim
    | smrgr _ _ hs₂ =>
      cases ht with
      | tmrg ha hb hd₁ _ => rw [ih hb (env_extend_typing hv hv₁ henv ha hd₁) hs₂]
      | tmergev _ hvb _ _ _ _ => exact (value_not_step hvb hs).elim
      | tmergevc _ hvb _ _ _ _ _ _ _ => exact (value_not_step hvb hs).elim
  | sproj _ hs ih =>
    cases h₂ with
    | sproj _ hs₂ =>
      cases ht with
      | tproj ha _ => rw [ih ha henv hs₂]
    | sprojv _ hv₁ _ => exact (value_not_step hv₁ hs).elim
  | sprojv _ hv₁ hlv =>
    cases h₂ with
    | sproj _ hs₂ => exact (value_not_step hv₁ hs₂).elim
    | sprojv _ _ hlv₂ => exact lookupv_det hlv hlv₂
  | slrec _ hs ih =>
    cases h₂ with
    | slrec _ hs₂ =>
      cases ht with
      | trcd ha => rw [ih ha henv hs₂]
  | srproj _ hs ih =>
    cases h₂ with
    | srproj _ hs₂ =>
      cases ht with
      | trproj ha _ => rw [ih ha henv hs₂]
    | srprojv _ hv₁ _ => exact (value_not_step hv₁ hs).elim
  | srprojv _ hv₁ hlv =>
    cases h₂ with
    | srproj _ hs₂ => exact (value_not_step hv₁ hs₂).elim
    | srprojv _ _ hlv₂ =>
      cases ht with
      | trproj ha hl => exact sel_determinism hl hv₁ ha hlv hlv₂
  | sanno _ hs ih =>
    cases h₂ with
    | sanno _ hs₂ =>
      cases ht with
      | tanno ha _ => rw [ih ha henv hs₂]
    | sannov _ hv₁ _ => exact (value_not_step hv₁ hs).elim
  | sannov _ hv₁ hc =>
    cases h₂ with
    | sanno _ hs₂ => exact (value_not_step hv₁ hs₂).elim
    | sannov _ _ hc₂ =>
      cases ht with
      | tanno ha _ => exact cast_determinism hc hv₁ ha hc₂
  | swrap _ hs ih =>
    cases h₂ with
    | swrap _ hs₂ =>
      cases ht with
      | twrap _ _ hv _ => exact (value_not_step hv hs).elim
  | sseal _ hs ih =>
    cases h₂ with
    | sseal _ hs₂ =>
      cases ht with
      | tseal _ _ _ _ ha => rw [ih ha henv hs₂]
    | ssealv _ hv₁ _ => exact (value_not_step hv₁ hs).elim
  | ssealv _ hv₁ hsv =>
    cases h₂ with
    | sseal _ hs₂ => exact (value_not_step hv₁ hs₂).elim
    | ssealv _ _ hsv₂ => exact sealv_det hsv hsv₂
  | sunseal _ hs ih =>
    cases h₂ with
    | sunseal _ hs₂ =>
      cases ht with
      | tunseal _ _ _ _ ha _ => rw [ih ha henv hs₂]
    | sunsealv _ hv₁ _ => exact (value_not_step hv₁ hs).elim
  | sunsealv _ hv₁ hsv =>
    cases h₂ with
    | sunseal _ hs₂ => exact (value_not_step hv₁ hs₂).elim
    | sunsealv _ _ hsv₂ => exact unsealv_det hsv hsv₂

-- Whole-program corollary.
theorem determinism {e e₁ e₂ : Exp} {A : Typ} (ht : HasType Δ .top e A)
    (h₁ : Step .unit e e₁) (h₂ : Step .unit e e₂) : e₁ = e₂ :=
  gdeterminism h₁ ht HasType.tunit h₂

end Seal
