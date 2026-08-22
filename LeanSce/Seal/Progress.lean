import LeanSce.Seal.Lookup

-- Generalized progress for λE^≤ (λE Theorem 4.8 + Eᵢ Theorem 13's casting cases).
-- The new redexes: (v : A) fires by progress of casting (the typing rule guarantees the
-- value's type sits below the annotation), and beta's argument-cast fires because the
-- closure's input slack C <: A₀ composes with the argument's typing.
namespace Seal

variable {Δ : BrandStore}

-- Progress of the coercions: a value typed at the representation view S[n:=R] seals at S,
-- and a value typed at S unseals.  Pure canonical-forms reasoning on the shape of S.
theorem sealv_progress {n : Nat} {R : Typ} : (S : Typ) → ∀ {Γ : Typ} {v : Exp},
    Value v → HasType Δ Γ v (substBrand n R S) → ∃ w, SealV n R S v w
  | .int, _, _, hv, ht => by
    simp only [substBrand] at ht
    cases ht with
    | tint => exact ⟨_, SealV.int⟩
    | tquery => nomatch hv
    | tapp _ _ => nomatch hv
    | tbox _ _ => nomatch hv
    | tproj _ _ => nomatch hv
    | trproj _ _ => nomatch hv
    | tanno _ _ => nomatch hv
    | tcase _ _ _ _ _ => nomatch hv
    | tunfold _ _ => nomatch hv
    | tseal _ _ _ _ => nomatch hv
    | tunseal _ _ _ _ _ => nomatch hv
  | .top, _, _, _, _ => ⟨_, SealV.top⟩
  | .brand m, _, _, _, _ => by
    by_cases h : m = n
    · subst h; exact ⟨_, SealV.brand_eq⟩
    · exact ⟨_, SealV.brand_ne h⟩
  | .arr _ _, _, _, _, _ => ⟨_, SealV.arr⟩
  | .var _, _, _, _, _ => ⟨_, SealV.var⟩
  | .mu _, _, _, _, _ => ⟨_, SealV.mu⟩
  | .bvar _, _, _, _, _ => ⟨_, SealV.bvar⟩
  | .allb _, _, _, _, _ => ⟨_, SealV.allb⟩
  | .rcd l A, _, _, hv, ht => by
    simp only [substBrand] at ht
    cases ht with
    | trcd h =>
      cases hv with
      | vrcd hv' =>
        obtain ⟨w, hw⟩ := sealv_progress A hv' h
        exact ⟨_, SealV.rcd hw⟩
    | tquery => nomatch hv
    | tapp _ _ => nomatch hv
    | tbox _ _ => nomatch hv
    | tproj _ _ => nomatch hv
    | trproj _ _ => nomatch hv
    | tanno _ _ => nomatch hv
    | tcase _ _ _ _ _ => nomatch hv
    | tunfold _ _ => nomatch hv
    | tseal _ _ _ _ => nomatch hv
    | tunseal _ _ _ _ _ => nomatch hv
  | .and A B, _, _, hv, ht => by
    simp only [substBrand] at ht
    cases ht with
    | tmrg h₁ h₂ _ _ =>
      cases hv with
      | vmrg hv₁ hv₂ =>
        obtain ⟨w₁, hw₁⟩ := sealv_progress A hv₁ h₁
        obtain ⟨w₂, hw₂⟩ := sealv_progress B hv₂ h₂
        exact ⟨_, SealV.and hw₁ hw₂⟩
    | tmergev hv₁ hv₂ h₁ h₂ _ _ =>
      obtain ⟨w₁, hw₁⟩ := sealv_progress A hv₁ h₁
      obtain ⟨w₂, hw₂⟩ := sealv_progress B hv₂ h₂
      exact ⟨_, SealV.and hw₁ hw₂⟩
    | tmergevc hv₁ hv₂ h₁ h₂ _ _ _ _ _ =>
      obtain ⟨w₁, hw₁⟩ := sealv_progress A hv₁ h₁
      obtain ⟨w₂, hw₂⟩ := sealv_progress B hv₂ h₂
      exact ⟨_, SealV.and hw₁ hw₂⟩
    | tquery => nomatch hv
    | tapp _ _ => nomatch hv
    | tbox _ _ => nomatch hv
    | tproj _ _ => nomatch hv
    | trproj _ _ => nomatch hv
    | tanno _ _ => nomatch hv
    | tcase _ _ _ _ _ => nomatch hv
    | tunfold _ _ => nomatch hv
    | tseal _ _ _ _ => nomatch hv
    | tunseal _ _ _ _ _ => nomatch hv
  | .or A B, _, _, hv, ht => by
    simp only [substBrand] at ht
    cases ht with
    | tinl h =>
      cases hv with
      | vinl hv' =>
        obtain ⟨w, hw⟩ := sealv_progress A hv' h
        exact ⟨_, SealV.inl hw⟩
    | tinr h =>
      cases hv with
      | vinr hv' =>
        obtain ⟨w, hw⟩ := sealv_progress B hv' h
        exact ⟨_, SealV.inr hw⟩
    | tquery => nomatch hv
    | tapp _ _ => nomatch hv
    | tbox _ _ => nomatch hv
    | tproj _ _ => nomatch hv
    | trproj _ _ => nomatch hv
    | tanno _ _ => nomatch hv
    | tcase _ _ _ _ _ => nomatch hv
    | tunfold _ _ => nomatch hv
    | tseal _ _ _ _ => nomatch hv
    | tunseal _ _ _ _ _ => nomatch hv

theorem unsealv_progress {n : Nat} {R : Typ} : (S : Typ) → ∀ {Γ : Typ} {v : Exp},
    Value v → HasType Δ Γ v S → ∃ w, UnsealV n R S v w
  | .int, _, _, hv, ht => by
    cases ht with
    | tint => exact ⟨_, UnsealV.int⟩
    | tquery => nomatch hv
    | tapp _ _ => nomatch hv
    | tbox _ _ => nomatch hv
    | tproj _ _ => nomatch hv
    | trproj _ _ => nomatch hv
    | tanno _ _ => nomatch hv
    | tcase _ _ _ _ _ => nomatch hv
    | tunfold _ _ => nomatch hv
    | tseal _ _ _ _ => nomatch hv
    | tunseal _ _ _ _ _ => nomatch hv
  | .top, _, _, _, _ => ⟨_, UnsealV.top⟩
  | .brand m, _, _, hv, ht => by
    by_cases h : m = n
    · subst h
      cases ht with
      | twrap _ _ _ => exact ⟨_, UnsealV.brand_eq⟩
      | tquery => nomatch hv
      | tapp _ _ => nomatch hv
      | tbox _ _ => nomatch hv
      | tproj _ _ => nomatch hv
      | trproj _ _ => nomatch hv
      | tanno _ _ => nomatch hv
      | tcase _ _ _ _ _ => nomatch hv
      | tunfold _ _ => nomatch hv
      | tseal _ _ _ _ => nomatch hv
      | tunseal _ _ _ _ _ => nomatch hv
    · exact ⟨_, UnsealV.brand_ne h⟩
  | .arr _ _, _, _, _, _ => ⟨_, UnsealV.arr⟩
  | .var _, _, _, _, _ => ⟨_, UnsealV.var⟩
  | .mu _, _, _, _, _ => ⟨_, UnsealV.mu⟩
  | .bvar _, _, _, _, _ => ⟨_, UnsealV.bvar⟩
  | .allb _, _, _, _, _ => ⟨_, UnsealV.allb⟩
  | .rcd l A, _, _, hv, ht => by
    cases ht with
    | trcd h =>
      cases hv with
      | vrcd hv' =>
        obtain ⟨w, hw⟩ := unsealv_progress A hv' h
        exact ⟨_, UnsealV.rcd hw⟩
    | tquery => nomatch hv
    | tapp _ _ => nomatch hv
    | tbox _ _ => nomatch hv
    | tproj _ _ => nomatch hv
    | trproj _ _ => nomatch hv
    | tanno _ _ => nomatch hv
    | tcase _ _ _ _ _ => nomatch hv
    | tunfold _ _ => nomatch hv
    | tseal _ _ _ _ => nomatch hv
    | tunseal _ _ _ _ _ => nomatch hv
  | .and A B, _, _, hv, ht => by
    cases ht with
    | tmrg h₁ h₂ _ _ =>
      cases hv with
      | vmrg hv₁ hv₂ =>
        obtain ⟨w₁, hw₁⟩ := unsealv_progress A hv₁ h₁
        obtain ⟨w₂, hw₂⟩ := unsealv_progress B hv₂ h₂
        exact ⟨_, UnsealV.and hw₁ hw₂⟩
    | tmergev hv₁ hv₂ h₁ h₂ _ _ =>
      obtain ⟨w₁, hw₁⟩ := unsealv_progress A hv₁ h₁
      obtain ⟨w₂, hw₂⟩ := unsealv_progress B hv₂ h₂
      exact ⟨_, UnsealV.and hw₁ hw₂⟩
    | tmergevc hv₁ hv₂ h₁ h₂ _ _ _ _ _ =>
      obtain ⟨w₁, hw₁⟩ := unsealv_progress A hv₁ h₁
      obtain ⟨w₂, hw₂⟩ := unsealv_progress B hv₂ h₂
      exact ⟨_, UnsealV.and hw₁ hw₂⟩
    | tquery => nomatch hv
    | tapp _ _ => nomatch hv
    | tbox _ _ => nomatch hv
    | tproj _ _ => nomatch hv
    | trproj _ _ => nomatch hv
    | tanno _ _ => nomatch hv
    | tcase _ _ _ _ _ => nomatch hv
    | tunfold _ _ => nomatch hv
    | tseal _ _ _ _ => nomatch hv
    | tunseal _ _ _ _ _ => nomatch hv
  | .or A B, _, _, hv, ht => by
    cases ht with
    | tinl h =>
      cases hv with
      | vinl hv' =>
        obtain ⟨w, hw⟩ := unsealv_progress A hv' h
        exact ⟨_, UnsealV.inl hw⟩
    | tinr h =>
      cases hv with
      | vinr hv' =>
        obtain ⟨w, hw⟩ := unsealv_progress B hv' h
        exact ⟨_, UnsealV.inr hw⟩
    | tquery => nomatch hv
    | tapp _ _ => nomatch hv
    | tbox _ _ => nomatch hv
    | tproj _ _ => nomatch hv
    | trproj _ _ => nomatch hv
    | tanno _ _ => nomatch hv
    | tcase _ _ _ _ _ => nomatch hv
    | tunfold _ _ => nomatch hv
    | tseal _ _ _ _ => nomatch hv
    | tunseal _ _ _ _ _ => nomatch hv

theorem gprogress {Γ A : Typ} {e : Exp} (ht : HasType Δ Γ e A)
    {v : Exp} (hv : Value v) (henv : HasType Δ .top v Γ)
    : Value e ∨ ∃ e', Step v e e' := by
  induction ht generalizing v with
  | tquery => exact Or.inr ⟨_, Step.squery hv⟩
  | tint => exact Or.inl Value.vint
  | tunit => exact Or.inl Value.vunit
  | tapp h₁ h₂ ih₁ ih₂ =>
    cases ih₁ hv henv with
    | inr hs =>
      obtain ⟨e₁', hs'⟩ := hs
      exact Or.inr ⟨_, Step.sappl hv hs'⟩
    | inl hv₁ =>
      cases ih₂ hv henv with
      | inr hs =>
        obtain ⟨e₂', hs'⟩ := hs
        exact Or.inr ⟨_, Step.sappr hv hv₁ hs'⟩
      | inl hv₂ =>
        cases h₁ with
        | tclos _ _ _ _ _ hs₂ =>
          obtain ⟨v₂', hc⟩ := cast_progress hv₂ h₂ hs₂
          cases hv₁ with
          | vclos hu => exact Or.inr ⟨_, Step.sbeta hv hu hv₂ hc⟩
        | tfclos _ _ _ _ _ _ _ hs₃ =>
          obtain ⟨v₂', hc⟩ := cast_progress hv₂ h₂ hs₃
          cases hv₁ with
          | vfclos hu => exact Or.inr ⟨_, Step.sfbeta hv hu hv₂ hc⟩
        | tflam _ _ _ => nomatch hv₁
        | tquery => nomatch hv₁
        | tapp _ _ => nomatch hv₁
        | tbox _ _ => nomatch hv₁
        | tproj _ _ => nomatch hv₁
        | trproj _ _ => nomatch hv₁
        | tanno _ _ => nomatch hv₁
        | tlam _ _ => nomatch hv₁
        | tcase _ _ _ _ _ => nomatch hv₁
        | tunfold _ _ => nomatch hv₁
        | tseal _ _ _ _ => nomatch hv₁
        | tunseal _ _ _ _ _ => nomatch hv₁
  | tbox h₁ _ ih₁ ih₂ =>
    cases ih₁ hv henv with
    | inr hs =>
      obtain ⟨e₁', hs'⟩ := hs
      exact Or.inr ⟨_, Step.sboxl hv hs'⟩
    | inl hv₁ =>
      cases ih₂ hv₁ (value_weaken h₁ hv₁) with
      | inr hs =>
        obtain ⟨e₂', hs'⟩ := hs
        exact Or.inr ⟨_, Step.sboxr hv hv₁ hs'⟩
      | inl hv₂ => exact Or.inr ⟨_, Step.sboxv hv hv₁ hv₂⟩
  | tproj h hl ih =>
    cases ih hv henv with
    | inr hs =>
      obtain ⟨e', hs'⟩ := hs
      exact Or.inr ⟨_, Step.sproj hv hs'⟩
    | inl hve =>
      obtain ⟨v', hlv⟩ := lookup_prog hl hve h
      exact Or.inr ⟨_, Step.sprojv hv hve hlv⟩
  | trcd _ ih =>
    cases ih hv henv with
    | inr hs =>
      obtain ⟨e', hs'⟩ := hs
      exact Or.inr ⟨_, Step.slrec hv hs'⟩
    | inl hve => exact Or.inl (Value.vrcd hve)
  | trproj h hl ih =>
    cases ih hv henv with
    | inr hs =>
      obtain ⟨e', hs'⟩ := hs
      exact Or.inr ⟨_, Step.srproj hv hs'⟩
    | inl hve =>
      obtain ⟨v', hlv⟩ := rlookup_prog hl hve h
      exact Or.inr ⟨_, Step.srprojv hv hve hlv⟩
  | tmrg h₁ _ hd₁ _ ih₁ ih₂ =>
    cases ih₁ hv henv with
    | inr hs =>
      obtain ⟨e₁', hs'⟩ := hs
      exact Or.inr ⟨_, Step.smrgl hv hs'⟩
    | inl hv₁ =>
      cases ih₂ (Value.vmrg hv hv₁) (env_extend_typing hv hv₁ henv h₁ hd₁) with
      | inr hs =>
        obtain ⟨e₂', hs'⟩ := hs
        exact Or.inr ⟨_, Step.smrgr hv hv₁ hs'⟩
      | inl hv₂ => exact Or.inl (Value.vmrg hv₁ hv₂)
  | tmergev hv₁ hv₂ _ _ _ _ _ _ => exact Or.inl (Value.vmrg hv₁ hv₂)
  | tmergevc hv₁ hv₂ _ _ _ _ _ _ _ _ _ _ => exact Or.inl (Value.vmrg hv₁ hv₂)
  | tlam _ _ _ => exact Or.inr ⟨_, Step.sclos hv⟩
  | tclos hu _ _ _ _ _ _ _ => exact Or.inl (Value.vclos hu)
  | tflam _ _ _ _ => exact Or.inr ⟨_, Step.sflam hv⟩
  | tfclos hu _ _ _ _ _ _ _ _ _ => exact Or.inl (Value.vfclos hu)
  | tfold _ ih =>
    cases ih hv henv with
    | inr hs =>
      obtain ⟨e', hs'⟩ := hs
      exact Or.inr ⟨_, Step.sfold hv hs'⟩
    | inl hve => exact Or.inl (Value.vfold hve)
  | tunfold h _ ih =>
    cases ih hv henv with
    | inr hs =>
      obtain ⟨e', hs'⟩ := hs
      exact Or.inr ⟨_, Step.sunfold hv hs'⟩
    | inl hve =>
      cases h with
      | tfold _ =>
        cases hve with
        | vfold hv' => exact Or.inr ⟨_, Step.sunfoldv hv hv'⟩
      | tquery => nomatch hve
      | tapp _ _ => nomatch hve
      | tbox _ _ => nomatch hve
      | tproj _ _ => nomatch hve
      | trproj _ _ => nomatch hve
      | tanno _ _ => nomatch hve
      | tcase _ _ _ _ _ => nomatch hve
      | tunfold _ _ => nomatch hve
      | tseal _ _ _ _ => nomatch hve
      | tunseal _ _ _ _ _ => nomatch hve
  | tinl _ ih =>
    cases ih hv henv with
    | inr hs =>
      obtain ⟨e', hs'⟩ := hs
      exact Or.inr ⟨_, Step.sinl hv hs'⟩
    | inl hve => exact Or.inl (Value.vinl hve)
  | tinr _ ih =>
    cases ih hv henv with
    | inr hs =>
      obtain ⟨e', hs'⟩ := hs
      exact Or.inr ⟨_, Step.sinr hv hs'⟩
    | inl hve => exact Or.inl (Value.vinr hve)
  | tcase h _ _ _ _ ih _ _ =>
    cases ih hv henv with
    | inr hs =>
      obtain ⟨e', hs'⟩ := hs
      exact Or.inr ⟨_, Step.scase hv hs'⟩
    | inl hve =>
      cases h with
      | tinl _ =>
        cases hve with
        | vinl hv' => exact Or.inr ⟨_, Step.scasel hv hv'⟩
      | tinr _ =>
        cases hve with
        | vinr hv' => exact Or.inr ⟨_, Step.scaser hv hv'⟩
      | tquery => nomatch hve
      | tapp _ _ => nomatch hve
      | tbox _ _ => nomatch hve
      | tproj _ _ => nomatch hve
      | trproj _ _ => nomatch hve
      | tanno _ _ => nomatch hve
      | tcase _ _ _ _ _ => nomatch hve
      | tunfold _ _ => nomatch hve
      | tseal _ _ _ _ => nomatch hve
      | tunseal _ _ _ _ _ => nomatch hve
  | tanno h hsub ih =>
    cases ih hv henv with
    | inr hs =>
      obtain ⟨e', hs'⟩ := hs
      exact Or.inr ⟨_, Step.sanno hv hs'⟩
    | inl hve =>
      obtain ⟨w, hc⟩ := cast_progress hve h hsub
      exact Or.inr ⟨_, Step.sannov hv hve hc⟩
  | twrap _ hv' _ _ => exact Or.inl (Value.vwrap hv')
  | tseal _ _ _ h ih =>
    cases ih hv henv with
    | inr hs =>
      obtain ⟨e', hs'⟩ := hs
      exact Or.inr ⟨_, Step.sseal hv hs'⟩
    | inl hve =>
      obtain ⟨w, hw⟩ := sealv_progress _ hve h
      exact Or.inr ⟨_, Step.ssealv hv hve hw⟩
  | tunseal _ _ _ h _ ih =>
    cases ih hv henv with
    | inr hs =>
      obtain ⟨e', hs'⟩ := hs
      exact Or.inr ⟨_, Step.sunseal hv hs'⟩
    | inl hve =>
      obtain ⟨w, hw⟩ := unsealv_progress _ hve h
      exact Or.inr ⟨_, Step.sunsealv hv hve hw⟩

-- Whole-program corollary.
theorem progress {e : Exp} {A : Typ} (ht : HasType Δ .top e A)
    : Value e ∨ ∃ e', Step .unit e e' :=
  gprogress ht Value.vunit HasType.tunit

end Seal
