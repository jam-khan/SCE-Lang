import LeanSce.Seal.CastingLemmas

-- λE's lookup and selection lemmas (progress, preservation, and the typed determinism of
-- selection — λE Lemmas 4.1 and 4.4–4.7), unchanged in substance from Core; only the
-- value-typing inversions now also see tmergev.
namespace Seal

variable {Δ : BrandStore}

theorem lookupv_value {v : Exp} {n : Nat} {v' : Exp} (hlv : LookupV v n v') (hv : Value v)
    : Value v' := by
  induction hlv with
  | lvzero => cases hv with | vmrg _ hv₂ => exact hv₂
  | lvsucc _ ih => cases hv with | vmrg hv₁ _ => exact ih hv₁

theorem rlookupv_value {v : Exp} {l : String} {v' : Exp} (hlv : RLookupV v l v')
    (hv : Value v) : Value v' := by
  induction hlv with
  | rvlzero => cases hv with | vrcd hv' => exact hv'
  | vlandl _ ih => cases hv with | vmrg hv₁ _ => exact ih hv₁
  | vlandr _ ih => cases hv with | vmrg _ hv₂ => exact ih hv₂

theorem lookupv_det {v : Exp} {n : Nat} {v₁ : Exp} (h₁ : LookupV v n v₁)
    {v₂ : Exp} (h₂ : LookupV v n v₂) : v₁ = v₂ := by
  induction h₁ generalizing v₂ with
  | lvzero => cases h₂ with | lvzero => rfl
  | lvsucc _ ih => cases h₂ with | lvsucc h₂' => exact ih h₂'

theorem lookup_prog {A : Typ} {n : Nat} {B : Typ} (hl : Lookup A n B)
    {v : Exp} {Γ : Typ} (hv : Value v) (ht : HasType Δ Γ v A) : ∃ v', LookupV v n v' := by
  induction hl generalizing v Γ with
  | zero =>
    cases ht with
    | tmrg _ _ _ _ => exact ⟨_, LookupV.lvzero⟩
    | tmergev _ _ _ _ _ _ => exact ⟨_, LookupV.lvzero⟩
    | tmergevc _ _ _ _ _ _ _ _ _ => exact ⟨_, LookupV.lvzero⟩
    | tquery => nomatch hv
    | tapp _ _ => nomatch hv
    | tbox _ _ => nomatch hv
    | tproj _ _ => nomatch hv
    | trproj _ _ => nomatch hv
    | tanno _ _ => nomatch hv
    | tcase _ _ _ _ _ => nomatch hv
    | tunfold _ _ => nomatch hv
    | tseal _ _ _ _ _ => nomatch hv
    | tunseal _ _ _ _ _ _ => nomatch hv
    | tbapp _ _ _ => nomatch hv
  | succ _ ih =>
    cases ht with
    | tmrg h₁ _ _ _ =>
      cases hv with
      | vmrg hv₁ _ =>
        obtain ⟨v', hlv⟩ := ih hv₁ h₁
        exact ⟨v', LookupV.lvsucc hlv⟩
    | tmergev hv₁ _ h₁ _ _ _ =>
      obtain ⟨v', hlv⟩ := ih hv₁ h₁
      exact ⟨v', LookupV.lvsucc hlv⟩
    | tmergevc hv₁ _ h₁ _ _ _ _ _ _ =>
      obtain ⟨v', hlv⟩ := ih hv₁ h₁
      exact ⟨v', LookupV.lvsucc hlv⟩
    | tquery => nomatch hv
    | tapp _ _ => nomatch hv
    | tbox _ _ => nomatch hv
    | tproj _ _ => nomatch hv
    | trproj _ _ => nomatch hv
    | tanno _ _ => nomatch hv
    | tcase _ _ _ _ _ => nomatch hv
    | tunfold _ _ => nomatch hv
    | tseal _ _ _ _ _ => nomatch hv
    | tunseal _ _ _ _ _ _ => nomatch hv
    | tbapp _ _ _ => nomatch hv

theorem lookup_pres {A : Typ} {n : Nat} {B : Typ} (hl : Lookup A n B)
    {v v' : Exp} {Γ : Typ} (hv : Value v) (ht : HasType Δ Γ v A) (hlv : LookupV v n v')
    : HasType Δ Γ v' B := by
  induction hl generalizing v v' Γ with
  | zero =>
    cases hlv with
    | lvzero =>
      cases hv with
      | vmrg _ hv₂ =>
        cases ht with
        | tmrg _ h₂ _ _ => exact value_weaken h₂ hv₂
        | tmergev _ _ _ h₂ _ _ => exact value_weaken h₂ hv₂
        | tmergevc _ _ _ h₂ _ _ _ _ _ => exact value_weaken h₂ hv₂
  | succ _ ih =>
    cases hlv with
    | lvsucc hlv' =>
      cases hv with
      | vmrg hv₁ _ =>
        cases ht with
        | tmrg h₁ _ _ _ => exact ih hv₁ h₁ hlv'
        | tmergev _ _ h₁ _ _ _ =>
          exact value_weaken (ih hv₁ h₁ hlv') (lookupv_value hlv' hv₁)
        | tmergevc _ _ h₁ _ _ _ _ _ _ =>
          exact value_weaken (ih hv₁ h₁ hlv') (lookupv_value hlv' hv₁)

-- If l does not occur in the type, the value has no l-selection (Core's notin_false).
theorem lin_absent {v v' : Exp} {l : String} (hlv : RLookupV v l v')
    {Γ B : Typ} (hv : Value v) (ht : HasType Δ Γ v B) (hnl : ¬ Lin l B) : False := by
  induction hlv generalizing Γ B with
  | rvlzero =>
    cases ht with
    | trcd _ => exact hnl Lin.rcd
  | vlandl _ ih =>
    cases hv with
    | vmrg hv₁ _ =>
      cases ht with
      | tmrg h₁ _ _ _ => exact ih hv₁ h₁ (fun hlin => hnl (Lin.andl hlin))
      | tmergev _ _ h₁ _ _ _ => exact ih hv₁ h₁ (fun hlin => hnl (Lin.andl hlin))
      | tmergevc _ _ h₁ _ _ _ _ _ _ => exact ih hv₁ h₁ (fun hlin => hnl (Lin.andl hlin))
  | vlandr _ ih =>
    cases hv with
    | vmrg _ hv₂ =>
      cases ht with
      | tmrg _ h₂ _ _ => exact ih hv₂ h₂ (fun hlin => hnl (Lin.andr hlin))
      | tmergev _ _ _ h₂ _ _ => exact ih hv₂ h₂ (fun hlin => hnl (Lin.andr hlin))
      | tmergevc _ _ _ h₂ _ _ _ _ _ => exact ih hv₂ h₂ (fun hlin => hnl (Lin.andr hlin))

theorem rlookup_prog {B : Typ} {l : String} {A : Typ} (hl : RLookup B l A)
    {v : Exp} {Γ : Typ} (hv : Value v) (ht : HasType Δ Γ v B) : ∃ v', RLookupV v l v' := by
  induction hl generalizing v Γ with
  | zero =>
    cases ht with
    | trcd _ => exact ⟨_, RLookupV.rvlzero⟩
    | tquery => nomatch hv
    | tapp _ _ => nomatch hv
    | tbox _ _ => nomatch hv
    | tproj _ _ => nomatch hv
    | trproj _ _ => nomatch hv
    | tanno _ _ => nomatch hv
    | tcase _ _ _ _ _ => nomatch hv
    | tunfold _ _ => nomatch hv
    | tseal _ _ _ _ _ => nomatch hv
    | tunseal _ _ _ _ _ _ => nomatch hv
    | tbapp _ _ _ => nomatch hv
  | landl _ _ ih =>
    cases ht with
    | tmrg h₁ _ _ _ =>
      cases hv with
      | vmrg hv₁ _ =>
        obtain ⟨v', hlv⟩ := ih hv₁ h₁
        exact ⟨v', RLookupV.vlandl hlv⟩
    | tmergev hv₁ _ h₁ _ _ _ =>
      obtain ⟨v', hlv⟩ := ih hv₁ h₁
      exact ⟨v', RLookupV.vlandl hlv⟩
    | tmergevc hv₁ _ h₁ _ _ _ _ _ _ =>
      obtain ⟨v', hlv⟩ := ih hv₁ h₁
      exact ⟨v', RLookupV.vlandl hlv⟩
    | tquery => nomatch hv
    | tapp _ _ => nomatch hv
    | tbox _ _ => nomatch hv
    | tproj _ _ => nomatch hv
    | trproj _ _ => nomatch hv
    | tanno _ _ => nomatch hv
    | tcase _ _ _ _ _ => nomatch hv
    | tunfold _ _ => nomatch hv
    | tseal _ _ _ _ _ => nomatch hv
    | tunseal _ _ _ _ _ _ => nomatch hv
    | tbapp _ _ _ => nomatch hv
  | landr _ _ ih =>
    cases ht with
    | tmrg _ h₂ _ _ =>
      cases hv with
      | vmrg _ hv₂ =>
        obtain ⟨v', hlv⟩ := ih hv₂ h₂
        exact ⟨v', RLookupV.vlandr hlv⟩
    | tmergev _ hv₂ _ h₂ _ _ =>
      obtain ⟨v', hlv⟩ := ih hv₂ h₂
      exact ⟨v', RLookupV.vlandr hlv⟩
    | tmergevc _ hv₂ _ h₂ _ _ _ _ _ =>
      obtain ⟨v', hlv⟩ := ih hv₂ h₂
      exact ⟨v', RLookupV.vlandr hlv⟩
    | tquery => nomatch hv
    | tapp _ _ => nomatch hv
    | tbox _ _ => nomatch hv
    | tproj _ _ => nomatch hv
    | trproj _ _ => nomatch hv
    | tanno _ _ => nomatch hv
    | tcase _ _ _ _ _ => nomatch hv
    | tunfold _ _ => nomatch hv
    | tseal _ _ _ _ _ => nomatch hv
    | tunseal _ _ _ _ _ _ => nomatch hv
    | tbapp _ _ _ => nomatch hv

theorem rlookup_pres {B : Typ} {l : String} {A : Typ} (hl : RLookup B l A)
    {v v' : Exp} {Γ : Typ} (hv : Value v) (ht : HasType Δ Γ v B) (hlv : RLookupV v l v')
    : HasType Δ Γ v' A := by
  induction hl generalizing v v' Γ with
  | zero =>
    cases hlv with
    | rvlzero =>
      cases ht with
      | trcd h => exact h
    | vlandl hlv' => nomatch ht
    | vlandr hlv' => nomatch ht
  | landl _ hnl ih =>
    cases hlv with
    | rvlzero => nomatch ht
    | vlandl hlv' =>
      cases hv with
      | vmrg hv₁ hv₂ =>
        cases ht with
        | tmrg h₁ _ _ _ => exact ih hv₁ h₁ hlv'
        | tmergev _ _ h₁ _ _ _ =>
          exact value_weaken (ih hv₁ h₁ hlv') (rlookupv_value hlv' hv₁)
        | tmergevc _ _ h₁ _ _ _ _ _ _ =>
          exact value_weaken (ih hv₁ h₁ hlv') (rlookupv_value hlv' hv₁)
    | vlandr hlv' =>
      cases hv with
      | vmrg hv₁ hv₂ =>
        cases ht with
        | tmrg _ h₂ _ _ => exact (lin_absent hlv' hv₂ h₂ hnl).elim
        | tmergev _ _ _ h₂ _ _ => exact (lin_absent hlv' hv₂ h₂ hnl).elim
        | tmergevc _ _ _ h₂ _ _ _ _ _ => exact (lin_absent hlv' hv₂ h₂ hnl).elim
  | landr _ hnl ih =>
    cases hlv with
    | rvlzero => nomatch ht
    | vlandr hlv' =>
      cases hv with
      | vmrg hv₁ hv₂ =>
        cases ht with
        | tmrg _ h₂ _ _ =>
          exact value_weaken (ih hv₂ (value_weaken h₂ hv₂ : HasType Δ .top _ _) hlv')
            (rlookupv_value hlv' hv₂)
        | tmergev _ _ _ h₂ _ _ =>
          exact value_weaken (ih hv₂ h₂ hlv') (rlookupv_value hlv' hv₂)
        | tmergevc _ _ _ h₂ _ _ _ _ _ =>
          exact value_weaken (ih hv₂ h₂ hlv') (rlookupv_value hlv' hv₂)
    | vlandl hlv' =>
      cases hv with
      | vmrg hv₁ hv₂ =>
        cases ht with
        | tmrg h₁ _ _ _ => exact (lin_absent hlv' hv₁ h₁ hnl).elim
        | tmergev _ _ h₁ _ _ _ => exact (lin_absent hlv' hv₁ h₁ hnl).elim
        | tmergevc _ _ h₁ _ _ _ _ _ _ => exact (lin_absent hlv' hv₁ h₁ hnl).elim

-- λE Lemma 4.1: well-typed selection is deterministic — containment rules out the
-- ambiguous branch.
theorem sel_determinism {B : Typ} {l : String} {A : Typ} (hl : RLookup B l A)
    {v v₁ : Exp} {Γ : Typ} (hv : Value v) (ht : HasType Δ Γ v B) (h₁ : RLookupV v l v₁)
    {v₂ : Exp} (h₂ : RLookupV v l v₂) : v₁ = v₂ := by
  induction hl generalizing v v₁ v₂ Γ with
  | zero =>
    cases h₁ with
    | rvlzero =>
      cases h₂ with
      | rvlzero => rfl
    | vlandl h₁' => nomatch ht
    | vlandr h₁' => nomatch ht
  | landl _ hnl ih =>
    cases h₁ with
    | rvlzero => nomatch ht
    | vlandl h₁' =>
      cases hv with
      | vmrg hv₁ hv₂ =>
        cases h₂ with
        | vlandl h₂' =>
          cases ht with
          | tmrg hp _ _ _ => exact ih hv₁ hp h₁' h₂'
          | tmergev _ _ hp _ _ _ => exact ih hv₁ hp h₁' h₂'
          | tmergevc _ _ hp _ _ _ _ _ _ => exact ih hv₁ hp h₁' h₂'
        | vlandr h₂' =>
          cases ht with
          | tmrg _ hq _ _ => exact (lin_absent h₂' hv₂ hq hnl).elim
          | tmergev _ _ _ hq _ _ => exact (lin_absent h₂' hv₂ hq hnl).elim
          | tmergevc _ _ _ hq _ _ _ _ _ => exact (lin_absent h₂' hv₂ hq hnl).elim
    | vlandr h₁' =>
      cases hv with
      | vmrg hv₁ hv₂ =>
        cases ht with
        | tmrg _ hq _ _ => exact (lin_absent h₁' hv₂ hq hnl).elim
        | tmergev _ _ _ hq _ _ => exact (lin_absent h₁' hv₂ hq hnl).elim
        | tmergevc _ _ _ hq _ _ _ _ _ => exact (lin_absent h₁' hv₂ hq hnl).elim
  | landr _ hnl ih =>
    cases h₁ with
    | rvlzero => nomatch ht
    | vlandr h₁' =>
      cases hv with
      | vmrg hv₁ hv₂ =>
        cases h₂ with
        | vlandr h₂' =>
          cases ht with
          | tmrg _ hq _ _ => exact ih hv₂ (value_weaken hq hv₂ : HasType Δ .top _ _) h₁' h₂'
          | tmergev _ _ _ hq _ _ => exact ih hv₂ hq h₁' h₂'
          | tmergevc _ _ _ hq _ _ _ _ _ => exact ih hv₂ hq h₁' h₂'
        | vlandl h₂' =>
          cases ht with
          | tmrg hp _ _ _ => exact (lin_absent h₂' hv₁ hp hnl).elim
          | tmergev _ _ hp _ _ _ => exact (lin_absent h₂' hv₁ hp hnl).elim
          | tmergevc _ _ hp _ _ _ _ _ _ => exact (lin_absent h₂' hv₁ hp hnl).elim
    | vlandl h₁' =>
      cases hv with
      | vmrg hv₁ hv₂ =>
        cases ht with
        | tmrg hp _ _ _ => exact (lin_absent h₁' hv₁ hp hnl).elim
        | tmergev _ _ hp _ _ _ => exact (lin_absent h₁' hv₁ hp hnl).elim
        | tmergevc _ _ hp _ _ _ _ _ _ => exact (lin_absent h₁' hv₁ hp hnl).elim

-- The environment extended by a merge branch stays well-typed: the shared plumbing of
-- smrgr in preservation, progress, and determinism.  This is exactly where the A ∗ Γ
-- premise of tmrg earns its keep.
theorem env_extend_typing {v v₁ : Exp} {Γ A : Typ}
    (hv : Value v) (hv₁ : Value v₁) (henv : HasType Δ .top v Γ) (h₁ : HasType Δ Γ v₁ A)
    (hd : Disj A Γ) : HasType Δ .top (.mrg v v₁) (.and Γ A) := by
  have h₁' : HasType Δ .top v₁ A := value_weaken h₁ hv₁
  exact HasType.tmergev hv hv₁ henv h₁' (disj_symm hd)
    (disjoint_consistent hv hv₁ henv h₁' (disj_symm hd))

end Seal
