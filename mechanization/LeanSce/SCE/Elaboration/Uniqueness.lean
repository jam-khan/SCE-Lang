import LeanSce.Core.Syntax
import LeanSce.Core.Typing.Typing
import LeanSce.SCE.Syntax
import LeanSce.SCE.Elaboration.Elaboration

/-!
Uniqueness of elaboration: source lookups are functional, and `elabExp` is
syntax-directed — a term has at most one source type and one Core term.
-/

open SCE Core

theorem index_lookup_uniqueness
    {T T₁ T₂ : SCE.Typ} {n : Nat}
    (h₁ : SLookup T n T₁)
    (h₂ : SLookup T n T₂)
    : T₁ = T₂ := by
  induction h₁ with
  | zero A B => cases h₂; rfl
  | succ A B n C _ ih => cases h₂ with | succ _ _ _ _ h₂ => exact ih h₂

theorem record_lookup_uniqueness
    {T T₁ T₂ : SCE.Typ} {l : String}
    (h₁ : SCE.SRLookup T l T₁)
    (h₂ : SCE.SRLookup T l T₂)
    : T₁ = T₂ := by
  induction h₁ with
  | zero l T => cases h₂; rfl
  | andl A B l T hsr h_cond ih =>
    cases h₂ with
    | andl _ _ _ _ h₂' _ => exact ih h₂'
    | andr _ _ _ _ h₂' h_cond₂ =>
      exact absurd (SCE.srlookup_labelin hsr) h_cond₂
  | andr A B l T hsr h_cond ih =>
    cases h₂ with
    | andr _ _ _ _ h₂' _ => exact ih h₂'
    | andl _ _ _ _ h₂' h_cond₂ =>
      exact absurd (SCE.srlookup_labelin hsr) h_cond₂
  | sig A l T hsr ih =>
    cases h₂ with
    | sig _ _ _ h₂' => exact ih h₂'

theorem elaboration_inference_uniqueness
    {Γ T₁ T₂ : SCE.Typ} {e : SCE.Exp} {ce₁ ce₂ : Core.Exp}
    (h₁ : elabExp Γ e T₁ ce₁)
    (h₂ : elabExp Γ e T₂ ce₂)
    : T₁ = T₂ := by
  revert T₂ ce₂
  induction h₁ with
  | equery =>
    intro ce₂ T₂ h₂; cases h₂; rfl
  | elit _ n =>
    intro ce₂ T₂ h₂; cases h₂; rfl
  | eunit _ =>
    intro ce₂ T₂ h₂; cases h₂; rfl
  | eapp ctx A B se1 se2 ce1 ce2 _ _ ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | eapp _ a' _ _ _ ce1' ce2' h1' h2' =>
      have := ih1 h1'
      cases this; rfl
  | eproj ctx A B se ce i _ hlook ih =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | eproj _ a' _ _ ce' _ h' hlook' =>
      have hA := ih h'
      rw [hA] at hlook
      exact index_lookup_uniqueness hlook hlook'
  | ebox ctx ctx' A se1 se2 ce1 ce2 _ _ ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | ebox _ en _ _ _ ce1' ce2' h1' h2' =>
      have hA := ih1 h1'
      rw [hA] at ih2
      exact ih2 h2'
  | edmrg ctx A B se1 se2 ce1 ce2 _ _ ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | edmrg _ a' b' _ _ ce1' ce2' h1' h2' =>
      have hA := ih1 h1'
      have hB := ih2 (hA ▸ h2')
      rw [hA, hB]
  | enmrg ctx A B se1 se2 ce1 ce2 _ _ ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | enmrg _ a' b' _ _ ce1' ce2' h1' h2' =>
      have hA := ih1 h1'
      have hB := ih2 h2'
      rw [hA, hB]
  | elam ctx A B se ce _ ih =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | elam _ _ b' _ ce' h' =>
      have hB := ih h'
      rw [hB]
  | erproj ctx A B se ce l _ hlook ih =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | erproj _ a' b' _ ce' _ h' hlook' =>
      have hB := ih h'
      rw [hB] at hlook
      exact record_lookup_uniqueness hlook hlook'
  | eclos ctx ctx' A B se1 se2 ce1 ce2 _ _ _ ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | eclos _ et _ bT _ _ ce1' ce2' _ h1' h2' =>
      have hA := ih1 h1'
      have hB := ih2 (hA ▸ h2')
      rw [hB]
  | elrec ctx A se ce l _ ih =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | elrec _ a' _ ce' _ h' =>
      have hA := ih h'
      rw [hA]
  | letb ctx A B se1 se2 ce1 ce2 _ _ ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | letb _ a' b' _ _ ce1' ce2' h1' h2' =>
      have hA := ih1 h1'
      cases hA
      exact ih2 h2'
  | openm ctx A B se1 se2 ce1 ce2 l _ _ ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | openm _ a' b' _ _ ce1' ce2' _ h1' h2' =>
      have hA : SCE.Typ.rcd l A = SCE.Typ.rcd _ a' := ih1 h1'
      cases hA
      exact ih2 h2'
  | mstruct ctx B se ce _ ih =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | mstruct _ b' _ ce' h' =>
      rw [ih h']
  | mfunctor ctx ctxInner A B sb se ce _ _ _ ih =>
    intro ce₂ T₂ h₂
    rename_i hs1 hs2 el1
    cases h₂ with
    | mfunctor _ ci' _ b' _ _ ce' hs1' hs2' h' =>
      have hCtx : ctxInner = ci' := by
        cases sb with
        | sandboxed => rw [hs1 rfl, hs1' rfl]
        | open_ => rw [hs2 rfl, hs2' rfl]
      rw [← hCtx] at h'
      have hB := ih h'
      rw [hB]
  | mclos ctx ctx' A B se1 se2 ce1 ce2 _ _ _ ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | mclos _ et _ bT _ _ ce1' ce2' _ h1' h2' =>
      have hA := ih1 h1'
      rw [← hA] at h2'
      have hB := ih2 h2'
      rw [hB]
  | mapp ctx A mt se1 se2 ce1 ce2 _ _ ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | mapp _ a' mt' _ _ ce1' ce2' h1' h2' =>
      have hA := ih2 h2'
      have := ih1 h1'
      rw [hA] at this
      cases this; rfl
  | mlink ctx Γ₁ A mt l se1 se2 ce1 ce2 _ _ _ ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | mlink _ Γ₁' A' mt' l' _ _ ce1' ce2' h1' h2' _ =>
      have hΓ := ih1 h1'
      have := ih2 h2'
      cases this
      rw [hΓ]
  | mlinkn ctx Γ₁ D B se1 se2 ce1 ce2 _ _ _ ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | mlinkn _ Γ₁' D' B' _ _ ce1' ce2' h1' h2' _ =>
      have hΓ := ih1 h1'
      have := ih2 h2'
      cases this
      rw [hΓ]
  | einl ctx A B se ce _ ih =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | einl _ a' _ _ ce' h' =>
      have hA := ih h'
      rw [hA]
  | einr ctx A B se ce _ ih =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | einr _ _ b' _ ce' h' =>
      have hB := ih h'
      rw [hB]
  | ecase ctx A B C se se1 se2 ce ce1 ce2 _ _ _ ih ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | ecase _ a' b' c' _ _ _ ce' ce1' ce2' h' h1' h2' =>
      have hor := ih h'
      cases hor
      exact ih1 h1'
  | eflam ctx A B se ce _ ih =>
    intro ce₂ T₂ h₂
    cases h₂
    rfl
  | efclos ctx ctx' A B se1 se2 ce1 ce2 _ _ _ ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂
    rfl
  | efold ctx T se ce _ ih =>
    intro ce₂ T₂ h₂
    cases h₂
    rfl
  | eunfold ctx T A se ce _ heq ih =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | eunfold _ T' _ _ ce' h' heq' =>
      have hmu := ih h'
      cases hmu
      rw [heq, heq']

/-- A source expression has at most one type in a given context. -/
theorem inference_uniqueness
    {Γ A₁ A₂ : SCE.Typ} {e : SCE.Exp}
    (h₁ : SCE.HasType Γ e A₁)
    (h₂ : SCE.HasType Γ e A₂)
    : A₁ = A₂ := by
  obtain ⟨ce₁, helab₁⟩ := h₁
  obtain ⟨ce₂, helab₂⟩ := h₂
  exact elaboration_inference_uniqueness helab₁ helab₂

theorem elaboration_uniqueness
    {Γ T₁ T₂ : SCE.Typ} {e : SCE.Exp} {ce₁ ce₂ : Core.Exp}
    (h₁ : elabExp Γ e T₁ ce₁)
    (h₂ : elabExp Γ e T₂ ce₂)
    : ce₁ = ce₂ := by
  revert T₂ ce₂
  induction h₁ with
  | equery =>
    intro ce₂ T₂ h₂; cases h₂; rfl
  | elit _ n =>
    intro ce₂ T₂ h₂; cases h₂; rfl
  | eunit _ =>
    intro ce₂ T₂ h₂; cases h₂; rfl
  | eapp ctx A B se1 se2 ce1 ce2 _ _ ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | eapp _ a' _ _ _ ce1' ce2' h1' h2' =>
      have hA := ih1 h1'
      have hB := ih2 h2'
      rw [hA, hB]
  | eproj ctx A B se ce i _ hlook ih =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | eproj _ a' _ _ ce' _ h' hlook' =>
      have hA := ih h'
      rw [hA]
  | ebox ctx ctx' A se1 se2 ce1 ce2 h1_orig h2_orig ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | ebox _ en _ _ _ ce1' ce2' h1' h2' =>
      have hce1 := ih1 h1'
      have hctx := elaboration_inference_uniqueness h1_orig h1'
      rw [← hctx] at h2'
      have hce2 := ih2 h2'
      rw [hce1, hce2]
  | edmrg ctx A B se1 se2 ce1 ce2 h1_orig h2_orig ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | edmrg _ a' b' _ _ ce1' ce2' h1' h2' =>
      have hce1 := ih1 h1'
      have hA := elaboration_inference_uniqueness h1_orig h1'
      rw [← hA] at h2'
      have hce2 := ih2 h2'
      rw [hce1, hce2]
  | enmrg ctx A B se1 se2 ce1 ce2 _ _ ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | enmrg _ a' b' _ _ ce1' ce2' h1' h2' =>
      rw [ih1 h1', ih2 h2']
  | elam ctx A B se ce _ ih =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | elam _ _ b' _ ce' h' =>
      have hce := ih h'
      rw [hce]
  | erproj ctx A B se ce l _ hlook ih =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | erproj _ a' b' _ ce' _ h' hlook' =>
      have hce := ih h'
      rw [hce]
  | eclos ctx ctx' A B se1 se2 ce1 ce2 hval h1_orig h2_orig ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | eclos _ et _ bT _ _ ce1' ce2' _ h1' h2' =>
      have hce1 := ih1 h1'
      have hctx := elaboration_inference_uniqueness h1_orig h1'
      rw [← hctx] at h2'
      have hce2 := ih2 h2'
      rw [hce1, hce2]
  | elrec ctx A se ce l _ ih =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | elrec _ a' _ ce' _ h' =>
      have hce := ih h'
      rw [hce]
  | letb ctx A B se1 se2 ce1 ce2 h1_orig _ ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | letb _ a' b' _ _ ce1' ce2' h1' h2' =>
      have hA := elaboration_inference_uniqueness h1_orig h1'
      cases hA
      have hce1 := ih1 h1'
      have hce2 := ih2 h2'
      rw [hce1, hce2]
  | openm ctx A B se1 se2 ce1 ce2 l h1_orig h2_orig ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | openm _ a' b' _ _ ce1' ce2' _ h1' h2' =>
      have htyp : SCE.Typ.rcd l A = SCE.Typ.rcd _ a' := elaboration_inference_uniqueness h1_orig h1'
      cases htyp
      have hce1 := ih1 h1'
      have hce2 := ih2 h2'
      rw [hce1, hce2]
  | mstruct ctx B se ce _ ih =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | mstruct _ b' _ ce' h' => exact ih h'
  | mfunctor ctx ctxInner A B sb se ce _ _ _ ih =>
    intro ce₂ T₂ h₂
    rename_i hs1 hs2 el1
    cases h₂ with
    | mfunctor _ ci' _ b' _ _ ce' hs1' hs2' h' =>
      have hCtx : ctxInner = ci' := by
        cases sb with
        | sandboxed => rw [hs1 rfl, hs1' rfl]
        | open_ => rw [hs2 rfl, hs2' rfl]
      rw [← hCtx] at h'
      have hce := ih h'
      rw [hce]
  | mclos ctx ctx' A B se1 se2 ce1 ce2 hval h1_orig h2_orig ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | mclos _ et _ bT _ _ ce1' ce2' _ h1' h2' =>
      have hce1 := ih1 h1'
      have hctx := elaboration_inference_uniqueness h1_orig h1'
      rw [← hctx] at h2'
      have hce2 := ih2 h2'
      rw [hce1, hce2]
  | mapp ctx A mt se1 se2 ce1 ce2 _ _ ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | mapp _ a' mt' _ _ ce1' ce2' h1' h2' =>
      have hce1 := ih1 h1'
      have hce2 := ih2 h2'
      rw [hce1, hce2]
  | mlink ctx Γ₁ A mt l se1 se2 ce1 ce2 h1_orig h2_orig _ ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | mlink _ Γ₁' A' mt' l' _ _ ce1' ce2' h1' h2' _ =>
      have hce1 := ih1 h1'
      have hce2 := ih2 h2'
      have htyp := elaboration_inference_uniqueness h2_orig h2'
      cases htyp
      have hΓ := elaboration_inference_uniqueness h1_orig h1'
      rw [hce1, hce2, hΓ]
  | mlinkn ctx Γ₁ D B se1 se2 ce1 ce2 h1_orig h2_orig _ ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | mlinkn _ Γ₁' D' B' _ _ ce1' ce2' h1' h2' _ =>
      have hce1 := ih1 h1'
      have hce2 := ih2 h2'
      have htyp := elaboration_inference_uniqueness h2_orig h2'
      cases htyp
      have hΓ := elaboration_inference_uniqueness h1_orig h1'
      rw [hce1, hce2, hΓ]
  | einl ctx A B se ce _ ih =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | einl _ a' _ _ ce' h' =>
      have hce := ih h'
      rw [hce]
  | einr ctx A B se ce _ ih =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | einr _ _ b' _ ce' h' =>
      have hce := ih h'
      rw [hce]
  | ecase ctx A B C se se1 se2 ce ce1 ce2 h_orig _ _ ih ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | ecase _ a' b' c' _ _ _ ce' ce1' ce2' h' h1' h2' =>
      have hor := elaboration_inference_uniqueness h_orig h'
      cases hor
      have hce := ih h'
      have hce1 := ih1 h1'
      have hce2 := ih2 h2'
      rw [hce, hce1, hce2]
  | eflam ctx A B se ce _ ih =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | eflam _ _ _ _ ce' h' =>
      have hce := ih h'
      rw [hce]
  | efclos ctx ctx' A B se1 se2 ce1 ce2 hval h1_orig h2_orig ih1 ih2 =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | efclos _ et _ _ _ _ ce1' ce2' _ h1' h2' =>
      have hce1 := ih1 h1'
      have hctx := elaboration_inference_uniqueness h1_orig h1'
      rw [← hctx] at h2'
      have hce2 := ih2 h2'
      rw [hce1, hce2]
  | efold ctx T se ce _ ih =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | efold _ _ _ ce' h' =>
      have hce := ih h'
      rw [hce]
  | eunfold ctx T A se ce h_orig heq ih =>
    intro ce₂ T₂ h₂
    cases h₂ with
    | eunfold _ T' _ _ ce' h' heq' =>
      have hmu := elaboration_inference_uniqueness h_orig h'
      cases hmu
      have hce := ih h'
      rw [hce]
