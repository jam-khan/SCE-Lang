import LeanSce.Core.Syntax
import LeanSce.Core.Typing.Typing
import LeanSce.Core.Semantics.SmallStep
import LeanSce.Core.Properties

open Core

theorem gprogress
  {E A : Typ} {e : Exp}
  {htype : HasType E e A} :
  ∀ {v : Exp},
  Value v
  → HasType .top v E
  → (Value e) ∨ (∃ e' : Exp, Step v e e') := by
  induction htype with
  | tquery =>
    rename_i Γ
    intro v hv henv
    right
    exists v
    exact Step.squery hv
  | tint =>
    rename_i Γ n
    intro v hv henv
    left
    exact Value.vint
  | tunit =>
    rename_i Γ
    intro v hv henv
    left
    exact Value.vunit
  | tapp htype1 htype2 ih1 ih2 =>
    rename_i Γ A B e1 e2
    intro v hv henv
    have h1 := ih1 hv henv
    have h2 := ih2 hv henv
    cases h1 with
    | inr h =>
      obtain ⟨e', hstep1⟩ := h
      right
      exists (.app e' e2)
      exact Step.sappl hv hstep1
    | inl hve1 =>
      right
      cases h2 with
      | inr h =>
        obtain ⟨e', hstep1⟩ := h
        exists (.app e1 e')
        exact Step.sappr hv hve1 hstep1
      | inl h =>
          cases hve1 with
          | vclos hvc =>
            cases htype1 with
            | tclos hv' ht' hb =>
              exact ⟨_, Step.sbeta hv h hvc⟩
          | vfclos hvc =>
            cases htype1 with
            | tfclos hv' ht' hb =>
              exact ⟨_, Step.sfbeta hv h hvc⟩
          | _ =>
            cases htype1
  | tbox htyp1 htyp2 ih1 ih2 =>
    rename_i Γ Γ₁ A e1 e2
    intro v hv henv
    have h1 := ih1 hv henv
    cases h1 with
    | inr h =>
      obtain ⟨e'', hstep⟩ := h
      right <;> exact ⟨_, Step.sboxl hv hstep⟩
    | inl hv1 =>
      right
      have henv2 : HasType .top e1 Γ₁ := value_weaken htyp1 hv1
      have h2 := ih2 hv1 henv2
      cases h2 with
      | inr h =>
        have ⟨e', hstep⟩ := h
        exists (.box e1 e')
        exact Step.sboxr hv hv1 hstep
      | inl hv' =>
        exists e2
        exact Step.sboxv hv hv1 hv'
  | tmrg htyp1 htyp2 ih1 ih2 =>
    rename_i Γ A B e1 e2
    intro v hv henv
    have h1 := ih1 hv henv
    cases h1 with
    | inr h =>
      obtain ⟨e', hstep⟩ := h
      right
      exact ⟨_, Step.smrgl hv hstep⟩
    | inl hve1 =>
      have henv' : HasType .top (.mrg v e1) (Γ.and A) :=
        HasType.tmrg henv (value_weaken htyp1 hve1)
      have h2 := ih2 (Value.vmrg hv hve1) henv'
      cases h2 with
      | inr h =>
        obtain ⟨e', hstep⟩ := h
        right
        exact ⟨_, Step.smrgr hv hve1 hstep⟩
      | inl hve2 =>
        left
        exact Value.vmrg hve1 hve2
  | tlam htyp ih1 =>
    rename_i Γ A1 B e1
    intro v hv henv
    right
    exists (.clos v A1 e1)
    exact Step.sclos hv
  | tclos hv htyp1 htyp2 ih1 ih2 =>
    rename_i Γ Γ₁ A1 B1 e1 e2
    intro v hv henv
    left
    (expose_names; exact Value.vclos hv_1)
  | tproj htyp1 hlookup ih1 =>
    rename_i Γ A B e1 n
    intro v hv henv
    right
    have h1 := ih1 hv henv
    cases h1 with
    | inr h =>
      obtain ⟨e', hstep⟩ := h
      exists (.proj e' n)
      exact Step.sproj hv hstep
    | inl h =>
      have htyp_top : HasType .top e1 A := value_weaken htyp1 h
      have ⟨v', hlv⟩ := lookup_prog hlookup htyp_top h
      exact ⟨_, Step.sprojv hv h hlv⟩
  | trcd htype ih1 =>
    intro v hv henv
    rename_i Γ A1 l e1
    have h1 := ih1 hv henv
    cases h1 with
    | inr h =>
      obtain ⟨e', hstep⟩ := h
      right
      exists (.lrec l e')
      exact Step.slrec hv hstep
    | inl h =>
      left
      exact Value.vrcd h
  | trproj htyp1 hlookup ih1 =>
    rename_i Γ A B l e1
    intro v hv henv
    have h1 := ih1 hv henv
    cases h1 with
    | inr h =>
      obtain ⟨e', hstep⟩ := h
      right
      exists (.rproj e' l)
      exact Step.srproj hv hstep
    | inl h =>
      right
      have htyp_top : HasType .top e1 B := value_weaken htyp1 h
      have ⟨v', hlv⟩ := rlookup_prog hlookup htyp_top h
      exact ⟨_, Step.srprojv hv h hlv⟩
  | tinl htyp ih =>
    intro v hv henv
    cases ih hv henv with
    | inl hve => left; exact Value.vinl hve
    | inr h =>
      obtain ⟨e', hstep⟩ := h
      right
      exact ⟨_, Step.sinl hv hstep⟩
  | tinr htyp ih =>
    intro v hv henv
    cases ih hv henv with
    | inl hve => left; exact Value.vinr hve
    | inr h =>
      obtain ⟨e', hstep⟩ := h
      right
      exact ⟨_, Step.sinr hv hstep⟩
  | tflam htyp ih =>
    intro v hv henv
    right
    exact ⟨_, Step.sfclos hv⟩
  | tfclos hv' htyp1 htyp2 ih1 ih2 =>
    intro v hv henv
    left
    exact Value.vfclos hv'
  | tfold htyp ih =>
    intro v hv henv
    cases ih hv henv with
    | inl hve => left; exact Value.vfold hve
    | inr h =>
      obtain ⟨e', hstep⟩ := h
      right
      exact ⟨_, Step.sfold hv hstep⟩
  | tunfold htyp heq ih =>
    intro v hv henv
    right
    cases ih hv henv with
    | inr h =>
      obtain ⟨e', hstep⟩ := h
      exact ⟨_, Step.sunfold hv hstep⟩
    | inl hve =>
      match hve with
      | .vfold hv1 => exact ⟨_, Step.sunfoldv hv hv1⟩
      | .vint => cases htyp
      | .vunit => cases htyp
      | .vclos _ => cases htyp
      | .vrcd _ => cases htyp
      | .vmrg _ _ => cases htyp
      | .vinl _ => cases htyp
      | .vinr _ => cases htyp
      | .vfclos _ => cases htyp
  | tcase htyp h1 h2 ih ih1 ih2 =>
    rename_i Γ A B C e e1 e2
    intro v hv henv
    right
    cases ih hv henv with
    | inr h =>
      obtain ⟨e', hstep⟩ := h
      exact ⟨_, Step.scase hv hstep⟩
    | inl hve =>
      match hve with
      | .vinl hv1 => exact ⟨_, Step.scasel hv hv1⟩
      | .vinr hv1 => exact ⟨_, Step.scaser hv hv1⟩
      | .vint => cases htyp
      | .vunit => cases htyp
      | .vclos _ => cases htyp
      | .vrcd _ => cases htyp
      | .vmrg _ _ => cases htyp

theorem progress {e A}
  : HasType .top e A
  →   Value e
    ∨ ∃ e', Step .unit e e' := by
  intros htype
  apply gprogress <;> try assumption
  · exact Value.vunit
  · exact HasType.tunit
