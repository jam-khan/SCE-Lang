import LeanSce.Core.Syntax
import LeanSce.Core.Properties

open Core

inductive EBig : Exp → Exp → Exp → Prop where
  | eblit {v : Exp} {i : Nat}
    : Value v
    → EBig v (.lit i) (.lit i)
  | ebunit {v : Exp}
    : Value v
    → EBig v .unit .unit
  | ebmrg {v e₁ e₂ v₁ v₂ : Exp}
    : EBig v e₁ v₁
    → EBig (.mrg v v₁) e₂ v₂
    → EBig v (.mrg e₁ e₂) (.mrg v₁ v₂)
  | ebclos {v : Exp} {A : Typ} {e : Exp}
    : Value v
    → EBig v (.lam A e) (.clos v A e)
  | ebapp {v e₁ e₂ v₁ v₂ vr e : Exp} {A : Typ}
    : EBig v e₁ (.clos v₂ A e)
    → EBig v e₂ v₁
    → EBig (.mrg v₂ v₁) e vr
    → EBig v (.app e₁ e₂) vr
  | ebbox {v e₁ e₂ v₁ vr : Exp}
    : EBig v e₁ v₁
    → EBig v₁ e₂ vr
    → EBig v (.box e₁ e₂) vr
  | eclos {v v₁ : Exp} {A : Typ} {e : Exp}
    : Value v
    → Value v₁
    → EBig v (.clos v₁ A e) (.clos v₁ A e)
  | equery {e : Exp}
    : Value e
    → EBig e .query e
  | ebproj {e a v v' : Exp} {n : Nat}
    : EBig e a v
    → LookupV v n v'
    → EBig e (.proj a n) v'
  | ebrec {e a v : Exp} {l : String}
    : EBig e a v
    → EBig e (.lrec l a) (.lrec l v)
  | ebsel {e a v₁ v₂ : Exp} {l : String}
    : EBig e a v₁
    → RLookupV v₁ l v₂
    → EBig e (.rproj a l) v₂
  | ebinl {e a v : Exp} {B : Typ}
    : EBig e a v
    → EBig e (.inl B a) (.inl B v)
  | ebinr {e a v : Exp} {A : Typ}
    : EBig e a v
    → EBig e (.inr A a) (.inr A v)
  | ebcasel {ρ e e₁ e₂ v₁ v : Exp} {B : Typ}
    : EBig ρ e (.inl B v₁)
    → EBig (.mrg ρ v₁) e₁ v
    → EBig ρ (.case e e₁ e₂) v
  | ebcaser {ρ e e₁ e₂ v₁ v : Exp} {A : Typ}
    : EBig ρ e (.inr A v₁)
    → EBig (.mrg ρ v₁) e₂ v
    → EBig ρ (.case e e₁ e₂) v
  | ebflam {v : Exp} {A B : Typ} {e : Exp}
    : Value v
    → EBig v (.flam A B e) (.fclos v A B e)
  | efclos {v v₁ : Exp} {A B : Typ} {e : Exp}
    : Value v
    → Value v₁
    → EBig v (.fclos v₁ A B e) (.fclos v₁ A B e)
  | ebfapp {v e₁ e₂ v₁ v₂ vr e : Exp} {A B : Typ}
    : EBig v e₁ (.fclos v₂ A B e)
    → EBig v e₂ v₁
    → EBig (.mrg (.mrg v₂ (.fclos v₂ A B e)) v₁) e vr
    → EBig v (.app e₁ e₂) vr
  | ebfold {e a v : Exp} {T : Typ}
    : EBig e a v
    → EBig e (.fold T a) (.fold T v)
  | ebunfold {ρ e v : Exp} {T : Typ}
    : EBig ρ e (.fold T v)
    → EBig ρ (.unfold e) v

theorem ebig_produces_value
    {v e v' : Core.Exp}
    (hval : Core.Value v)
    (hbig : EBig v e v')
    : Core.Value v' := by
  induction hbig with
  | eblit _ => exact Value.vint
  | ebunit _ => exact Value.vunit
  | ebmrg _ _ ih1 ih2 => exact Value.vmrg (ih1 hval) (ih2 (Value.vmrg hval (ih1 hval)))
  | ebclos hv => exact Value.vclos hv
  | ebapp _ _ _ ih1 ih2 ih3 =>
    have hclos := ih1 hval
    cases hclos with | vclos hv => exact ih3 (Value.vmrg hv (ih2 hval))
  | ebbox _ _ ih1 ih2 => exact ih2 (ih1 hval)
  | eclos _ hv1 => exact Value.vclos hv1
  | equery hv => exact hv
  | ebproj _ hlook ih =>
    exact lookupv_value hlook (ih hval)
  | ebrec _ ih => exact Value.vrcd (ih hval)
  | ebsel _ hsel ih =>
    exact rlookupv_value hsel (ih hval)
  | ebinl _ ih => exact Value.vinl (ih hval)
  | ebinr _ ih => exact Value.vinr (ih hval)
  | ebcasel _ _ ih1 ih2 =>
    have hinl := ih1 hval
    cases hinl with | vinl hv1 => exact ih2 (Value.vmrg hval hv1)
  | ebcaser _ _ ih1 ih2 =>
    have hinr := ih1 hval
    cases hinr with | vinr hv1 => exact ih2 (Value.vmrg hval hv1)
  | ebflam hv => exact Value.vfclos hv
  | efclos _ hv1 => exact Value.vfclos hv1
  | ebfapp _ _ _ ih1 ih2 ih3 =>
    have hclos := ih1 hval
    cases hclos with
    | vfclos hv => exact ih3 (Value.vmrg (Value.vmrg hv (Value.vfclos hv)) (ih2 hval))
  | ebfold _ ih => exact Value.vfold (ih hval)
  | ebunfold _ ih =>
    have hfold := ih hval
    cases hfold with | vfold hv => exact hv

theorem ebig_env_value {env e v : Core.Exp} (h : EBig env e v) : Core.Value env := by
  induction h with
  | ebmrg _ _ ih1 _ => exact ih1
  | ebapp _ _ _ ih1 _ _ => exact ih1
  | ebbox _ _ ih1 _ => exact ih1
  | ebproj _ _ ih => exact ih
  | ebrec _ ih => exact ih
  | ebsel _ _ ih => exact ih
  | ebinl _ ih => exact ih
  | ebinr _ ih => exact ih
  | ebcasel _ _ ih1 _ => exact ih1
  | ebcaser _ _ ih1 _ => exact ih1
  | ebfapp _ _ _ ih1 _ _ => exact ih1
  | ebfold _ ih => exact ih
  | ebunfold _ ih => exact ih
  | _ => assumption
