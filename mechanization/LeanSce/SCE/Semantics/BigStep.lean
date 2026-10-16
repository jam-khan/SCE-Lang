import LeanSce.SCE.Syntax

open SCE

namespace S_Sem

inductive LookupV : Exp → Nat → Exp → Prop where
  | dmrg_zero {v₁ v₂ : Exp}
    : LookupV (.mrg v₁ v₂) 0 v₂
  | dmrg_succ {v₁ v₂ v' : Exp} {n : Nat}
    : LookupV v₁ n v'
    → LookupV (.mrg v₁ v₂) (n + 1) v'
  | nmrg_zero {v₁ v₂ : Exp}
    : LookupV (.nmrg v₁ v₂) 0 v₂
  | nmrg_succ {v₁ v₂ v' : Exp} {n : Nat}
    : LookupV v₁ n v'
    → LookupV (.nmrg v₁ v₂) (n + 1) v'

inductive Sel : Exp → String → Exp → Prop where
  | rcd {l : String} {v : Exp}
    : Sel (.lrec l v) l v
  | dmrg_left {v₁ v₂ v' : Exp} {l : String}
    : Sel v₁ l v'
    → Sel (.mrg v₁ v₂) l v'
  | dmrg_right {v₁ v₂ v' : Exp} {l : String}
    : Sel v₂ l v'
    → Sel (.mrg v₁ v₂) l v'
  | nmrg_left {v₁ v₂ v' : Exp} {l : String}
    : Sel v₁ l v'
    → Sel (.nmrg v₁ v₂) l v'
  | nmrg_right {v₁ v₂ v' : Exp} {l : String}
    : Sel v₂ l v'
    → Sel (.nmrg v₁ v₂) l v'
  -- a struct value is transparent for selection (mirrors SRLookup.sig)
  | mstruct {v v' : Exp} {l : String}
    : Sel v l v'
    → Sel (.mstruct v) l v'

-- SelPkg v D pkg: extract from the module value v the record package pkg
-- shaped after the import interface D (one Sel per labeled import)
inductive SelPkg : Exp → Typ → Exp → Prop where
  | one {v : Exp} {l : String} {A : Typ} {vl : Exp}
    : Sel v l vl
    → SelPkg v (.rcd l A) (.lrec l vl)
  | more {v : Exp} {D : Typ} {pkg : Exp} {l : String} {A : Typ} {vl : Exp}
    : SelPkg v D pkg
    → Sel v l vl
    → SelPkg v (.and D (.rcd l A)) (.mrg pkg (.lrec l vl))

theorem sel_value {v v' : Exp} {l : String}
    (hsel : Sel v l v') (hv : Value v) : Value v' := by
  induction hsel with
  | rcd => cases hv; assumption
  | dmrg_left _ ih => cases hv with | vmrg h1 h2 => exact ih h1
  | dmrg_right _ ih => cases hv with | vmrg h1 h2 => exact ih h2
  | nmrg_left _ ih => cases hv
  | nmrg_right _ ih => cases hv
  | mstruct _ ih => cases hv with | vmstruct h => exact ih h

theorem selpkg_value {v : Exp} {D : Typ} {pkg : Exp}
    (hsp : SelPkg v D pkg) (hv : Value v) : Value pkg := by
  induction hsp with
  | one hsel => exact Value.vlrec (sel_value hsel hv)
  | more _ hsel ih => exact Value.vmrg ih (Value.vlrec (sel_value hsel hv))

inductive BStep : Exp → Exp → Exp → Prop where
  | query {ρ : Exp}
    : Value ρ
    → BStep ρ .query ρ
  | lit {ρ : Exp} {n : Nat}
    : Value ρ
    → BStep ρ (.lit n) (.lit n)
  | unit {ρ : Exp}
    : Value ρ
    → BStep ρ .unit .unit
  | clos_val {ρ v : Exp} {A : Typ} {body : Exp}
    : Value ρ
    → Value v
    → BStep ρ (.clos v A body) (.clos v A body)
  | mclos_val {ρ v : Exp} {A : Typ} {body : Exp}
    : Value ρ
    → Value v
    → BStep ρ (.mclos v A body) (.mclos v A body)
  | proj {ρ e v v' : Exp} {n : Nat}
    : Value ρ
    → BStep ρ e v
    → LookupV v n v'
    → BStep ρ (.proj e n) v'
  | lam {ρ : Exp} {A : Typ} {body : Exp}
    : Value ρ
    → BStep ρ (.lam A body) (.clos ρ A body)
  | box {ρ e₁ e₂ v₁ v : Exp}
    : Value ρ
    → BStep ρ e₁ v₁
    → BStep v₁ e₂ v
    → BStep ρ (.box e₁ e₂) v
  | app_clos {ρ e₁ e₂ v₁ v₂ v : Exp} {A : Typ} {body : Exp}
    : Value ρ
    → BStep ρ e₁ (.clos v₁ A body)
    → BStep ρ e₂ v₂
    → BStep (.mrg v₁ v₂) body v
    → BStep ρ (.app e₁ e₂) v
  | app_mclos {ρ e₁ e₂ v₁ v₂ v : Exp} {A : Typ} {body : Exp}
    : Value ρ
    → BStep ρ e₁ (.mclos v₁ A body)
    → BStep ρ e₂ v₂
    → BStep (.mrg v₁ v₂) body v
    → BStep ρ (.mapp e₁ e₂) v
  | dmrg {ρ e₁ e₂ v₁ v₂ : Exp}
    : Value ρ
    → BStep ρ e₁ v₁
    → BStep (.mrg ρ v₁) e₂ v₂
    → BStep ρ (.mrg e₁ e₂) (.mrg v₁ v₂)
  | nmrg {ρ e₁ e₂ v₁ v₂ : Exp}
    : Value ρ
    → BStep ρ e₁ v₁
    → BStep ρ e₂ v₂
    → BStep ρ (.nmrg e₁ e₂) (.mrg v₁ v₂)
  | lrec {ρ e v : Exp} {l : String}
    : Value ρ
    → BStep ρ e v
    → BStep ρ (.lrec l e) (.lrec l v)
  | rproj {ρ e v v' : Exp} {l : String}
    : Value ρ
    → BStep ρ e v
    → Sel v l v'
    → BStep ρ (.rproj e l) v'
  | letb {ρ e₁ e₂ v₁ v : Exp}
    : Value ρ
    → BStep ρ e₁ v₁
    → BStep (.mrg ρ v₁) e₂ v
    → BStep ρ (.letb e₁ e₂) v
  | openm {ρ e₁ e₂ v' v : Exp} {l : String}
    : Value ρ
    → BStep ρ e₁ (.lrec l v')
    → BStep (.mrg ρ v') e₂ v
    → BStep ρ (.openm e₁ e₂) v
  | mstruct {ρ body v : Exp}
    : Value ρ
    → BStep ρ body v
    → BStep ρ (.mstruct body) (.mstruct v)
  | mfunctor_sandboxed {ρ : Exp} {A : Typ} {body : Exp}
    : Value ρ
    → BStep ρ (.mfunctor .sandboxed A body) (.mclos .unit A body)
  | mfunctor_open {ρ : Exp} {A : Typ} {body : Exp}
    : Value ρ
    → BStep ρ (.mfunctor .open_ A body) (.mclos ρ A body)
| mlink {ρ e₁ e₂ v₁ v₂ vₗ v₃ : Exp} {A : Typ} {body : Exp} {l : String}
    : Value ρ
    → BStep ρ e₁ v₁
    → BStep ρ e₂ (.mclos v₂ (.rcd l A) body)
    → Sel v₁ l vₗ
    → BStep (.mrg v₂ (.lrec l vₗ)) body v₃
    → BStep ρ (.mlink e₁ e₂) (.mrg v₁ v₃)
  | inl {ρ e v : Exp} {B : Typ}
    : Value ρ
    → BStep ρ e v
    → BStep ρ (.inl B e) (.inl B v)
  | inr {ρ e v : Exp} {A : Typ}
    : Value ρ
    → BStep ρ e v
    → BStep ρ (.inr A e) (.inr A v)
  | case_inl {ρ e e₁ e₂ v₁ v : Exp} {B : Typ}
    : Value ρ
    → BStep ρ e (.inl B v₁)
    → BStep (.mrg ρ v₁) e₁ v
    → BStep ρ (.case e e₁ e₂) v
  | case_inr {ρ e e₁ e₂ v₁ v : Exp} {A : Typ}
    : Value ρ
    → BStep ρ e (.inr A v₁)
    → BStep (.mrg ρ v₁) e₂ v
    → BStep ρ (.case e e₁ e₂) v
  | fclos_val {ρ v : Exp} {A B : Typ} {body : Exp}
    : Value ρ
    → Value v
    → BStep ρ (.fclos v A B body) (.fclos v A B body)
  | flam {ρ : Exp} {A B : Typ} {body : Exp}
    : Value ρ
    → BStep ρ (.flam A B body) (.fclos ρ A B body)
  | app_fclos {ρ e₁ e₂ v₁ v₂ v : Exp} {A B : Typ} {body : Exp}
    : Value ρ
    → BStep ρ e₁ (.fclos v₁ A B body)
    → BStep ρ e₂ v₂
    → BStep (.mrg (.mrg v₁ (.fclos v₁ A B body)) v₂) body v
    → BStep ρ (.app e₁ e₂) v
  | fold {ρ e v : Exp} {T : Typ}
    : Value ρ
    → BStep ρ e v
    → BStep ρ (.fold T e) (.fold T v)
  | unfold {ρ e v : Exp} {T : Typ}
    : Value ρ
    → BStep ρ e (.fold T v)
    → BStep ρ (.unfold e) v
  | mlinkn {ρ e₁ e₂ v₁ v₂ pkg v₃ : Exp} {D : Typ} {body : Exp}
    : Value ρ
    → BStep ρ e₁ v₁
    → BStep ρ e₂ (.mclos v₂ D body)
    → SelPkg v₁ D pkg
    → BStep (.mrg v₂ pkg) body v₃
    → BStep ρ (.mlinkn e₁ e₂) (.mrg v₁ v₃)
end S_Sem

open S_Sem

-- Evaluation produces values, and values evaluate only to themselves

theorem source_lookupv_value
    {v v' : SCE.Exp} {n : Nat}
    (hval : SCE.Value v)
    (hlook : S_Sem.LookupV v n v')
    : SCE.Value v' := by
  induction hlook with
  | dmrg_zero => cases hval with | vmrg h1 h2 => exact h2
  | dmrg_succ _ ih => cases hval with | vmrg h1 h2 => exact ih h1
  | nmrg_zero => cases hval
  | nmrg_succ => cases hval

theorem source_sel_value
    {v v' : SCE.Exp} {l : String}
    (hval : SCE.Value v)
    (hsel : S_Sem.Sel v l v')
    : SCE.Value v' := by
  induction hsel with
  | rcd => cases hval with | vlrec h => exact h
  | dmrg_left _ ih => cases hval with | vmrg h1 h2 => exact ih h1
  | dmrg_right _ ih => cases hval with | vmrg h1 h2 => exact ih h2
  | nmrg_left _ ih => cases hval
  | nmrg_right _ ih => cases hval
  | mstruct _ ih => cases hval with | vmstruct h => exact ih h

theorem eval_produces_value
    {ρ e v : SCE.Exp}
    (hval : SCE.Value ρ)
    (heval : S_Sem.BStep ρ e v)
    : SCE.Value v := by
  induction heval with
  | query _ => exact hval
  | lit _ => exact SCE.Value.vint
  | unit _ => exact SCE.Value.vunit
  | clos_val _ hv => exact SCE.Value.vclos hv
  | mclos_val _ hv => exact SCE.Value.vmclos hv
  | proj _ _ hlook ih1 =>
    exact source_lookupv_value (ih1 hval) hlook
  | lam _ => exact SCE.Value.vclos hval
  | box _ _ _ ih1 ih2 => exact ih2 (ih1 hval)
  | app_clos _ _ _ _ ih1 ih2 ih3 =>
    have hvclos := ih1 hval
    cases hvclos with | vclos hv => exact ih3 (SCE.Value.vmrg hv (ih2 hval))
  | app_mclos _ _ _ _ ih1 ih2 ih3 =>
    have hvclos := ih1 hval
    cases hvclos with | vmclos hv => exact ih3 (SCE.Value.vmrg hv (ih2 hval))
  | dmrg _ _ _ ih1 ih2 =>
    exact SCE.Value.vmrg (ih1 hval) (ih2 (SCE.Value.vmrg hval (ih1 hval)))
  | nmrg _ _ _ ih1 ih2 =>
    exact SCE.Value.vmrg (ih1 hval) (ih2 hval)
  | lrec _ _ ih => exact SCE.Value.vlrec (ih hval)
  | rproj _ _ hsel ih =>
    exact source_sel_value (ih hval) hsel
  | letb _ _ _ ih1 ih2 =>
    exact ih2 (SCE.Value.vmrg hval (ih1 hval))
  | openm _ _ _ ih1 ih2 =>
    have := ih1 hval
    cases this with | vlrec hv => exact ih2 (SCE.Value.vmrg hval hv)
  | mstruct _ _ ih => exact SCE.Value.vmstruct (ih hval)
  | mfunctor_sandboxed _ => exact SCE.Value.vmclos SCE.Value.vunit
  | mfunctor_open hv => exact SCE.Value.vmclos hv
  | mlink hv hstep1 hstep2 hsel hstep3 ih1 ih2 ih3 =>
    have hv1 := ih1 hv
    have hv2 := ih2 hv
    cases hv2 with
    | vmclos hvv2 =>
      have hvl := source_sel_value hv1 hsel
      exact SCE.Value.vmrg hv1 (ih3 (SCE.Value.vmrg hvv2 (SCE.Value.vlrec hvl)))
  | mlinkn hv hstep1 hstep2 hsp hstep3 ih1 ih2 ih3 =>
    have hv1 := ih1 hv
    have hv2 := ih2 hv
    cases hv2 with
    | vmclos hvv2 =>
      exact SCE.Value.vmrg hv1 (ih3 (SCE.Value.vmrg hvv2 (S_Sem.selpkg_value hsp hv1)))
  | inl _ _ ih => exact SCE.Value.vinl (ih hval)
  | inr _ _ ih => exact SCE.Value.vinr (ih hval)
  | case_inl _ _ _ ih1 ih2 =>
    have hinl := ih1 hval
    cases hinl with | vinl hv1 => exact ih2 (SCE.Value.vmrg hval hv1)
  | case_inr _ _ _ ih1 ih2 =>
    have hinr := ih1 hval
    cases hinr with | vinr hv1 => exact ih2 (SCE.Value.vmrg hval hv1)
  | fclos_val _ hv => exact SCE.Value.vfclos hv
  | flam _ => exact SCE.Value.vfclos hval
  | app_fclos _ _ _ _ ih1 ih2 ih3 =>
    have hvclos := ih1 hval
    cases hvclos with
    | vfclos hv =>
      exact ih3 (SCE.Value.vmrg (SCE.Value.vmrg hv (SCE.Value.vfclos hv)) (ih2 hval))
  | fold _ _ ih => exact SCE.Value.vfold (ih hval)
  | unfold _ _ ih =>
    have hfold := ih hval
    cases hfold with | vfold hv => exact hv

-- A value big-steps only to itself
theorem bstep_value_id {v : SCE.Exp}
    (hv : SCE.Value v)
    : ∀ {ρ v' : SCE.Exp}, S_Sem.BStep ρ v v' → v' = v := by
  induction hv with
  | vint => intro _ _ h; cases h; rfl
  | vunit => intro _ _ h; cases h; rfl
  | vclos _ => intro _ _ h; cases h; rfl
  | vmclos _ => intro _ _ h; cases h; rfl
  | vmstruct _ ih =>
    intro _ _ h
    cases h with
    | mstruct _ hb => rw [ih hb]
  | vmrg _ _ ih1 ih2 =>
    intro _ _ h
    cases h with
    | dmrg _ hb1 hb2 => rw [ih1 hb1, ih2 hb2]
  | vlrec _ ih =>
    intro _ _ h
    cases h with
    | lrec _ hb => rw [ih hb]
  | vinl _ ih =>
    intro _ _ h
    cases h with
    | inl _ hb => rw [ih hb]
  | vinr _ ih =>
    intro _ _ h
    cases h with
    | inr _ hb => rw [ih hb]
  | vfclos _ => intro _ _ h; cases h; rfl
  | vfold _ ih =>
    intro _ _ h
    cases h with
    | fold _ hb => rw [ih hb]
