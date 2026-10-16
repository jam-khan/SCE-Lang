import LeanSce.Core.Syntax

open Core

inductive HasType : Typ → Exp → Typ → Prop where
  | tquery {Γ : Typ}
    : HasType Γ .query Γ
  | tint {Γ : Typ} {i : Nat}
    : HasType Γ (.lit i) .int
  | tunit {Γ : Typ}
    : HasType Γ .unit .top
  | tapp {Γ A B : Typ} {e₁ e₂ : Exp}
    : HasType Γ e₁ (.arr A B)
    → HasType Γ e₂ A
    → HasType Γ (.app e₁ e₂) B
  | tbox {Γ Γ₁ A : Typ} {e₁ e₂ : Exp}
    : HasType Γ e₁ Γ₁
    → HasType Γ₁ e₂ A
    → HasType Γ (.box e₁ e₂) A
  | tmrg {Γ A B : Typ} {e₁ e₂ : Exp}
    : HasType Γ e₁ A
    → HasType (.and Γ A) e₂ B
    → HasType Γ (.mrg e₁ e₂) (.and A B)
  | tlam {Γ A B : Typ} {e : Exp}
    : HasType (.and Γ A) e B
    → HasType Γ (.lam A e) (.arr A B)
  | tproj {Γ A B : Typ} {e : Exp} {n : Nat}
    : HasType Γ e A
    → Lookup A n B
    → HasType Γ (.proj e n) B
  | tclos {Γ Γ₁ A B : Typ} {v e : Exp}
    : Value v
    → HasType .top v Γ₁
    → HasType (.and Γ₁ A) e B
    → HasType Γ (.clos v A e) (.arr A B)
  | trcd {Γ A : Typ} {l : String} {e : Exp}
    : HasType Γ e A
    → HasType Γ (.lrec l e) (.rcd l A)
  | trproj {Γ A B : Typ} {l : String} {e : Exp}
    : HasType Γ e B
    → RLookup B l A
    → HasType Γ (.rproj e l) A
  | tinl {Γ A B : Typ} {e : Exp}
    : HasType Γ e A
    → HasType Γ (.inl B e) (.or A B)
  | tinr {Γ A B : Typ} {e : Exp}
    : HasType Γ e B
    → HasType Γ (.inr A e) (.or A B)
  | tcase {Γ A B C : Typ} {e e₁ e₂ : Exp}
    : HasType Γ e (.or A B)
    → HasType (.and Γ A) e₁ C
    → HasType (.and Γ B) e₂ C
    → HasType Γ (.case e e₁ e₂) C
  | tflam {Γ A B : Typ} {e : Exp}
    : HasType (.and (.and Γ (.arr A B)) A) e B
    → HasType Γ (.flam A B e) (.arr A B)
  | tfclos {Γ Γ₁ A B : Typ} {v e : Exp}
    : Value v
    → HasType .top v Γ₁
    → HasType (.and (.and Γ₁ (.arr A B)) A) e B
    → HasType Γ (.fclos v A B e) (.arr A B)
  | tfold {Γ T : Typ} {e : Exp}
    : HasType Γ e (substTyp 0 (.mu T) T)
    → HasType Γ (.fold T e) (.mu T)
  -- conclusion type is a variable guarded by an equation so that dependent
  -- elimination (cases at a concrete type) does not get stuck on substTyp
  | tunfold {Γ T A : Typ} {e : Exp}
    : HasType Γ e (.mu T)
    → A = substTyp 0 (.mu T) T
    → HasType Γ (.unfold e) A
