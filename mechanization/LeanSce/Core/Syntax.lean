namespace Core

inductive Typ where
  | int  : Typ
  | top  : Typ
  | arr  : Typ → Typ → Typ
  | and  : Typ → Typ → Typ
  | or   : Typ → Typ → Typ
  | rcd  : String → Typ → Typ
  -- iso-recursive types: de Bruijn var 0 is bound by the nearest mu
  | var  : Nat → Typ
  | mu   : Typ → Typ
  deriving Repr

-- substTyp d S T replaces var d by S in T (S is closed, so no shifting)
def substTyp (d : Nat) (S : Typ) : Typ → Typ
  | .int => .int
  | .top => .top
  | .arr A B => .arr (substTyp d S A) (substTyp d S B)
  | .and A B => .and (substTyp d S A) (substTyp d S B)
  | .or A B => .or (substTyp d S A) (substTyp d S B)
  | .rcd l A => .rcd l (substTyp d S A)
  | .var n => if n = d then S else .var n
  | .mu T => .mu (substTyp (d + 1) S T)

inductive Exp where
  | query  : Exp
  | proj   : Exp → Nat → Exp
  | lit    : Nat → Exp
  | unit   : Exp
  | lam    : Typ → Exp → Exp
  | box    : Exp → Exp → Exp
  | clos   : Exp → Typ → Exp → Exp
  | app    : Exp → Exp → Exp
  | mrg    : Exp → Exp → Exp
  | lrec   : String → Exp → Exp
  | rproj  : Exp → String → Exp
  -- unions: inl B e injects into _ ∨ B, inr A e into A ∨ _
  | inl    : Typ → Exp → Exp
  | inr    : Typ → Exp → Exp
  | case   : Exp → Exp → Exp → Exp
  -- fixpoint: flam A B e is a recursive function of type A → B;
  -- its body sees ?.0 = argument, ?.1 = the function itself
  | flam   : Typ → Typ → Exp → Exp
  | fclos  : Exp → Typ → Typ → Exp → Exp
  -- iso-recursive types: fold T e stores the mu-body T, folds into mu T
  | fold   : Typ → Exp → Exp
  | unfold : Exp → Exp
  deriving Repr

inductive Lookup : Typ → Nat → Typ → Prop where
  | zero {A B}
    : Lookup (.and A B) 0 B
  | succ {A B n C}
    : Lookup A n C
    → Lookup (.and A B) (n+1) C

inductive Value : Exp → Prop where
  | vint {n}      : Value (.lit n)
  | vunit         : Value .unit
  | vclos {v A e} : Value v → Value (.clos v A e)
  | vrcd {v l}    : Value v → Value (.lrec l v)
  | vmrg {v1 v2}  : Value v1 → Value v2 → Value (.mrg v1 v2)
  | vinl {v B}    : Value v → Value (.inl B v)
  | vinr {v A}    : Value v → Value (.inr A v)
  | vfclos {v A B e} : Value v → Value (.fclos v A B e)
  | vfold {v T}   : Value v → Value (.fold T v)

inductive Lin : String → Typ → Prop where
  | rcd {l A}
    : Lin l (.rcd l A)
  | andl {l A B}
    : Lin l A
    → Lin l (.and A B)
  | andr {l B A}
    : Lin l B
    → Lin l (.and A B)

inductive RLookup : Typ → String → Typ → Prop where
  | zero {l A}
    : RLookup (.rcd l A) l A
  | landl {A l C B}
    : RLookup A l C
      → ¬Lin l B
      → RLookup (.and A B) l C
  | landr {B l C A}
    : RLookup B l C
      → ¬Lin l A
      → RLookup (.and A B) l C

-- A successful lookup witnesses containment.  This is why `landr` needs only
-- `¬Lin l A`: the `Lin l B` half of the disjointness condition is already
-- implied by its first premise, so stating it would be redundant.  Both
-- constructors now carry exactly one negative premise, matching SCE.SRLookup.
theorem rlookup_lin {A : Typ} {l : String} {C : Typ} : RLookup A l C → Lin l A := by
  intro h
  induction h with
  | zero => exact Lin.rcd
  | landl _ _ ih => exact Lin.andl ih
  | landr _ _ ih => exact Lin.andr ih

inductive LookupV : Exp → Nat → Exp → Prop where
  | lvzero {v₁ v₂ : Exp}
    : LookupV (.mrg v₁ v₂) 0 v₂
  | lvsucc {v₁ v₂ v₃ : Exp} {n : Nat}
    : LookupV v₁ n v₃
    → LookupV (.mrg v₁ v₂) (n + 1) v₃

inductive RLookupV : Exp → String → Exp → Prop where
  | rvlzero {l : String} {e : Exp}
    : RLookupV (.lrec l e) l e
  | vlandl {e₁ e₂ e : Exp} {l : String}
    : RLookupV e₁ l e
    → RLookupV (.mrg e₁ e₂) l e
  | vlandr {e₁ e₂ e : Exp} {l : String}
    : RLookupV e₂ l e
    → RLookupV (.mrg e₁ e₂) l e

end Core
