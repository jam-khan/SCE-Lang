
namespace SCE

inductive Typ where
  | int  : Typ
  | top  : Typ
  | arr  : Typ → Typ → Typ
  -- functor type: a distinct former from `arr`, so a functor cannot be applied
  -- with ordinary application.  `elabTyp` erases it to `arr`.
  | marr : Typ → Typ → Typ
  -- signature type `Sig A`: the interface of a module struct.  A distinct
  -- former from `A` itself, so a struct cannot be consumed as a plain value.
  -- `elabTyp` erases it to its content type.
  | sig  : Typ → Typ
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
  | .marr A B => .marr (substTyp d S A) (substTyp d S B)
  | .sig A => .sig (substTyp d S A)
  | .and A B => .and (substTyp d S A) (substTyp d S B)
  | .or A B => .or (substTyp d S A) (substTyp d S B)
  | .rcd l A => .rcd l (substTyp d S A)
  | .var n => if n = d then S else .var n
  | .mu T => .mu (substTyp (d + 1) S T)

-- Functor modes determine which environment a functor captures.
inductive Sandbox where
  | sandboxed : Sandbox
  | open_ : Sandbox
  deriving Repr

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
  -- to be elaborated
  | mstruct : Exp → Exp
  | mfunctor : Sandbox → Typ → Exp → Exp
  | mclos : Exp → Typ → Exp → Exp
  | mlink : Exp → Exp → Exp
  | mapp : Exp → Exp → Exp
  -- more terms
  | nmrg  : Exp → Exp → Exp
  | letb  : Exp → Exp → Exp
  | openm : Exp → Exp → Exp
  -- n-ary linking: satisfy every labeled import of a functor at once
  | mlinkn : Exp → Exp → Exp
  -- unions: inl B e injects into _ ∨ B, inr A e into A ∨ _
  | inl   : Typ → Exp → Exp
  | inr   : Typ → Exp → Exp
  | case  : Exp → Exp → Exp → Exp
  -- fixpoint: flam A B e is a recursive function of type A → B;
  -- its body sees ?.0 = argument, ?.1 = the function itself
  | flam  : Typ → Typ → Exp → Exp
  | fclos : Exp → Typ → Typ → Exp → Exp
  -- iso-recursive types: fold T e stores the mu-body T, folds into mu T
  | fold   : Typ → Exp → Exp
  | unfold : Exp → Exp
  deriving Repr

inductive Value : Exp → Prop where
  | vint   {n}      : Value (.lit n)
  | vunit           : Value .unit
  | vclos  {v A e}  : Value v → Value (.clos v A e)
  | vmclos {v A e}  : Value v → Value (.mclos v A e)
  -- a fully evaluated struct stays wrapped: it is the value of type `Sig A`
  | vmstruct {v} : Value v → Value (.mstruct v)
  | vmrg   {v₁ v₂}  : Value v₁ → Value v₂ → Value (.mrg v₁ v₂)
  | vlrec  {v l}    : Value v → Value (.lrec l v)
  | vinl   {v B}    : Value v → Value (.inl B v)
  | vinr   {v A}    : Value v → Value (.inr A v)
  | vfclos {v A B e} : Value v → Value (.fclos v A B e)
  | vfold  {v T}    : Value v → Value (.fold T v)

inductive SLookup : Typ → Nat → Typ → Prop
| zero (A B : Typ) : SLookup (Typ.and A B) 0 B
| succ (A B : Typ) (n : Nat) (C : Typ)
    : SLookup A n C → SLookup (Typ.and A B) (Nat.succ n) C

inductive LabelIn : String → Typ → Prop where
  | rcd (label : String) (T : Typ)
    : LabelIn label (Typ.rcd label T)
  | andl (A B : Typ) (label : String)
    : LabelIn label A → LabelIn label (Typ.and A B)
  | andr (A B : Typ) (label : String)
    : LabelIn label B → LabelIn label (Typ.and A B)
  -- a sig-typed component erases to its content, so its labels still count
  -- for disjointness: conflicts must be detected through the signature
  | sig (A : Typ) (label : String)
    : LabelIn label A → LabelIn label (Typ.sig A)

inductive SRLookup : Typ → String → Typ → Prop
| zero (label : String) (T : Typ) :
    SRLookup (Typ.rcd label T) label T
| andl (A B : Typ) (label : String) (T : Typ) :
    SRLookup A label T →
    ¬ LabelIn label B →
    SRLookup (Typ.and A B) label T
| andr (A B : Typ) (label : String) (T : Typ) :
    SRLookup B label T →
    ¬ LabelIn label A →
    SRLookup (Typ.and A B) label T
-- a signature is transparent for lookup: it marks a module but hides nothing
-- (its erasure is the erasure of its content)
| sig (A : Typ) (label : String) (T : Typ) :
    SRLookup A label T →
    SRLookup (Typ.sig A) label T

-- A successful lookup witnesses containment.  This is why the `and` rules above
-- carry only the negative half of their disjointness condition: the positive
-- half follows from the first premise.  Core.RLookup is stated the same way.
theorem srlookup_labelin {A : Typ} {l : String} {T : Typ} : SRLookup A l T → LabelIn l A := by
  intro h
  induction h with
  | zero => exact LabelIn.rcd _ _
  | andl _ _ _ _ _ _ ih => exact LabelIn.andl _ _ _ ih
  | andr _ _ _ _ _ _ ih => exact LabelIn.andr _ _ _ ih
  | sig _ _ _ _ ih => exact LabelIn.sig _ _ ih

-- LinkOk Γ₁ D: the module type Γ₁ satisfies every labeled import of the
-- interface D ::= rcd l A | D & rcd l A (left-nested intersections of records)
inductive LinkOk : Typ → Typ → Prop where
  | one {Γ₁ : Typ} {l : String} {A : Typ}
    : SRLookup Γ₁ l A
    → LinkOk Γ₁ (.rcd l A)
  | more {Γ₁ D : Typ} {l : String} {A : Typ}
    : LinkOk Γ₁ D
    → SRLookup Γ₁ l A
    → LinkOk Γ₁ (.and D (.rcd l A))

end SCE
