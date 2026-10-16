import LeanSce.SCE.Syntax
import LeanSce.Core.Syntax


open SCE

/-- Save the ambient environment and restore it for each operand. -/
def nmrgCore (ce₁ ce₂ : Core.Exp) : Core.Exp :=
  .proj (.mrg .query
    (.mrg (.box (.proj .query 0) ce₁)
      (.box (.proj .query 1) ce₂))) 0

def wire (shift : Nat) : Core.Typ → Core.Exp
  | .rcd l _ => .lrec l (.rproj (.proj .query shift) l)
  | .and D (.rcd l _) =>
    .mrg (wire shift D) (.lrec l (.rproj (.proj .query (shift + 1)) l))
  | _ => .unit

def linkStep (g1 D B : Core.Typ) : Core.Exp :=
  .lam g1 (.lam (.arr D B) (.mrg (.proj .query 1) (.app (.proj .query 1) (wire 0 D))))

def linkedCore (g1 D B : Core.Typ) (ce₁ ce₂ : Core.Exp) : Core.Exp :=
  .app (.app (linkStep g1 D B) ce₁) ce₂

@[simp]
def elabTyp : Typ → Core.Typ
  | Typ.int        => Core.Typ.int
  | Typ.top        => Core.Typ.top
  | Typ.arr t1 t2  => Core.Typ.arr (elabTyp t1) (elabTyp t2)
  -- the functor type erases to an ordinary arrow: modules leave no trace
  -- in target types
  | Typ.marr t1 t2 => Core.Typ.arr (elabTyp t1) (elabTyp t2)
  -- the signature type erases to its content: structs leave no trace either
  | Typ.sig t      => elabTyp t
  | Typ.and t1 t2  => Core.Typ.and (elabTyp t1) (elabTyp t2)
  | Typ.or t1 t2   => Core.Typ.or (elabTyp t1) (elabTyp t2)
  | Typ.rcd str t  => Core.Typ.rcd str (elabTyp t)
  | Typ.var n      => Core.Typ.var n
  | Typ.mu t       => Core.Typ.mu (elabTyp t)

-- elaboration commutes with mu-unfolding substitution
theorem elab_substTyp (d : Nat) (S : Typ)
    : (T : Typ) → elabTyp (substTyp d S T) = Core.substTyp d (elabTyp S) (elabTyp T)
  | .int => rfl
  | .top => rfl
  | .arr A B => by
    simp [substTyp, elabTyp, Core.substTyp, elab_substTyp d S A, elab_substTyp d S B]
  | .marr A B => by
    simp [substTyp, elabTyp, Core.substTyp, elab_substTyp d S A, elab_substTyp d S B]
  | .sig A => by
    simp [substTyp, elabTyp, elab_substTyp d S A]
  | .and A B => by
    simp [substTyp, elabTyp, Core.substTyp, elab_substTyp d S A, elab_substTyp d S B]
  | .or A B => by
    simp [substTyp, elabTyp, Core.substTyp, elab_substTyp d S A, elab_substTyp d S B]
  | .rcd l A => by
    simp [substTyp, elabTyp, Core.substTyp, elab_substTyp d S A]
  | .var n => by
    by_cases h : n = d <;> simp [substTyp, elabTyp, Core.substTyp, h]
  | .mu T => by
    simp [substTyp, elabTyp, Core.substTyp, elab_substTyp (d + 1) S T]

abbrev TyCtx := Typ

inductive elabExp : TyCtx → Exp → Typ → Core.Exp → Prop
  | equery {ctx}
    : elabExp ctx Exp.query ctx Core.Exp.query
  | elit (ctx : Typ) (n : Nat)
    : elabExp ctx (Exp.lit n) Typ.int (Core.Exp.lit n)
  | eunit (ctx : Typ)
    : elabExp ctx Exp.unit Typ.top Core.Exp.unit
  | eapp (ctx A B : Typ) (se1 se2 : Exp) (ce1 ce2 : Core.Exp)
    : elabExp ctx se1 (Typ.arr A B) ce1
    → elabExp ctx se2 A ce2
    → elabExp ctx (Exp.app se1 se2) B (Core.Exp.app ce1 ce2)
  | eproj (ctx A B : Typ) (se : Exp) (ce : Core.Exp) (i : Nat)
    : elabExp ctx se A ce
    → SLookup A i B
    → elabExp ctx (Exp.proj se i) B (Core.Exp.proj ce i)
  | ebox (ctx ctx' A : Typ) (se1 se2 : Exp) (ce1 ce2 : Core.Exp)
    : elabExp ctx se1 ctx' ce1
    → elabExp ctx' se2 A ce2
    → elabExp ctx (Exp.box se1 se2) A (Core.Exp.box ce1 ce2)
  | edmrg (ctx A B : Typ) (se1 se2 : Exp) (ce1 ce2 : Core.Exp)
    : elabExp ctx se1 A ce1
    → elabExp (Typ.and ctx A) se2 B ce2
    → elabExp ctx (Exp.mrg se1 se2) (Typ.and A B) (Core.Exp.mrg ce1 ce2)
  /-
    Γ ⊢ eˢ₁ : A ⤳ eᶜ₁
    Γ ⊢ eˢ₂ : B ⤳ eᶜ₂
    ──────────────────────────────────────────────────────────
    Γ ⊢ eˢ₁ ,, eˢ₂ : A & B ⤳ (?, ((?.0 ▷ eᶜ₁), (?.1 ▷ eᶜ₂))).0
  -/
  | enmrg (ctx A B : Typ) (se1 se2 : Exp) (ce1 ce2 : Core.Exp)
    : elabExp ctx se1 A ce1
    → elabExp ctx se2 B ce2
    → elabExp ctx (Exp.nmrg se1 se2) (Typ.and A B)
        (nmrgCore ce1 ce2)
  | elam (ctx A B : Typ) (se : Exp) (ce : Core.Exp)
    : elabExp (Typ.and ctx A) se B ce
    → elabExp ctx (Exp.lam A se) (Typ.arr A B) (Core.Exp.lam (elabTyp A) ce)
  | erproj (ctx A B : Typ) (se : Exp) (ce : Core.Exp) (l : String) :
      elabExp ctx se B ce
      → SRLookup B l A
      → elabExp ctx (Exp.rproj se l) A (Core.Exp.rproj ce l)
  | eclos (ctx ctx' A B : Typ) (se1 se2 : Exp) (ce1 ce2 : Core.Exp)
    : SCE.Value se1
    → elabExp Typ.top se1 ctx' ce1
    → elabExp (Typ.and ctx' A) se2 B ce2
    → elabExp ctx (Exp.clos se1 A se2) (Typ.arr A B) (Core.Exp.clos ce1 (elabTyp A) ce2)
  | elrec (ctx A : Typ) (se : Exp) (ce : Core.Exp) (l : String)
    : elabExp ctx se A ce
    → elabExp ctx (Exp.lrec l se) (Typ.rcd l A) (Core.Exp.lrec l ce)
  | letb (ctx A B : Typ) (se1 se2 : Exp) (ce1 ce2 : Core.Exp)
    : elabExp ctx se1 A ce1
    → elabExp (Typ.and ctx A) se2 B ce2
    → elabExp ctx (Exp.letb se1 se2) B
        (Core.Exp.proj (Core.Exp.mrg ce1 ce2) 0)
  | openm (ctx A B : Typ) (se1 se2 : Exp) (ce1 ce2 : Core.Exp) (l : String)
    : elabExp ctx se1 (Typ.rcd l A) ce1
    → elabExp (Typ.and ctx A) se2 B ce2
    → elabExp ctx (Exp.openm se1 se2) B
        (Core.Exp.app (Core.Exp.lam (elabTyp A) ce2) (Core.Exp.rproj ce1 l))
  -- Structures use the ambient environment; their wrapper erases uniformly.
  | mstruct (ctx B : Typ) (se : Exp) (ce : Core.Exp)
    : elabExp ctx se B ce
    → elabExp ctx (Exp.mstruct se) (Typ.sig B) ce
  | mfunctor (ctx ctxInner A B : Typ) (sb : Sandbox) (se : Exp) (ce : Core.Exp)
    : (sb = Sandbox.sandboxed → ctxInner = Typ.and Typ.top A)
    → (sb = Sandbox.open_     → ctxInner = Typ.and ctx A)
    → elabExp ctxInner se B ce
    → elabExp ctx (Exp.mfunctor sb A se) (Typ.marr A B)
        (match sb with
          | Sandbox.sandboxed => Core.Exp.box Core.Exp.unit (Core.Exp.lam (elabTyp A) ce)
          | Sandbox.open_     => Core.Exp.lam (elabTyp A) ce)
  | mclos (ctx ctx' A B : Typ) (se1 se2 : Exp) (ce1 ce2 : Core.Exp)
    : SCE.Value se1
    → elabExp Typ.top se1 ctx' ce1
    → elabExp (Typ.and ctx' A) se2 B ce2
    → elabExp ctx (Exp.mclos se1 A se2) (Typ.marr A B)
        (Core.Exp.clos ce1 (elabTyp A) ce2)
  | mapp (ctx A B : Typ) (se1 se2 : Exp) (ce1 ce2 : Core.Exp)
    : elabExp ctx se1 (Typ.marr A B) ce1
    → elabExp ctx se2 A ce2
    → elabExp ctx (Exp.mapp se1 se2) B (Core.Exp.app ce1 ce2)
  | mlink (ctx Γ₁ A B : Typ) (l : String)
      (se1 se2 : Exp) (ce1 ce2 : Core.Exp)
    : elabExp ctx se1 Γ₁ ce1
    → elabExp ctx se2 (Typ.marr (Typ.rcd l A) B) ce2
    → SRLookup Γ₁ l A
    → elabExp ctx (Exp.mlink se1 se2) (Typ.and Γ₁ B)
        (linkedCore (elabTyp Γ₁) (elabTyp (Typ.rcd l A)) (elabTyp B) ce1 ce2)
  | mlinkn (ctx Γ₁ D B : Typ)
      (se1 se2 : Exp) (ce1 ce2 : Core.Exp)
    : elabExp ctx se1 Γ₁ ce1
    → elabExp ctx se2 (Typ.marr D B) ce2
    → LinkOk Γ₁ D
    → elabExp ctx (Exp.mlinkn se1 se2) (Typ.and Γ₁ B)
        (linkedCore (elabTyp Γ₁) (elabTyp D) (elabTyp B) ce1 ce2)
  | einl (ctx A B : Typ) (se : Exp) (ce : Core.Exp)
    : elabExp ctx se A ce
    → elabExp ctx (Exp.inl B se) (Typ.or A B) (Core.Exp.inl (elabTyp B) ce)
  | einr (ctx A B : Typ) (se : Exp) (ce : Core.Exp)
    : elabExp ctx se B ce
    → elabExp ctx (Exp.inr A se) (Typ.or A B) (Core.Exp.inr (elabTyp A) ce)
  | ecase (ctx A B C : Typ) (se se1 se2 : Exp) (ce ce1 ce2 : Core.Exp)
    : elabExp ctx se (Typ.or A B) ce
    → elabExp (Typ.and ctx A) se1 C ce1
    → elabExp (Typ.and ctx B) se2 C ce2
    → elabExp ctx (Exp.case se se1 se2) C (Core.Exp.case ce ce1 ce2)
  | eflam (ctx A B : Typ) (se : Exp) (ce : Core.Exp)
    : elabExp (Typ.and (Typ.and ctx (Typ.arr A B)) A) se B ce
    → elabExp ctx (Exp.flam A B se) (Typ.arr A B)
        (Core.Exp.flam (elabTyp A) (elabTyp B) ce)
  | efclos (ctx ctx' A B : Typ) (se1 se2 : Exp) (ce1 ce2 : Core.Exp)
    : SCE.Value se1
    → elabExp Typ.top se1 ctx' ce1
    → elabExp (Typ.and (Typ.and ctx' (Typ.arr A B)) A) se2 B ce2
    → elabExp ctx (Exp.fclos se1 A B se2) (Typ.arr A B)
        (Core.Exp.fclos ce1 (elabTyp A) (elabTyp B) ce2)
  | efold (ctx T : Typ) (se : Exp) (ce : Core.Exp)
    : elabExp ctx se (substTyp 0 (Typ.mu T) T) ce
    → elabExp ctx (Exp.fold T se) (Typ.mu T) (Core.Exp.fold (elabTyp T) ce)
  -- result type is a variable guarded by an equation so that dependent
  -- elimination (cases at a concrete type) does not get stuck on substTyp
  | eunfold (ctx T A : Typ) (se : Exp) (ce : Core.Exp)
    : elabExp ctx se (Typ.mu T) ce
    → A = substTyp 0 (Typ.mu T) T
    → elabExp ctx (Exp.unfold se) A (Core.Exp.unfold ce)

/-- A sandboxed functor elaborates identically in any ambient context. -/
theorem sandboxed_functor_elab_context_independent
    {Γ₁ Γ₂ A T : Typ} {body : Exp} {c : Core.Exp}
    (h : elabExp Γ₁ (.mfunctor .sandboxed A body) T c) :
    elabExp Γ₂ (.mfunctor .sandboxed A body) T c := by
  cases h with
  | mfunctor _ ctxInner _ B _ _ ce hSandbox _ hBody =>
    exact elabExp.mfunctor Γ₂ ctxInner A B .sandboxed body ce
      hSandbox (by intro h; cases h) hBody

/-- Source typing is elaboration with the generated core term hidden. -/
abbrev SCE.HasType (Γ : SCE.Typ) (e : SCE.Exp) (A : SCE.Typ) : Prop :=
  ∃ ce, elabExp Γ e A ce
