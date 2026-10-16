import LeanSce.Core.Syntax
import LeanSce.Core.Typing.Typing
import LeanSce.Core.Semantics.BigStep
import LeanSce.SCE.Syntax
import LeanSce.SCE.Semantics.BigStep
import LeanSce.SCE.Elaboration.Elaboration
import LeanSce.SCE.Elaboration.Preservation
import LeanSce.SCE.SemanticsPreservation

/-!
Separate compilation: the linker's step on compiled units (`CoreLink`,
`CoreLinkN`) is well-typed and evaluates in lock-step with source-level
`link` / `linkall`.
-/

open SCE Core

-- Linking and separate compilation

/-- The linker's binary step, as a relation on compiled units: given a provider
`ec₁ : A₁` and a functor `ec₂ : {l:A} → B` with `A₁ ∋ l : A`, the linked unit is
`linkedCore A₁ {l:A} B ec₁ ec₂`.  The linearized step is closed — it does not
mention the ambient context — so the relation carries none. -/
inductive CoreLink
    : String → Core.Typ → Core.Typ → Core.Typ
    → Core.Exp → Core.Exp → Core.Exp → Prop where
  | link (A₁ A B : Core.Typ) (l : String) (ec₁ ec₂ : Core.Exp)
    : Core.RLookup A₁ l A
    → CoreLink l A₁ A B ec₁ ec₂ (linkedCore A₁ (.rcd l A) B ec₁ ec₂)

def linkSCE (e₁ e₂ : SCE.Exp) : SCE.Exp :=
  .mlink e₁ e₂

/-- The linker's binary step produces a well-typed unit at `A₁ & B`. -/
theorem core_link_typed
    {Γ A₁ A B : Core.Typ} {l : String} {ec₁ ec₂ ec : Core.Exp}
    (hlink : CoreLink l A₁ A B ec₁ ec₂ ec)
    (h₁ : HasType Γ ec₁ A₁)
    (h₂ : HasType Γ ec₂ (.arr (.rcd l A) B))
    : HasType Γ ec (.and A₁ B) := by
  cases hlink with
  | link _ _ _ _ _ _ hrlookup =>
    exact linkedCore_typed h₁ h₂ (wire_typed_rcd hrlookup)

/-- **Separate compilation (binary `link`).**  Elaborate the provider and the
functor separately, compose the compiled pieces with the linker's step, and the
result evaluates in lock-step with source-level `link`. -/
theorem separate_compilation
    {Γ Γ₁ A B : SCE.Typ} {l : String}
    {es₁ es₂ : SCE.Exp} {ec₁ ec₂ ec : Core.Exp}
    {ρs vs : SCE.Exp} {ρc : Core.Exp}
    (helab₁ : elabExp Γ es₁ Γ₁ ec₁)
    (helab₂ : elabExp Γ es₂ (.marr (.rcd l A) B) ec₂)
    (hlookup : SRLookup Γ₁ l A)
    (hlink : CoreLink l (elabTyp Γ₁) (elabTyp A) (elabTyp B) ec₁ ec₂ ec)
    (heval : S_Sem.BStep ρs (.mlink es₁ es₂) vs)
    (henv : elabExp SCE.Typ.top ρs Γ ρc)
    (henv_val : SCE.Value ρs)
    : ∃ vc, EBig ρc ec vc
           ∧ elabExp SCE.Typ.top vs (.and Γ₁ B) vc := by
  cases hlink with
  | link _ _ _ _ _ _ _ =>
    have hmlink := elabExp.mlink Γ Γ₁ A B l es₁ es₂ ec₁ ec₂ helab₁ helab₂ hlookup
    exact semantic_preservation hmlink heval henv henv_val

/-- Separate compilation reuses a sandboxed client elaborated under the empty
context with a compatible provider in any ambient context. -/
theorem separate_compilation_sandboxed
    {Γ Γ₁ A B : SCE.Typ} {l : String}
    {es₁ body : SCE.Exp} {ec₁ ec₂ ec : Core.Exp}
    {ρs vs : SCE.Exp} {ρc : Core.Exp}
    (helab₁ : elabExp Γ es₁ Γ₁ ec₁)
    (helab₂ : elabExp SCE.Typ.top (.mfunctor .sandboxed (.rcd l A) body)
      (.marr (.rcd l A) B) ec₂)
    (hlookup : SRLookup Γ₁ l A)
    (hlink : CoreLink l (elabTyp Γ₁) (elabTyp A) (elabTyp B) ec₁ ec₂ ec)
    (heval : S_Sem.BStep ρs
      (.mlink es₁ (.mfunctor .sandboxed (.rcd l A) body)) vs)
    (henv : elabExp SCE.Typ.top ρs Γ ρc)
    (henv_val : SCE.Value ρs)
    : ∃ vc, EBig ρc ec vc
           ∧ elabExp SCE.Typ.top vs (.and Γ₁ B) vc := by
  exact separate_compilation helab₁
    (sandboxed_functor_elab_context_independent helab₂)
    hlookup hlink heval henv henv_val

/-- **Separate compilation, closed** — the toolchain's actual case: closed
compiled units, empty initial environment. -/
theorem separate_compilation_closed
    {Γ₁ A B : SCE.Typ} {l : String}
    {es₁ es₂ : SCE.Exp} {ec₁ ec₂ : Core.Exp}
    {vs : SCE.Exp}
    (helab₁ : elabExp SCE.Typ.top es₁ Γ₁ ec₁)
    (helab₂ : elabExp SCE.Typ.top es₂ (.marr (.rcd l A) B) ec₂)
    (hlookup : SRLookup Γ₁ l A)
    (heval : S_Sem.BStep .unit (.mlink es₁ es₂) vs)
    : ∃ vc, EBig .unit (linkedCore (elabTyp Γ₁) (elabTyp (SCE.Typ.rcd l A)) (elabTyp B) ec₁ ec₂) vc
           ∧ elabExp SCE.Typ.top vs (.and Γ₁ B) vc := by
  have hlink : CoreLink l (elabTyp Γ₁) (elabTyp A) (elabTyp B) ec₁ ec₂
      (linkedCore (elabTyp Γ₁) (elabTyp (SCE.Typ.rcd l A)) (elabTyp B) ec₁ ec₂) :=
    CoreLink.link _ _ _ _ _ _ (type_safe_record_lookup hlookup)
  exact separate_compilation helab₁ helab₂ hlookup hlink heval (elabExp.eunit .top) SCE.Value.vunit

-- N-ary linking and separate compilation

/-- The linker's n-ary step: the provider is wired to every import of the
elaborated interface `⟦D⟧` by projection from its single binding. -/
inductive CoreLinkN
    : SCE.Typ → Core.Typ → Core.Typ → Core.Exp → Core.Exp → Core.Exp → Prop where
  | link (D : SCE.Typ) (A₁ B : Core.Typ) (ec₁ ec₂ : Core.Exp)
    : CoreLinkN D A₁ B ec₁ ec₂ (linkedCore A₁ (elabTyp D) B ec₁ ec₂)

theorem core_linkn_typed
    {Γ₁ D : SCE.Typ} {Γc B : Core.Typ} {ec₁ ec₂ ec : Core.Exp}
    (hlink : CoreLinkN D (elabTyp Γ₁) B ec₁ ec₂ ec)
    (hok : LinkOk Γ₁ D)
    (h₁ : HasType Γc ec₁ (elabTyp Γ₁))
    (h₂ : HasType Γc ec₂ (.arr (elabTyp D) B))
    : HasType Γc ec (.and (elabTyp Γ₁) B) := by
  cases hlink with
  | link => exact linkedCore_typed h₁ h₂ (wire_typed hok)

/-- **Separate compilation (n-ary `linkall`).**  As above, with a whole import
interface `D` wired by projection from the once-bound provider. -/
theorem separate_compilation_n
    {Γ Γ₁ D B : SCE.Typ}
    {es₁ es₂ : SCE.Exp} {ec₁ ec₂ ec : Core.Exp}
    {ρs vs : SCE.Exp} {ρc : Core.Exp}
    (helab₁ : elabExp Γ es₁ Γ₁ ec₁)
    (helab₂ : elabExp Γ es₂ (.marr D B) ec₂)
    (hok : LinkOk Γ₁ D)
    (hlink : CoreLinkN D (elabTyp Γ₁) (elabTyp B) ec₁ ec₂ ec)
    (heval : S_Sem.BStep ρs (.mlinkn es₁ es₂) vs)
    (henv : elabExp SCE.Typ.top ρs Γ ρc)
    (henv_val : SCE.Value ρs)
    : ∃ vc, EBig ρc ec vc ∧ elabExp SCE.Typ.top vs (.and Γ₁ B) vc := by
  cases hlink with
  | link =>
    have hn := elabExp.mlinkn Γ Γ₁ D B es₁ es₂ ec₁ ec₂ helab₁ helab₂ hok
    exact semantic_preservation hn heval henv henv_val

/-- Multi-import separate compilation reuses a sandboxed client elaborated
under the empty context with a compatible provider in any ambient context. -/
theorem separate_compilation_n_sandboxed
    {Γ Γ₁ D B : SCE.Typ}
    {es₁ body : SCE.Exp} {ec₁ ec₂ ec : Core.Exp}
    {ρs vs : SCE.Exp} {ρc : Core.Exp}
    (helab₁ : elabExp Γ es₁ Γ₁ ec₁)
    (helab₂ : elabExp SCE.Typ.top (.mfunctor .sandboxed D body) (.marr D B) ec₂)
    (hok : LinkOk Γ₁ D)
    (hlink : CoreLinkN D (elabTyp Γ₁) (elabTyp B) ec₁ ec₂ ec)
    (heval : S_Sem.BStep ρs (.mlinkn es₁ (.mfunctor .sandboxed D body)) vs)
    (henv : elabExp SCE.Typ.top ρs Γ ρc)
    (henv_val : SCE.Value ρs)
    : ∃ vc, EBig ρc ec vc ∧ elabExp SCE.Typ.top vs (.and Γ₁ B) vc := by
  exact separate_compilation_n helab₁
    (sandboxed_functor_elab_context_independent helab₂)
    hok hlink heval henv henv_val

/-- **Separate compilation, n-ary, closed.** -/
theorem separate_compilation_n_closed
    {Γ₁ D B : SCE.Typ}
    {es₁ es₂ : SCE.Exp} {ec₁ ec₂ : Core.Exp}
    {vs : SCE.Exp}
    (helab₁ : elabExp SCE.Typ.top es₁ Γ₁ ec₁)
    (helab₂ : elabExp SCE.Typ.top es₂ (.marr D B) ec₂)
    (hok : LinkOk Γ₁ D)
    (heval : S_Sem.BStep .unit (.mlinkn es₁ es₂) vs)
    : ∃ vc, EBig .unit (linkedCore (elabTyp Γ₁) (elabTyp D) (elabTyp B) ec₁ ec₂) vc
           ∧ elabExp SCE.Typ.top vs (.and Γ₁ B) vc := by
  have hlink : CoreLinkN D (elabTyp Γ₁) (elabTyp B) ec₁ ec₂
      (linkedCore (elabTyp Γ₁) (elabTyp D) (elabTyp B) ec₁ ec₂) :=
    CoreLinkN.link _ _ _ _ _
  exact separate_compilation_n helab₁ helab₂ hok hlink heval (elabExp.eunit .top) SCE.Value.vunit
