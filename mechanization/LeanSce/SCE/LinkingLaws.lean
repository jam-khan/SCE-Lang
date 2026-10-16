/-
  Linking laws not covered by the existing development.

  A. Interface abstraction -- a client cannot observe anything about the
     provider beyond the package it extracts through its import interface.
     This is the semantic half of "compiled against interfaces alone";
     `core_link_typed` gives only the typing half.
-/
import LeanSce.SCE.Semantics.BigStep
import LeanSce.SCE.Semantics.Determinism
import LeanSce.SCE.Preservation
import LeanSce.SCE.Semantics.Equivalence

open SCE

namespace S_Sem

/-- **Interface abstraction (n-ary).**  If two providers agree on every package
extractable at any import interface, then either may drive the same client to
the same exports.  The client's body derivation never mentions the provider, so
the whole proof is: invert, swap the provider, reapply. -/
theorem link_respects_interface
    {ρ P₁ P₂ C v₁ v₁' w : Exp}
    (hlink : BStep ρ (.mlinkn P₁ C) (.mrg v₁ w))
    (hP₂   : BStep ρ P₂ v₁')
    (hagree : ∀ (D : Typ) (pkg : Exp), SelPkg v₁ D pkg → SelPkg v₁' D pkg)
    : BStep ρ (.mlinkn P₂ C) (.mrg v₁' w) := by
  cases hlink with
  | mlinkn hρ _hP₁ hC hpkg hbody =>
      exact BStep.mlinkn hρ hP₂ hC (hagree _ _ hpkg) hbody

/-- Binary instance, for `link`. -/
theorem link_respects_interface_bin
    {ρ P₁ P₂ C v₁ v₁' w : Exp}
    (hlink : BStep ρ (.mlink P₁ C) (.mrg v₁ w))
    (hP₂   : BStep ρ P₂ v₁')
    (hagree : ∀ (l : String) (vl : Exp), Sel v₁ l vl → Sel v₁' l vl)
    : BStep ρ (.mlink P₂ C) (.mrg v₁' w) := by
  cases hlink with
  | mlink hρ _hP₁ hC hsel hbody =>
      exact BStep.mlink hρ hP₂ hC (hagree _ _ hsel) hbody

/-- Equality form: two interface-agreeing providers drive the client to the
*same* exports.  Needs the general determinism, indexed by an elaboration
witness. -/
theorem link_interface_determined
    {Γ A : Typ} {ρ P₁ P₂ C v₁ v₁' w w' : Exp} {ec ρc : Core.Exp}
    (helab : elabExp Γ (.mlinkn P₂ C) A ec)
    (henv  : elabExp Typ.top ρ Γ ρc)
    (hρ    : Value ρ)
    (h₁ : BStep ρ (.mlinkn P₁ C) (.mrg v₁ w))
    (hP₂ : BStep ρ P₂ v₁')
    (hagree : ∀ (D : Typ) (pkg : Exp), SelPkg v₁ D pkg → SelPkg v₁' D pkg)
    (h₂ : BStep ρ (.mlinkn P₂ C) (.mrg v₁' w'))
    : w = w' := by
  have h₁' := link_respects_interface h₁ hP₂ hagree
  have heq := bigstep_deterministic_gen helab henv hρ h₁' h₂
  simpa using heq

/-- **Interface abstraction, import-label form.**  Two providers that agree on
the client's import label (the only label the link selects) drive the client
to the same exports.  The providers need not agree on any other label.  The
paper's statement, over typed provider values, is `interface_abstraction`. -/
theorem link_respects_import
    {ρ P₁ P₂ C v₁ v₁' w : Exp}
    (hlink : BStep ρ (.mlink P₁ C) (.mrg v₁ w))
    (hP₂   : BStep ρ P₂ v₁')
    (hagree : ∀ (v₂ : Exp) (l : String) (A : Typ) (body vl : Exp),
        BStep ρ C (.mclos v₂ (.rcd l A) body) → Sel v₁ l vl → Sel v₁' l vl)
    : BStep ρ (.mlink P₂ C) (.mrg v₁' w) := by
  cases hlink with
  | mlink hρ _hP₁ hC hsel hbody =>
      exact BStep.mlink hρ hP₂ hC (hagree _ _ _ _ _ hC hsel) hbody

/-- Equality form of `link_respects_import`, for a well-typed link. -/
theorem link_import_determined
    {Γ A : Typ} {ρ P₁ P₂ C v₁ v₁' w w' : Exp} {ec ρc : Core.Exp}
    (helab : elabExp Γ (.mlink P₂ C) A ec)
    (henv  : elabExp Typ.top ρ Γ ρc)
    (hρ    : Value ρ)
    (h₁ : BStep ρ (.mlink P₁ C) (.mrg v₁ w))
    (hP₂ : BStep ρ P₂ v₁')
    (hagree : ∀ (v₂ : Exp) (l : String) (A : Typ) (body vl : Exp),
        BStep ρ C (.mclos v₂ (.rcd l A) body) → Sel v₁ l vl → Sel v₁' l vl)
    (h₂ : BStep ρ (.mlink P₂ C) (.mrg v₁' w'))
    : w = w' := by
  have h₁' := link_respects_import h₁ hP₂ hagree
  have heq := bigstep_deterministic_gen helab henv hρ h₁' h₂
  simpa using heq

/-- **Law C prerequisite.**  Selection is unaffected by a merge extension whose
labels it avoids.  Without disjointness `Sel` genuinely relates both sides. -/
theorem sel_merge_disjoint
    {v₁ v₂ w : Exp} {B : Typ} {l : String} {ce₂ : Core.Exp}
    (hv₂ : Value v₂)
    (helab₂ : elabExp Typ.top v₂ B ce₂)
    (hnotin : ¬ LabelIn l B)
    : Sel (.mrg v₁ v₂) l w ↔ Sel v₁ l w := by
  constructor
  · intro h
    cases h with
    | dmrg_left h'  => exact h'
    | dmrg_right h' => exact (elab_notin_sel_false h' hv₂ hnotin helab₂).elim
  · exact Sel.dmrg_left

/-- One direction of `interface_abstraction`.  The client's closure imports
exactly `l` (by semantic preservation), and selection of `l` from the first
provider is unique, so the second provider supplies the same import. -/
private theorem interface_abstraction_dir
    {Γ A B P₁ : Typ} {l : String} {ρ e p₁ p₂ vl w : Exp}
    {ec ρc pc₁ : Core.Exp}
    (he : elabExp Γ e (.marr (.rcd l A) B) ec)
    (hρ : elabExp Typ.top ρ Γ ρc) (hρv : Value ρ)
    (hp₁v : Value p₁) (hp₂v : Value p₂)
    (hp₁ : elabExp Typ.top p₁ P₁ pc₁)
    (hl₁ : SRLookup P₁ l A)
    (hs₁ : Sel p₁ l vl) (hs₂ : Sel p₂ l vl)
    (h : BStep ρ (.mlink p₁ e) (.mrg p₁ w))
    : BStep ρ (.mlink p₂ e) (.mrg p₂ w) := by
  refine link_respects_import h (sbig_value_refl hp₂v hρv) ?_
  intro v₂ l' A' body vl' hC hsel
  obtain ⟨_, _, hclos⟩ := semantic_preservation he hC hρ hρv
  cases hclos
  have heq := sel_deterministic hp₁v hp₁ hl₁ hs₁ hsel
  subst heq
  exact hs₂

/-- **Interface abstraction** (the paper's Theorem `thm:interface-abstraction`).
Two well-typed provider values that select the same value at the client's
import label `l` drive the client to the same exports. -/
theorem interface_abstraction
    {Γ A B P₁ P₂ : Typ} {l : String} {ρ e p₁ p₂ vl w : Exp}
    {ec ρc pc₁ pc₂ : Core.Exp}
    (he : elabExp Γ e (.marr (.rcd l A) B) ec)
    (hρ : elabExp Typ.top ρ Γ ρc) (hρv : Value ρ)
    (hp₁v : Value p₁) (hp₂v : Value p₂)
    (hp₁ : elabExp Typ.top p₁ P₁ pc₁) (hp₂ : elabExp Typ.top p₂ P₂ pc₂)
    (hl₁ : SRLookup P₁ l A) (hl₂ : SRLookup P₂ l A)
    (hs₁ : Sel p₁ l vl) (hs₂ : Sel p₂ l vl)
    : BStep ρ (.mlink p₁ e) (.mrg p₁ w) ↔ BStep ρ (.mlink p₂ e) (.mrg p₂ w) :=
  ⟨interface_abstraction_dir he hρ hρv hp₁v hp₂v hp₁ hl₁ hs₁ hs₂,
   interface_abstraction_dir he hρ hρv hp₂v hp₁v hp₂ hl₂ hs₂ hs₁⟩

end S_Sem
