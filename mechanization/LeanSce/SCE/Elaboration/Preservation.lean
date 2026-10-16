import LeanSce.Core.Syntax
import LeanSce.Core.Typing.Typing
import LeanSce.SCE.Syntax
import LeanSce.SCE.Elaboration.Elaboration

/-!
Type preservation of elaboration: source lookups erase to Core lookups under
`elabTyp`, the emitted composition terms are well-typed, and every elaborated
term is a well-typed Core term.
-/

open SCE Core

theorem type_safe_index_lookup
    {ST₁ ST₂ : SCE.Typ} {n : Nat}
    (h : SLookup ST₁ n ST₂)
    : Core.Lookup (elabTyp ST₁) n (elabTyp ST₂) := by
  induction h with
  | zero A B => exact Core.Lookup.zero
  | succ A B n C _ ih => exact Core.Lookup.succ ih

theorem type_safe_label_existence
    {l : String} {ST : SCE.Typ}
    : SCE.LabelIn l ST ↔ Core.Lin l (elabTyp ST) := by
  constructor
  · intro h
    induction h with
    | rcd l T =>
      simp [elabTyp]
      exact Core.Lin.rcd
    | andl A B l _ ih =>
      simp [elabTyp]
      exact Core.Lin.andl ih
    | andr A B l _ ih =>
      simp [elabTyp]
      exact Core.Lin.andr ih
    | sig A l _ ih =>
      simpa [elabTyp] using ih
  · intro h
    cases ST with
    | rcd lA T =>
      simp [elabTyp] at h
      cases h
      exact SCE.LabelIn.rcd l T
    | and A B =>
      simp [elabTyp] at h
      cases h with
      | andl h =>
        exact SCE.LabelIn.andl A B l (type_safe_label_existence.mpr h)
      | andr h =>
        exact SCE.LabelIn.andr A B l (type_safe_label_existence.mpr h)
    | int => simp [elabTyp] at h; cases h
    | top => simp [elabTyp] at h; cases h
    | arr _ _ => simp [elabTyp] at h; cases h
    | marr _ _ => simp [elabTyp] at h; cases h
    | sig A =>
      simp [elabTyp] at h
      exact SCE.LabelIn.sig A l (type_safe_label_existence.mpr h)
    | or _ _ => simp [elabTyp] at h; cases h
    | var _ => simp [elabTyp] at h; cases h
    | mu _ => simp [elabTyp] at h; cases h


theorem type_safe_label_nonexistence
    {l : String} {ST : SCE.Typ}
    : ¬ SCE.LabelIn l ST ↔ ¬ Core.Lin l (elabTyp ST) := by
  constructor
  · intro hns hc; exact hns (type_safe_label_existence.mpr hc)
  · intro hnc hs; exact hnc (type_safe_label_existence.mp hs)

theorem type_safe_record_lookup
    {ST₁ ST₂ : SCE.Typ} {l : String}
    (h : SCE.SRLookup ST₁ l ST₂)
    : Core.RLookup (elabTyp ST₁) l (elabTyp ST₂) := by
  induction h with
  | zero l T =>
    simp [elabTyp]
    exact Core.RLookup.zero
  | andl A B l T _ h_cond ih =>
    simp [elabTyp]
    exact Core.RLookup.landl ih
      (type_safe_label_nonexistence.mp h_cond)
  | andr A B l T _ h_cond ih =>
    simp [elabTyp]
    exact Core.RLookup.landr ih
      (type_safe_label_nonexistence.mp h_cond)
  | sig A l T _ ih =>
    simpa [elabTyp] using ih

theorem elab_value
    {Γ A : SCE.Typ} {v : SCE.Exp} {cv : Core.Exp}
    (helab : elabExp Γ v A cv)
    (hval : SCE.Value v)
    : Core.Value cv := by
  induction hval generalizing Γ A cv with
  | vint =>
    cases helab
    exact Core.Value.vint
  | vunit =>
    cases helab
    exact Core.Value.vunit
  | vclos hv ih =>
    cases helab with
    | eclos _ _ _ _ _ _ ce1 ce2 _ h1 h2 =>
      exact Core.Value.vclos (ih h1)
  | vmclos hv ih =>
    cases helab with
    | mclos _ _ _ _ _ _ ce1 ce2 _ h1 h2 =>
      exact Core.Value.vclos (ih h1)
  | vmrg hv1 hv2 ih1 ih2 =>
    cases helab with
    | edmrg _ _ _ _ _ ce1 ce2 h1 h2 =>
      exact Core.Value.vmrg (ih1 h1) (ih2 h2)
  | vlrec hv ih =>
    cases helab with
    | elrec _ _ _ ce _ h =>
      exact Core.Value.vrcd (ih h)
  | vinl hv ih =>
    cases helab with
    | einl _ _ _ _ ce h =>
      exact Core.Value.vinl (ih h)
  | vinr hv ih =>
    cases helab with
    | einr _ _ _ _ ce h =>
      exact Core.Value.vinr (ih h)
  | vfclos hv ih =>
    cases helab with
    | efclos _ _ _ _ _ _ ce1 ce2 _ h1 h2 =>
      exact Core.Value.vfclos (ih h1)
  | vfold hv ih =>
    cases helab with
    | efold _ _ _ ce h =>
      exact Core.Value.vfold (ih h)
  | vmstruct hv ih =>
    cases helab with
    | mstruct _ _ _ _ h => exact ih h

/-- The linearized wire is well-typed: under any context that reaches the
provider type `⟦Γ₁⟧` at index `shift`, `wire_shift ⟦D⟧` has the interface type
`⟦D⟧`. -/
theorem wire_typed {Γ₁ D : SCE.Typ} (hok : LinkOk Γ₁ D)
    : ∀ {C : Core.Typ} {shift : Nat},
      Core.Lookup C shift (elabTyp Γ₁)
      → HasType C (wire shift (elabTyp D)) (elabTyp D) := by
  induction hok with
  | one hrl =>
    intro C shift hlook
    simp only [wire, elabTyp]
    exact HasType.trcd (HasType.trproj (HasType.tproj HasType.tquery hlook)
      (type_safe_record_lookup hrl))
  | more hok' hrl ih =>
    intro C shift hlook
    simp only [wire, elabTyp]
    exact HasType.tmrg (ih hlook)
      (HasType.trcd (HasType.trproj
        (HasType.tproj HasType.tquery (Core.Lookup.succ hlook))
        (type_safe_record_lookup hrl)))

/-- The single-import wire, stated purely at the target: `wire_shift {l:A}` is
well-typed whenever the provider type reachable at `shift` has an `l : A` field. -/
theorem wire_typed_rcd {A₁ A : Core.Typ} {l : String} (hrl : Core.RLookup A₁ l A)
    : ∀ {C : Core.Typ} {shift : Nat},
      Core.Lookup C shift A₁ → HasType C (wire shift (.rcd l A)) (.rcd l A) := by
  intro C shift hlook
  simp only [wire]
  exact HasType.trcd (HasType.trproj (HasType.tproj HasType.tquery hlook) hrl)

/-- The linearized link composition is well-typed at `g1 & B` — the check the
OCaml linker replays on every link, discharged once and for all for the step
term it emits.  The wire hypothesis is supplied by `wire_typed` (interface
`LinkOk`) or `wire_typed_rcd` (single import). -/
theorem linkedCore_typed
    {Γc g1 D B : Core.Typ} {ce₁ ce₂ : Core.Exp}
    (h₁ : HasType Γc ce₁ g1)
    (h₂ : HasType Γc ce₂ (.arr D B))
    (hw : ∀ {C : Core.Typ} {shift : Nat}, Core.Lookup C shift g1 → HasType C (wire shift D) D)
    : HasType Γc (linkedCore g1 D B ce₁ ce₂) (.and g1 B) := by
  simp only [linkedCore, linkStep]
  apply HasType.tapp (HasType.tapp ?_ h₁) h₂
  apply HasType.tlam
  apply HasType.tlam
  apply HasType.tmrg
  · exact HasType.tproj HasType.tquery (Core.Lookup.succ Core.Lookup.zero)
  · exact HasType.tapp
      (HasType.tproj HasType.tquery (Core.Lookup.succ Core.Lookup.zero))
      (hw Core.Lookup.zero)

/-- Restoring the ambient context types both operands independently. -/
theorem nmrgCore_typed {Γc a b : Core.Typ} {ce₁ ce₂ : Core.Exp}
    (h₁ : HasType Γc ce₁ a) (h₂ : HasType Γc ce₂ b)
    : HasType Γc (nmrgCore ce₁ ce₂) (.and a b) := by
  exact HasType.tproj
    (HasType.tmrg HasType.tquery
      (HasType.tmrg
        (HasType.tbox (HasType.tproj HasType.tquery Core.Lookup.zero) h₁)
        (HasType.tbox
          (HasType.tproj HasType.tquery (Core.Lookup.succ Core.Lookup.zero)) h₂)))
    Core.Lookup.zero

theorem type_preservation
    {Γ A : SCE.Typ} {es : SCE.Exp} {ec : Core.Exp}
    (h : elabExp Γ es A ec)
    : HasType (elabTyp Γ) ec (elabTyp A) := by
    induction h with
    | equery =>
      exact HasType.tquery
    | elit ctx n =>
      simp [elabTyp]
      exact HasType.tint
    | eunit ctx =>
      simp [elabTyp]
      exact HasType.tunit
    | eapp ctx A B se1 se2 ce1 ce2 _ _ ih1 ih2 =>
      exact HasType.tapp ih1 ih2
    | eproj ctx A B se ce i _ hlook ih =>
      exact HasType.tproj ih (type_safe_index_lookup hlook)
    | ebox ctx ctx' A se1 se2 ce1 ce2 _ _ ih1 ih2 =>
      exact HasType.tbox ih1 ih2
    | edmrg ctx A B se1 se2 ce1 ce2 _ _ ih1 ih2 =>
      simp [elabTyp]
      exact HasType.tmrg ih1 ih2
    | enmrg ctx A B se1 se2 ce1 ce2 _ _ ih1 ih2 =>
      exact nmrgCore_typed ih1 ih2
    | elam ctx A B se ce _ ih =>
      simp [elabTyp]
      exact HasType.tlam ih
    | erproj ctx A B se ce l _ hlook ih =>
      exact HasType.trproj ih (type_safe_record_lookup hlook)
    | eclos ctx ctx' A B se1 se2 ce1 ce2 hval h1 h2 ih1 ih2 =>
      simp [elabTyp]
      exact HasType.tclos (elab_value h1 hval) ih1 ih2
    | elrec ctx A se ce l _ ih =>
      simp [elabTyp]
      exact HasType.trcd ih
    | letb ctx A B se1 se2 ce1 ce2 _ _ ih1 ih2 =>
      exact HasType.tproj (HasType.tmrg ih1 ih2) Core.Lookup.zero
    | openm ctx A B se1 se2 ce1 ce2 l _ _ ih1 ih2 =>
      exact HasType.tapp (HasType.tlam ih2) (HasType.trproj ih1 Core.RLookup.zero)
    | mstruct ctx B se ce _ ih =>
      exact ih
    | mfunctor ctx ctxInner A B sb se ce hs1 hs2 _ ih =>
      simp [elabTyp]
      cases sb with
      | sandboxed =>
        have := hs1 rfl
        rw [this] at ih
        simp [elabTyp] at ih
        exact HasType.tbox HasType.tunit (HasType.tlam ih)
      | open_ =>
        have := hs2 rfl
        rw [this] at ih
        simp [elabTyp] at ih
        exact HasType.tlam ih
    | mclos ctx ctx' A B se1 se2 ce1 ce2 hval h1 h2 ih1 ih2 =>
      simp [elabTyp]
      exact HasType.tclos (elab_value h1 hval) ih1 ih2
    | mapp ctx A B se1 se2 ce1 ce2 _ _ ih1 ih2 =>
      exact HasType.tapp ih1 ih2
    | mlink ctx Γ₁ A mt l se1 se2 ce1 ce2 _ _ hlookup ih1 ih2 =>
      exact linkedCore_typed ih1 ih2 (wire_typed_rcd (type_safe_record_lookup hlookup))
    | mlinkn ctx Γ₁ D B se1 se2 ce1 ce2 _ _ hok ih1 ih2 =>
      exact linkedCore_typed ih1 ih2 (wire_typed hok)
    | einl ctx A B se ce _ ih =>
      simp [elabTyp]
      exact HasType.tinl ih
    | einr ctx A B se ce _ ih =>
      simp [elabTyp]
      exact HasType.tinr ih
    | ecase ctx A B C se se1 se2 ce ce1 ce2 _ _ _ ih ih1 ih2 =>
      simp [elabTyp] at ih
      exact HasType.tcase ih ih1 ih2
    | eflam ctx A B se ce _ ih =>
      simp [elabTyp] at ih ⊢
      exact HasType.tflam ih
    | efclos ctx ctx' A B se1 se2 ce1 ce2 hval h1 h2 ih1 ih2 =>
      simp [elabTyp] at ih2 ⊢
      exact HasType.tfclos (elab_value h1 hval) ih1 ih2
    | efold ctx T se ce _ ih =>
      rw [elab_substTyp] at ih
      simp [elabTyp] at ih ⊢
      exact HasType.tfold ih
    | eunfold ctx T A se ce _ heq ih =>
      subst heq
      rw [elab_substTyp]
      simp [elabTyp] at ih ⊢
      exact HasType.tunfold ih rfl
