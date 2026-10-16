import LeanSce.Core.Syntax
import LeanSce.Core.Typing.Typing
import LeanSce.Core.Semantics.SmallStep
import LeanSce.Core.Semantics.Equivalence
import LeanSce.Core.Semantics.Determinism
import LeanSce.SCE.Syntax
import LeanSce.SCE.Semantics.BigStep
import LeanSce.SCE.Semantics.SmallStep
import LeanSce.SCE.Elaboration.Elaboration
import LeanSce.SCE.Elaboration.Preservation
import LeanSce.SCE.Preservation
import LeanSce.SCE.SemanticsPreservation

/-!
# Small-step forward simulation for elaboration

Every source small step of a well-typed expression is matched by one or more
Core steps of its elaboration, except one administrative source step (`letb`
entering its body), which is matched by zero Core steps and strictly decreases
a measure `letbCount` on the source term (CompCert's `forward_simulation_star`
shape).

The elaboration of a reduct is in general not the Core reduct: the encodings of
`,,` (`nmrgCore`), `open` and `link`/`linkall` (`linkedCore`) perform
administrative Core steps that have no source counterpart, and `let` is
compiled to a merge/projection that never builds the source's `box`.  The
relation is therefore

  `Sim ρs ρc Γ es A ec  :=  ∃ r, ec →* r  ∧  Ready ρs ρc Γ es A r`

where `Ready` is elaboration with the administrative steps performed *up to the
focus of the next source step* and no further.  Being behind (`ec →* r`) is
harmless; `Ready` pins how far ahead the Core term may be.
-/

open SCE S_Sem

/-! ## Core preliminaries -/

/-- One or more Core steps. -/
def CPlus (ρ a b : Core.Exp) : Prop := ∃ a', Step ρ a a' ∧ MStep ρ a' b

theorem mstep_lift {ρ ρ' : Core.Exp} (f : Core.Exp → Core.Exp)
    (hρ' : Core.Value ρ')
    (hf : ∀ {a b}, Step ρ a b → Step ρ' (f a) (f b))
    {a b : Core.Exp} (h : MStep ρ a b) : MStep ρ' (f a) (f b) := by
  induction h with
  | refl _ => exact MStep.refl hρ'
  | step hs _ ih => exact MStep.step (hf hs) ih

theorem cplus_lift {ρ ρ' : Core.Exp} (f : Core.Exp → Core.Exp)
    (hρ' : Core.Value ρ')
    (hf : ∀ {a b}, Step ρ a b → Step ρ' (f a) (f b))
    {a b : Core.Exp} (h : CPlus ρ a b) : CPlus ρ' (f a) (f b) := by
  obtain ⟨a', hs, hm⟩ := h
  exact ⟨f a', hf hs, mstep_lift f hρ' hf hm⟩

theorem cplus_mstep {ρ a b : Core.Exp} (h : CPlus ρ a b) : MStep ρ a b := by
  obtain ⟨a', hs, hm⟩ := h
  exact MStep.step hs hm

theorem cplus_mstep_trans {ρ a b c : Core.Exp}
    (h1 : CPlus ρ a b) (h2 : MStep ρ b c) : CPlus ρ a c := by
  obtain ⟨a', hs, hm⟩ := h1
  exact ⟨a', hs, mstep_trans hm h2⟩

theorem mstep_cplus_trans {ρ a b c : Core.Exp}
    (h1 : MStep ρ a b) (h2 : CPlus ρ b c) : CPlus ρ a c := by
  induction h1 with
  | refl _ => exact h2
  | step hs hm ih => exact ⟨_, hs, cplus_mstep (ih h2)⟩

theorem mstep_one {ρ a b : Core.Exp} (h : Step ρ a b) : MStep ρ a b :=
  MStep.step h (MStep.refl (step_env_value h))

theorem cplus_one {ρ a b : Core.Exp} (h : Step ρ a b) : CPlus ρ a b :=
  ⟨b, h, MStep.refl (step_env_value h)⟩

/-- Core terms whose steps do not consult the ambient environment. -/
def EnvFree (c : Core.Exp) : Prop :=
  Core.Value c ∨ ∃ w e, c = .box w e ∧ Core.Value w

theorem envfree_step {ρ c c' : Core.Exp} (hf : EnvFree c) (hs : Step ρ c c')
    {ρ' : Core.Exp} (hρ' : Core.Value ρ') : Step ρ' c c' ∧ EnvFree c' := by
  rcases hf with hv | ⟨w, e, rfl, hw⟩
  · exact absurd hs (core_value_no_step hv)
  · cases hs with
    | sboxl _ h => exact absurd h (core_value_no_step hw)
    | sboxr _ _ h => exact ⟨Step.sboxr hρ' hw h, Or.inr ⟨_, _, rfl, hw⟩⟩
    | sboxv _ _ hv2 => exact ⟨Step.sboxv hρ' hw hv2, Or.inl hv2⟩

theorem envfree_mstep {ρ c c' : Core.Exp} (hm : MStep ρ c c') :
    EnvFree c → ∀ {ρ' : Core.Exp}, Core.Value ρ' → MStep ρ' c c' ∧ EnvFree c' := by
  induction hm with
  | refl _ => intro hf _ hρ'; exact ⟨MStep.refl hρ', hf⟩
  | step hs _ ih =>
    intro hf _ hρ'
    obtain ⟨hs', hf'⟩ := envfree_step hf hs hρ'
    obtain ⟨hm', hf''⟩ := ih hf' hρ'
    exact ⟨MStep.step hs' hm', hf''⟩

theorem envfree_cplus {ρ c c' : Core.Exp} (hp : CPlus ρ c c') (hf : EnvFree c)
    {ρ' : Core.Exp} (hρ' : Core.Value ρ') : CPlus ρ' c c' ∧ EnvFree c' := by
  obtain ⟨a, hs, hm⟩ := hp
  obtain ⟨hs', hfa⟩ := envfree_step hf hs hρ'
  obtain ⟨hm', hf'⟩ := envfree_mstep hm hfa hρ'
  exact ⟨⟨a, hs', hm'⟩, hf'⟩

theorem envfree_progress {ρ ρ' rY c : Core.Exp} {P : Prop} (hEF : EnvFree rY)
    (hρ' : Core.Value ρ') (h : CPlus ρ rY c ∨ (MStep ρ rY c ∧ P)) :
    (CPlus ρ' rY c ∨ (MStep ρ' rY c ∧ P)) ∧ EnvFree c := by
  rcases h with hp | ⟨hm', hP⟩
  · obtain ⟨hp', hEFc⟩ := envfree_cplus hp hEF hρ'
    exact ⟨Or.inl hp', hEFc⟩
  · obtain ⟨hm'', hEFc⟩ := envfree_mstep hm' hEF hρ'
    exact ⟨Or.inr ⟨hm'', hP⟩, hEFc⟩

/-! ## The stutter measure -/

/-- Number of `letb` nodes outside binders.  Values have measure 0. -/
def letbCount : SCE.Exp → Nat
  | .query => 0
  | .proj e _ => letbCount e
  | .lit _ => 0
  | .unit => 0
  | .lam _ _ => 0
  | .box e1 e2 => letbCount e1 + letbCount e2
  | .clos _ _ _ => 0
  | .app e1 e2 => letbCount e1 + letbCount e2
  | .mrg e1 e2 => letbCount e1 + letbCount e2
  | .lrec _ e => letbCount e
  | .rproj e _ => letbCount e
  | .mstruct e => letbCount e
  | .mfunctor _ _ _ => 0
  | .mclos _ _ _ => 0
  | .mlink e1 e2 => letbCount e1 + letbCount e2
  | .mapp e1 e2 => letbCount e1 + letbCount e2
  | .nmrg e1 e2 => letbCount e1 + letbCount e2
  | .letb e1 e2 => letbCount e1 + letbCount e2 + 1
  | .openm e1 e2 => letbCount e1 + letbCount e2
  | .mlinkn e1 e2 => letbCount e1 + letbCount e2
  | .inl _ e => letbCount e
  | .inr _ e => letbCount e
  | .case e e1 e2 => letbCount e + letbCount e1 + letbCount e2
  | .flam _ _ _ => 0
  | .fclos _ _ _ _ => 0
  | .fold _ e => letbCount e
  | .unfold e => letbCount e

theorem letbCount_value {v : SCE.Exp} (hv : SCE.Value v) : letbCount v = 0 := by
  induction hv <;> simp_all [letbCount]

/-! ## The simulation relation -/

/-- The body of the inner `λ` of the linker step `linkStep`. -/
def linkInner (D : Core.Typ) : Core.Exp :=
  .mrg (.proj .query 1) (.app (.proj .query 1) (wire 0 D))

theorem linkStep_eq (g1 D B : Core.Typ) :
    linkStep g1 D B = .lam g1 (.lam (.arr D B) (linkInner D)) := rfl

/-- `Ready ρs ρc Γ es A r`: under source environment `ρs` and Core environment
`ρc` (with `ρs : Γ ⤳ ρc`), the Core term `r` is the elaboration of `es` at type
`A` with exactly the administrative steps before the next source step done. -/
inductive Ready : SCE.Exp → Core.Exp → SCE.Typ → SCE.Exp → SCE.Typ → Core.Exp → Prop where
  | val {ρs ρc Γ e A c}
    : SCE.Value e → elabExp Γ e A c → Ready ρs ρc Γ e A c
  | query {ρs ρc Γ}
    : Ready ρs ρc Γ .query Γ .query
  | lam {ρs ρc Γ A B e c}
    : elabExp (.and Γ A) e B c
    → Ready ρs ρc Γ (.lam A e) (.arr A B) (.lam (elabTyp A) c)
  | flam {ρs ρc Γ A B e c}
    : elabExp (.and (.and Γ (.arr A B)) A) e B c
    → Ready ρs ρc Γ (.flam A B e) (.arr A B) (.flam (elabTyp A) (elabTyp B) c)
  | mfunctor {ρs ρc Γ sb A e T c}
    : elabExp Γ (.mfunctor sb A e) T c
    → Ready ρs ρc Γ (.mfunctor sb A e) T c
  | app1 {ρs ρc Γ A B e1 e2 r1 c2}
    : ¬ SCE.Value e1 → Ready ρs ρc Γ e1 (.arr A B) r1 → elabExp Γ e2 A c2
    → Ready ρs ρc Γ (.app e1 e2) B (.app r1 c2)
  | app2 {ρs ρc Γ A B v1 e2 c1 r2}
    : SCE.Value v1 → elabExp Γ v1 (.arr A B) c1 → Ready ρs ρc Γ e2 A r2
    → Ready ρs ρc Γ (.app v1 e2) B (.app c1 r2)
  | mapp1 {ρs ρc Γ A B e1 e2 r1 c2}
    : ¬ SCE.Value e1 → Ready ρs ρc Γ e1 (.marr A B) r1 → elabExp Γ e2 A c2
    → Ready ρs ρc Γ (.mapp e1 e2) B (.app r1 c2)
  | mapp2 {ρs ρc Γ A B v1 e2 c1 r2}
    : SCE.Value v1 → elabExp Γ v1 (.marr A B) c1 → Ready ρs ρc Γ e2 A r2
    → Ready ρs ρc Γ (.mapp v1 e2) B (.app c1 r2)
  | proj {ρs ρc Γ A B e r i}
    : Ready ρs ρc Γ e A r → SLookup A i B
    → Ready ρs ρc Γ (.proj e i) B (.proj r i)
  | box1 {ρs ρc Γ Γ' A e1 e2 r1 c2}
    : ¬ SCE.Value e1 → Ready ρs ρc Γ e1 Γ' r1 → elabExp Γ' e2 A c2
    → Ready ρs ρc Γ (.box e1 e2) A (.box r1 c2)
  | box2 {ρs ρc Γ Γ' A v1 e2 c1 r2}
    : SCE.Value v1 → elabExp .top v1 Γ' c1 → Ready v1 c1 Γ' e2 A r2
    → Ready ρs ρc Γ (.box v1 e2) A (.box c1 r2)
  | mrg1 {ρs ρc Γ A B e1 e2 r1 c2}
    : ¬ SCE.Value e1 → Ready ρs ρc Γ e1 A r1 → elabExp (.and Γ A) e2 B c2
    → Ready ρs ρc Γ (.mrg e1 e2) (.and A B) (.mrg r1 c2)
  | mrg2 {ρs ρc Γ A B v1 e2 c1 r2}
    : SCE.Value v1 → elabExp Γ v1 A c1
    → Ready (.mrg ρs v1) (.mrg ρc c1) (.and Γ A) e2 B r2
    → Ready ρs ρc Γ (.mrg v1 e2) (.and A B) (.mrg c1 r2)
  | nmrg1 {ρs ρc Γ A B e1 e2 r1 c2}
    : ¬ SCE.Value e1 → Ready ρs ρc Γ e1 A r1 → elabExp Γ e2 B c2
    → Ready ρs ρc Γ (.nmrg e1 e2) (.and A B)
        (.proj (.mrg ρc (.mrg (.box ρc r1) (.box (.proj .query 1) c2))) 0)
  | nmrg2 {ρs ρc Γ A B v1 e2 c1 r2}
    : SCE.Value v1 → elabExp Γ v1 A c1 → Ready ρs ρc Γ e2 B r2
    → Ready ρs ρc Γ (.nmrg v1 e2) (.and A B)
        (.proj (.mrg ρc (.mrg c1 (.box ρc r2))) 0)
  | lrec {ρs ρc Γ A e r l}
    : Ready ρs ρc Γ e A r → Ready ρs ρc Γ (.lrec l e) (.rcd l A) (.lrec l r)
  | rproj {ρs ρc Γ A B e r l}
    : Ready ρs ρc Γ e B r → SRLookup B l A
    → Ready ρs ρc Γ (.rproj e l) A (.rproj r l)
  | letb {ρs ρc Γ A B e1 e2 r1 c2}
    : Ready ρs ρc Γ e1 A r1 → elabExp (.and Γ A) e2 B c2
    → Ready ρs ρc Γ (.letb e1 e2) B (.proj (.mrg r1 c2) 0)
  | letres {ρs ρc Γ A B v1 e2 c1 r2}
    : SCE.Value v1 → elabExp Γ v1 A c1
    → Ready (.mrg ρs v1) (.mrg ρc c1) (.and Γ A) e2 B r2
    → Ready ρs ρc Γ (.box (.mrg ρs v1) e2) B (.proj (.mrg c1 r2) 0)
  | openm {ρs ρc Γ A B e1 e2 r1 c2 l}
    : Ready ρs ρc Γ e1 (.rcd l A) r1 → elabExp (.and Γ A) e2 B c2
    → Ready ρs ρc Γ (.openm e1 e2) B (.app (.clos ρc (elabTyp A) c2) (.rproj r1 l))
  | mstruct {ρs ρc Γ B e r}
    : Ready ρs ρc Γ e B r → Ready ρs ρc Γ (.mstruct e) (.sig B) r
  | mlink1 {ρs ρc Γ Γ₁ A B e1 e2 r1 c2 l}
    : ¬ SCE.Value e1 → Ready ρs ρc Γ e1 Γ₁ r1
    → elabExp Γ e2 (.marr (.rcd l A) B) c2 → SRLookup Γ₁ l A
    → Ready ρs ρc Γ (.mlink e1 e2) (.and Γ₁ B)
        (.app (.app (.clos ρc (elabTyp Γ₁)
          (.lam (.arr (elabTyp (.rcd l A)) (elabTyp B)) (linkInner (elabTyp (.rcd l A))))) r1) c2)
  | mlink2 {ρs ρc Γ Γ₁ A B v1 e2 c1 r2 l}
    : SCE.Value v1 → elabExp Γ v1 Γ₁ c1
    → Ready ρs ρc Γ e2 (.marr (.rcd l A) B) r2 → SRLookup Γ₁ l A
    → Ready ρs ρc Γ (.mlink v1 e2) (.and Γ₁ B)
        (.app (.clos (.mrg ρc c1) (.arr (elabTyp (.rcd l A)) (elabTyp B))
          (linkInner (elabTyp (.rcd l A)))) r2)
  | mlinkn1 {ρs ρc Γ Γ₁ D B e1 e2 r1 c2}
    : ¬ SCE.Value e1 → Ready ρs ρc Γ e1 Γ₁ r1
    → elabExp Γ e2 (.marr D B) c2 → LinkOk Γ₁ D
    → Ready ρs ρc Γ (.mlinkn e1 e2) (.and Γ₁ B)
        (.app (.app (.clos ρc (elabTyp Γ₁)
          (.lam (.arr (elabTyp D) (elabTyp B)) (linkInner (elabTyp D)))) r1) c2)
  | mlinkn2 {ρs ρc Γ Γ₁ D B v1 e2 c1 r2}
    : SCE.Value v1 → elabExp Γ v1 Γ₁ c1
    → Ready ρs ρc Γ e2 (.marr D B) r2 → LinkOk Γ₁ D
    → Ready ρs ρc Γ (.mlinkn v1 e2) (.and Γ₁ B)
        (.app (.clos (.mrg ρc c1) (.arr (elabTyp D) (elabTyp B)) (linkInner (elabTyp D))) r2)
  /-- the linker's result while the functor body runs: the Core term still
  sits under the `box` of the linker's inner closure body. -/
  | linkres {ρs ρc Γ Γ₁ B v1 Y c1 ρ' rY}
    : SCE.Value v1 → elabExp Γ v1 Γ₁ c1 → Core.Value ρ' → ¬ SCE.Value Y
    → Ready (.mrg ρs v1) (.mrg ρc c1) (.and Γ Γ₁) Y B rY → EnvFree rY
    → Ready ρs ρc Γ (.mrg v1 Y) (.and Γ₁ B) (.box ρ' (.mrg c1 rY))
  | inl {ρs ρc Γ A B e r}
    : Ready ρs ρc Γ e A r → Ready ρs ρc Γ (.inl B e) (.or A B) (.inl (elabTyp B) r)
  | inr {ρs ρc Γ A B e r}
    : Ready ρs ρc Γ e B r → Ready ρs ρc Γ (.inr A e) (.or A B) (.inr (elabTyp A) r)
  | case {ρs ρc Γ A B C e e1 e2 r c1 c2}
    : Ready ρs ρc Γ e (.or A B) r → elabExp (.and Γ A) e1 C c1 → elabExp (.and Γ B) e2 C c2
    → Ready ρs ρc Γ (.case e e1 e2) C (.case r c1 c2)
  | fold {ρs ρc Γ T e r}
    : Ready ρs ρc Γ e (substTyp 0 (.mu T) T) r
    → Ready ρs ρc Γ (.fold T e) (.mu T) (.fold (elabTyp T) r)
  | unfold {ρs ρc Γ T A e r}
    : Ready ρs ρc Γ e (.mu T) r → A = substTyp 0 (.mu T) T
    → Ready ρs ρc Γ (.unfold e) A (.unfold r)

/-- The simulation relation: the Core term reaches a `Ready` form. -/
def Sim (ρs : SCE.Exp) (ρc : Core.Exp) (Γ : SCE.Typ) (es : SCE.Exp) (A : SCE.Typ)
    (ec : Core.Exp) : Prop :=
  ∃ r, MStep ρc ec r ∧ Ready ρs ρc Γ es A r

/-- A `Ready` form of a source value is a Core value elaborating it. -/
theorem ready_value {ρs ρc Γ e A r} (h : Ready ρs ρc Γ e A r) (hv : SCE.Value e) :
    elabExp Γ e A r := by
  induction h with
  | val _ he => exact he
  | mrg1 hnv _ _ _ => cases hv with | vmrg h1 _ => exact absurd h1 hnv
  | mrg2 hv1 he1 _ ih =>
    cases hv with | vmrg _ h2 => exact elabExp.edmrg _ _ _ _ _ _ _ he1 (ih h2)
  | linkres _ _ _ hnY _ _ _ => cases hv with | vmrg _ h2 => exact absurd h2 hnY
  | lrec _ ih => cases hv with | vlrec h => exact elabExp.elrec _ _ _ _ _ (ih h)
  | mstruct _ ih => cases hv with | vmstruct h => exact elabExp.mstruct _ _ _ _ (ih h)
  | inl _ ih => cases hv with | vinl h => exact elabExp.einl _ _ _ _ _ (ih h)
  | inr _ ih => cases hv with | vinr h => exact elabExp.einr _ _ _ _ _ (ih h)
  | fold _ ih => cases hv with | vfold h => exact elabExp.efold _ _ _ _ (ih h)
  | _ => cases hv

theorem sim_of_mstep {ρs ρc Γ es A a b} (hm : MStep ρc a b) (h : Sim ρs ρc Γ es A b) :
    Sim ρs ρc Γ es A a := by
  obtain ⟨r, hm', hr⟩ := h
  exact ⟨r, mstep_trans hm hm', hr⟩

theorem sim_of_ready {ρs ρc Γ es A r} (hρc : Core.Value ρc) (h : Ready ρs ρc Γ es A r) :
    Sim ρs ρc Γ es A r := ⟨r, MStep.refl hρc, h⟩

/-! ### Administrative prefixes, shared by initialisation and simulation -/

theorem app_ready {ρs ρc Γ A B e1 e2 r1 c2} (hρc : Core.Value ρc)
    (hr1 : Ready ρs ρc Γ e1 (.arr A B) r1) (he2 : elabExp Γ e2 A c2)
    (h2 : SCE.Value e1 → Sim ρs ρc Γ e2 A c2) :
    Sim ρs ρc Γ (.app e1 e2) B (.app r1 c2) := by
  by_cases hv : SCE.Value e1
  · have he1 := ready_value hr1 hv
    obtain ⟨r2, hm, hr2⟩ := h2 hv
    exact ⟨_, mstep_app_right (elab_value he1 hv) hm, Ready.app2 hv he1 hr2⟩
  · exact sim_of_ready hρc (Ready.app1 hv hr1 he2)

theorem mapp_ready {ρs ρc Γ A B e1 e2 r1 c2} (hρc : Core.Value ρc)
    (hr1 : Ready ρs ρc Γ e1 (.marr A B) r1) (he2 : elabExp Γ e2 A c2)
    (h2 : SCE.Value e1 → Sim ρs ρc Γ e2 A c2) :
    Sim ρs ρc Γ (.mapp e1 e2) B (.app r1 c2) := by
  by_cases hv : SCE.Value e1
  · have he1 := ready_value hr1 hv
    obtain ⟨r2, hm, hr2⟩ := h2 hv
    exact ⟨_, mstep_app_right (elab_value he1 hv) hm, Ready.mapp2 hv he1 hr2⟩
  · exact sim_of_ready hρc (Ready.mapp1 hv hr1 he2)

theorem box_ready {ρs ρc Γ Γ' A e1 e2 r1 c2} (hρc : Core.Value ρc)
    (hr1 : Ready ρs ρc Γ e1 Γ' r1) (he2 : elabExp Γ' e2 A c2)
    (h2 : SCE.Value e1 → ∀ {c1}, elabExp .top e1 Γ' c1 → Sim e1 c1 Γ' e2 A c2) :
    Sim ρs ρc Γ (.box e1 e2) A (.box r1 c2) := by
  by_cases hv : SCE.Value e1
  · have he1 := elab_value_weaken (ready_value hr1 hv) hv .top
    obtain ⟨r2, hm, hr2⟩ := h2 hv he1
    exact ⟨_, mstep_box_right hρc (elab_value he1 hv) hm, Ready.box2 hv he1 hr2⟩
  · exact sim_of_ready hρc (Ready.box1 hv hr1 he2)

theorem mrg_ready {ρs ρc Γ A B e1 e2 r1 c2} (hρc : Core.Value ρc)
    (hr1 : Ready ρs ρc Γ e1 A r1) (he2 : elabExp (.and Γ A) e2 B c2)
    (h2 : SCE.Value e1 → ∀ {c1}, elabExp Γ e1 A c1 →
      Sim (.mrg ρs e1) (.mrg ρc c1) (.and Γ A) e2 B c2) :
    Sim ρs ρc Γ (.mrg e1 e2) (.and A B) (.mrg r1 c2) := by
  by_cases hv : SCE.Value e1
  · have he1 := ready_value hr1 hv
    obtain ⟨r2, hm, hr2⟩ := h2 hv he1
    exact ⟨_, mstep_mrg_right hρc (elab_value he1 hv) hm, Ready.mrg2 hv he1 hr2⟩
  · exact sim_of_ready hρc (Ready.mrg1 hv hr1 he2)

theorem nmrg_ready {ρs ρc Γ A B e1 e2 r1 c2} (hρc : Core.Value ρc)
    (hr1 : Ready ρs ρc Γ e1 A r1) (he2 : elabExp Γ e2 B c2)
    (h2 : SCE.Value e1 → Sim ρs ρc Γ e2 B c2) :
    Sim ρs ρc Γ (.nmrg e1 e2) (.and A B)
      (.proj (.mrg ρc (.mrg (.box ρc r1) (.box (.proj .query 1) c2))) 0) := by
  by_cases hv : SCE.Value e1
  · have he1 := ready_value hr1 hv
    have hv1 := elab_value he1 hv
    obtain ⟨r2, hm, hr2⟩ := h2 hv
    have E := Core.Value.vmrg hρc hρc
    have E2 := Core.Value.vmrg E hv1
    refine ⟨_, ?_, Ready.nmrg2 hv he1 hr2⟩
    refine MStep.step (Step.sproj hρc (Step.smrgr hρc hρc
      (Step.smrgl E (Step.sboxv E hρc hv1)))) ?_
    refine MStep.step (Step.sproj hρc (Step.smrgr hρc hρc
      (Step.smrgr E hv1 (Step.sboxl E2 (Step.sproj E2 (Step.squery E2)))))) ?_
    refine MStep.step (Step.sproj hρc (Step.smrgr hρc hρc
      (Step.smrgr E hv1 (Step.sboxl E2
        (Step.sprojv E2 E2 (Core.LookupV.lvsucc Core.LookupV.lvzero)))))) ?_
    exact mstep_proj (mstep_mrg_right hρc hρc (mstep_mrg_right E hv1
      (mstep_box_right E2 hρc hm)))
  · exact sim_of_ready hρc (Ready.nmrg1 hv hr1 he2)

/-- The linker step's administrative prefix once the provider is a value. -/
theorem linker_admin {ρc r1 c2 : Core.Exp} {g1 T : Core.Typ} {M : Core.Exp}
    (hρc : Core.Value ρc) (hv1 : Core.Value r1) :
    MStep ρc (.app (.app (.clos ρc g1 (.lam T M)) r1) c2)
      (.app (.clos (.mrg ρc r1) T M) c2) := by
  have E := Core.Value.vmrg hρc hv1
  refine MStep.step (Step.sappl hρc (Step.sbeta hρc hv1 hρc)) ?_
  refine MStep.step (Step.sappl hρc (Step.sboxr hρc E (Step.sclos E))) ?_
  exact MStep.step (Step.sappl hρc (Step.sboxv hρc E (Core.Value.vclos E))) (MStep.refl hρc)

theorem mlink_ready {ρs ρc Γ Γ₁ A B e1 e2 r1 c2 l} (hρc : Core.Value ρc)
    (hr1 : Ready ρs ρc Γ e1 Γ₁ r1) (he2 : elabExp Γ e2 (.marr (.rcd l A) B) c2)
    (hl : SRLookup Γ₁ l A)
    (h2 : SCE.Value e1 → Sim ρs ρc Γ e2 (.marr (.rcd l A) B) c2) :
    Sim ρs ρc Γ (.mlink e1 e2) (.and Γ₁ B)
        (.app (.app (.clos ρc (elabTyp Γ₁)
          (.lam (.arr (elabTyp (.rcd l A)) (elabTyp B)) (linkInner (elabTyp (.rcd l A))))) r1) c2) := by
  by_cases hv : SCE.Value e1
  · have he1 := ready_value hr1 hv
    have hv1 := elab_value he1 hv
    obtain ⟨r2, hm, hr2⟩ := h2 hv
    exact ⟨_, mstep_trans (linker_admin hρc hv1)
      (mstep_app_right (Core.Value.vclos (Core.Value.vmrg hρc hv1)) hm),
      Ready.mlink2 hv he1 hr2 hl⟩
  · exact sim_of_ready hρc (Ready.mlink1 hv hr1 he2 hl)

theorem mlinkn_ready {ρs ρc Γ Γ₁ D B e1 e2 r1 c2} (hρc : Core.Value ρc)
    (hr1 : Ready ρs ρc Γ e1 Γ₁ r1) (he2 : elabExp Γ e2 (.marr D B) c2)
    (hok : LinkOk Γ₁ D)
    (h2 : SCE.Value e1 → Sim ρs ρc Γ e2 (.marr D B) c2) :
    Sim ρs ρc Γ (.mlinkn e1 e2) (.and Γ₁ B)
        (.app (.app (.clos ρc (elabTyp Γ₁)
          (.lam (.arr (elabTyp D) (elabTyp B)) (linkInner (elabTyp D)))) r1) c2) := by
  by_cases hv : SCE.Value e1
  · have he1 := ready_value hr1 hv
    have hv1 := elab_value he1 hv
    obtain ⟨r2, hm, hr2⟩ := h2 hv
    exact ⟨_, mstep_trans (linker_admin hρc hv1)
      (mstep_app_right (Core.Value.vclos (Core.Value.vmrg hρc hv1)) hm),
      Ready.mlinkn2 hv he1 hr2 hok⟩
  · exact sim_of_ready hρc (Ready.mlinkn1 hv hr1 he2 hok)

/-- Environment extension used by every rule that evaluates under `ρ , v`. -/
theorem env_ext {ρs ρc Γ v A c} (henv : elabExp .top ρs Γ ρc) (hv : SCE.Value v)
    (hc : elabExp Γ v A c) : elabExp .top (.mrg ρs v) (.and Γ A) (.mrg ρc c) :=
  elabExp.edmrg _ _ _ _ _ _ _ henv (elab_value_weaken hc hv _)

/-! ## Initialisation: an elaboration is `Sim`-related to its source -/

theorem sim_init {Γ es A ec} (helab : elabExp Γ es A ec) :
    ∀ {ρs ρc}, SCE.Value ρs → elabExp .top ρs Γ ρc → Sim ρs ρc Γ es A ec := by
  induction helab with
  | equery =>
    intro ρs ρc hρs henv
    exact sim_of_ready (elab_value henv hρs) Ready.query
  | elit =>
    intro ρs ρc hρs henv
    exact sim_of_ready (elab_value henv hρs) (Ready.val SCE.Value.vint (elabExp.elit _ _))
  | eunit =>
    intro ρs ρc hρs henv
    exact sim_of_ready (elab_value henv hρs) (Ready.val SCE.Value.vunit (elabExp.eunit _))
  | eapp _ _ _ _ _ _ ce2 h1 h2 ih1 ih2 =>
    intro ρs ρc hρs henv
    have hρc := elab_value henv hρs
    obtain ⟨r1, hm1, hr1⟩ := ih1 hρs henv
    exact sim_of_mstep (mstep_app_left hm1 ce2)
      (app_ready hρc hr1 h2 (fun _ => ih2 hρs henv))
  | eproj _ _ _ _ _ _ _ hl ih =>
    intro ρs ρc hρs henv
    obtain ⟨r, hm, hr⟩ := ih hρs henv
    exact ⟨_, mstep_proj hm, Ready.proj hr hl⟩
  | ebox _ _ _ _ _ _ ce2 h1 h2 ih1 ih2 =>
    intro ρs ρc hρs henv
    have hρc := elab_value henv hρs
    obtain ⟨r1, hm1, hr1⟩ := ih1 hρs henv
    exact sim_of_mstep (mstep_box_left hm1 ce2)
      (box_ready hρc hr1 h2 (fun hv _ hc1 => ih2 hv hc1))
  | edmrg _ _ _ _ _ _ ce2 h1 h2 ih1 ih2 =>
    intro ρs ρc hρs henv
    have hρc := elab_value henv hρs
    obtain ⟨r1, hm1, hr1⟩ := ih1 hρs henv
    exact sim_of_mstep (mstep_mrg_left hm1 ce2)
      (mrg_ready hρc hr1 h2 (fun hv _ hc1 =>
        ih2 (SCE.Value.vmrg hρs hv) (env_ext henv hv hc1)))
  | enmrg _ _ _ _ _ _ ce2 h1 h2 ih1 ih2 =>
    intro ρs ρc hρs henv
    have hρc := elab_value henv hρs
    have E := Core.Value.vmrg hρc hρc
    obtain ⟨r1, hm1, hr1⟩ := ih1 hρs henv
    refine sim_of_mstep ?_ (nmrg_ready hρc hr1 h2 (fun _ => ih2 hρs henv))
    simp only [nmrgCore]
    refine MStep.step (Step.sproj hρc (Step.smrgl hρc (Step.squery hρc))) ?_
    refine MStep.step (Step.sproj hρc (Step.smrgr hρc hρc
      (Step.smrgl E (Step.sboxl E (Step.sproj E (Step.squery E)))))) ?_
    refine MStep.step (Step.sproj hρc (Step.smrgr hρc hρc
      (Step.smrgl E (Step.sboxl E (Step.sprojv E E Core.LookupV.lvzero))))) ?_
    exact mstep_proj (mstep_mrg_right hρc hρc (mstep_mrg_left
      (mstep_box_right E hρc hm1) _))
  | elam _ _ _ _ _ h _ =>
    intro ρs ρc hρs henv
    exact sim_of_ready (elab_value henv hρs) (Ready.lam h)
  | erproj _ _ _ _ _ _ _ hl ih =>
    intro ρs ρc hρs henv
    obtain ⟨r, hm, hr⟩ := ih hρs henv
    exact ⟨_, mstep_rproj hm, Ready.rproj hr hl⟩
  | eclos _ _ _ _ _ _ _ _ hv h1 h2 _ _ =>
    intro ρs ρc hρs henv
    exact sim_of_ready (elab_value henv hρs)
      (Ready.val (SCE.Value.vclos hv) (elabExp.eclos _ _ _ _ _ _ _ _ hv h1 h2))
  | elrec _ _ _ _ _ _ ih =>
    intro ρs ρc hρs henv
    obtain ⟨r, hm, hr⟩ := ih hρs henv
    exact ⟨_, mstep_lrec hm, Ready.lrec hr⟩
  | letb _ _ _ _ _ _ ce2 h1 h2 ih1 _ =>
    intro ρs ρc hρs henv
    obtain ⟨r1, hm1, hr1⟩ := ih1 hρs henv
    exact ⟨_, mstep_proj (mstep_mrg_left hm1 ce2), Ready.letb hr1 h2⟩
  | openm _ _ _ _ _ _ _ _ h1 h2 ih1 _ =>
    intro ρs ρc hρs henv
    have hρc := elab_value henv hρs
    obtain ⟨r1, hm1, hr1⟩ := ih1 hρs henv
    exact ⟨_, MStep.step (Step.sappl hρc (Step.sclos hρc))
      (mstep_app_right (Core.Value.vclos hρc) (mstep_rproj hm1)), Ready.openm hr1 h2⟩
  | mstruct _ _ _ _ _ ih =>
    intro ρs ρc hρs henv
    obtain ⟨r, hm, hr⟩ := ih hρs henv
    exact ⟨_, hm, Ready.mstruct hr⟩
  | mfunctor _ _ _ _ _ _ _ hs1 hs2 hb _ =>
    intro ρs ρc hρs henv
    exact sim_of_ready (elab_value henv hρs)
      (Ready.mfunctor (elabExp.mfunctor _ _ _ _ _ _ _ hs1 hs2 hb))
  | mclos _ _ _ _ _ _ _ _ hv h1 h2 _ _ =>
    intro ρs ρc hρs henv
    exact sim_of_ready (elab_value henv hρs)
      (Ready.val (SCE.Value.vmclos hv) (elabExp.mclos _ _ _ _ _ _ _ _ hv h1 h2))
  | mapp _ _ _ _ _ _ ce2 h1 h2 ih1 ih2 =>
    intro ρs ρc hρs henv
    have hρc := elab_value henv hρs
    obtain ⟨r1, hm1, hr1⟩ := ih1 hρs henv
    exact sim_of_mstep (mstep_app_left hm1 ce2)
      (mapp_ready hρc hr1 h2 (fun _ => ih2 hρs henv))
  | mlink _ _ _ _ _ _ _ _ ce2 h1 h2 hl ih1 ih2 =>
    intro ρs ρc hρs henv
    have hρc := elab_value henv hρs
    obtain ⟨r1, hm1, hr1⟩ := ih1 hρs henv
    refine sim_of_mstep ?_ (mlink_ready hρc hr1 h2 hl (fun _ => ih2 hρs henv))
    simp only [linkedCore, linkStep_eq]
    exact MStep.step (Step.sappl hρc (Step.sappl hρc (Step.sclos hρc)))
      (mstep_app_left (mstep_app_right (Core.Value.vclos hρc) hm1) ce2)
  | mlinkn _ _ _ _ _ _ _ ce2 h1 h2 hok ih1 ih2 =>
    intro ρs ρc hρs henv
    have hρc := elab_value henv hρs
    obtain ⟨r1, hm1, hr1⟩ := ih1 hρs henv
    refine sim_of_mstep ?_ (mlinkn_ready hρc hr1 h2 hok (fun _ => ih2 hρs henv))
    simp only [linkedCore, linkStep_eq]
    exact MStep.step (Step.sappl hρc (Step.sappl hρc (Step.sclos hρc)))
      (mstep_app_left (mstep_app_right (Core.Value.vclos hρc) hm1) ce2)
  | einl _ _ _ _ _ _ ih =>
    intro ρs ρc hρs henv
    obtain ⟨r, hm, hr⟩ := ih hρs henv
    exact ⟨_, mstep_inl hm, Ready.inl hr⟩
  | einr _ _ _ _ _ _ ih =>
    intro ρs ρc hρs henv
    obtain ⟨r, hm, hr⟩ := ih hρs henv
    exact ⟨_, mstep_inr hm, Ready.inr hr⟩
  | ecase _ _ _ _ _ _ _ _ _ _ _ h1 h2 ih _ _ =>
    intro ρs ρc hρs henv
    obtain ⟨r, hm, hr⟩ := ih hρs henv
    exact ⟨_, mstep_case hm, Ready.case hr h1 h2⟩
  | eflam _ _ _ _ _ h _ =>
    intro ρs ρc hρs henv
    exact sim_of_ready (elab_value henv hρs) (Ready.flam h)
  | efclos _ _ _ _ _ _ _ _ hv h1 h2 _ _ =>
    intro ρs ρc hρs henv
    exact sim_of_ready (elab_value henv hρs)
      (Ready.val (SCE.Value.vfclos hv) (elabExp.efclos _ _ _ _ _ _ _ _ hv h1 h2))
  | efold _ _ _ _ _ ih =>
    intro ρs ρc hρs henv
    obtain ⟨r, hm, hr⟩ := ih hρs henv
    exact ⟨_, mstep_fold hm, Ready.fold hr⟩
  | eunfold _ _ _ _ _ _ heq ih =>
    intro ρs ρc hρs henv
    obtain ⟨r, hm, hr⟩ := ih hρs henv
    exact ⟨_, mstep_unfold hm, Ready.unfold hr heq⟩

/-! ## The simulation step -/

/-- The conclusion of one simulation step: one or more Core steps, or zero or
more Core steps with a strict decrease of the stutter measure, reaching a term
`Sim`-related to the source reduct. -/
def SimStep (ρs : SCE.Exp) (ρc : Core.Exp) (Γ : SCE.Typ) (es es' : SCE.Exp) (A : SCE.Typ)
    (r : Core.Exp) : Prop :=
  ∃ c, (CPlus ρc r c ∨ (MStep ρc r c ∧ letbCount es' < letbCount es)) ∧ Sim ρs ρc Γ es' A c

/-- Lift a simulation step through an evaluation context of the Core term. -/
theorem simstep_lift {ρs' ρ' Γ' e e' A' r} {ρs ρc Γ E E' A}
    (f : Core.Exp → Core.Exp) (hρc : Core.Value ρc)
    (hf : ∀ {a b}, Step ρ' a b → Step ρc (f a) (f b))
    (hμ : letbCount e' < letbCount e → letbCount E' < letbCount E)
    (h : SimStep ρs' ρ' Γ' e e' A' r)
    (hk : ∀ {r'}, Ready ρs' ρ' Γ' e' A' r' → Sim ρs ρc Γ E' A (f r')) :
    SimStep ρs ρc Γ E E' A (f r) := by
  obtain ⟨c, hpr, r', hm, hr'⟩ := h
  refine ⟨f c, ?_, sim_of_mstep (mstep_lift f hρc hf hm) (hk hr')⟩
  rcases hpr with hp | ⟨hm', hlt⟩
  · exact Or.inl (cplus_lift f hρc hf hp)
  · exact Or.inr ⟨mstep_lift f hρc hf hm', hμ hlt⟩

theorem simstep_redex {ρs ρc Γ es es' A r c} (hρs : SCE.Value ρs)
    (henv : elabExp .top ρs Γ ρc) (hp : CPlus ρc r c) (he : elabExp Γ es' A c) :
    SimStep ρs ρc Γ es es' A r :=
  ⟨c, Or.inl hp, sim_init he hρs henv⟩

theorem simstep_redex1 {ρs ρc Γ es es' A r c} (hρs : SCE.Value ρs)
    (henv : elabExp .top ρs Γ ρc) (hs : Step ρc r c) (he : elabExp Γ es' A c) :
    SimStep ρs ρc Γ es es' A r :=
  simstep_redex hρs henv (cplus_one hs) he

theorem sim_step_ready {ρs es es'} (hstep : SStep ρs es es') :
    ∀ {ρc Γ A r}, ¬ SCE.Value es → elabExp .top ρs Γ ρc → Ready ρs ρc Γ es A r →
      SimStep ρs ρc Γ es es' A r := by
  induction hstep with
  | ssquery hρs =>
    intro ρc Γ A r hnv henv hr
    have hρc := elab_value henv hρs
    cases hr with
    | val hv _ => exact absurd hv hnv
    | query => exact simstep_redex1 hρs henv (Step.squery hρc) (elab_value_weaken henv hρs _)
  | ssappl hρs h1 ih =>
    intro ρc Γ A r hnv henv hr
    have hρc := elab_value henv hρs
    cases hr with
    | val hv _ => exact absurd hv hnv
    | app1 hnv1 hr1 he2 =>
      exact simstep_lift (fun x => .app x _) hρc (fun hs => Step.sappl hρc hs)
        (by simp [letbCount]) (ih (fun hv => value_no_step hv h1) henv hr1)
        (fun hr' => app_ready hρc hr' he2 (fun _ => sim_init he2 hρs henv))
    | app2 hv1 _ _ => exact absurd h1 (value_no_step hv1)
  | ssboxl hρs h1 ih =>
    intro ρc Γ A r hnv henv hr
    have hρc := elab_value henv hρs
    cases hr with
    | val hv _ => exact absurd hv hnv
    | box1 hnv1 hr1 he2 =>
      exact simstep_lift (fun x => .box x _) hρc (fun hs => Step.sboxl hρc hs)
        (by simp [letbCount]) (ih (fun hv => value_no_step hv h1) henv hr1)
        (fun hr' => box_ready hρc hr' he2 (fun hv _ hc1 => sim_init he2 hv hc1))
    | box2 hv1 _ _ => exact absurd h1 (value_no_step hv1)
    | letres hv1 _ _ => exact absurd h1 (value_no_step (SCE.Value.vmrg hρs hv1))
  | ssmrgl hρs h1 ih =>
    intro ρc Γ A r hnv henv hr
    have hρc := elab_value henv hρs
    cases hr with
    | val hv _ => exact absurd hv hnv
    | mrg1 hnv1 hr1 he2 =>
      exact simstep_lift (fun x => .mrg x _) hρc (fun hs => Step.smrgl hρc hs)
        (by simp [letbCount]) (ih (fun hv => value_no_step hv h1) henv hr1)
        (fun hr' => mrg_ready hρc hr' he2 (fun hv _ hc1 =>
          sim_init he2 (SCE.Value.vmrg hρs hv) (env_ext henv hv hc1)))
    | mrg2 hv1 _ _ => exact absurd h1 (value_no_step hv1)
    | linkres hv1 _ _ _ _ _ => exact absurd h1 (value_no_step hv1)
  | ssappr hρs hv1 h2 ih =>
    intro ρc Γ A r hnv henv hr
    have hρc := elab_value henv hρs
    cases hr with
    | val hv _ => exact absurd hv hnv
    | app1 hnv1 _ _ => exact absurd hv1 hnv1
    | app2 _ he1 hr2 =>
      exact simstep_lift (fun x => .app _ x) hρc
        (fun hs => Step.sappr hρc (elab_value he1 hv1) hs)
        (by simp [letbCount]) (ih (fun hv => value_no_step hv h2) henv hr2)
        (fun hr' => sim_of_ready hρc (Ready.app2 hv1 he1 hr'))
  | ssboxr hρs hv1 h2 ih =>
    intro ρc Γ A r hnv henv hr
    have hρc := elab_value henv hρs
    cases hr with
    | val hv _ => exact absurd hv hnv
    | box1 hnv1 _ _ => exact absurd hv1 hnv1
    | box2 _ he1 hr2 =>
      exact simstep_lift (fun x => .box _ x) hρc
        (fun hs => Step.sboxr hρc (elab_value he1 hv1) hs)
        (by simp [letbCount]) (ih (fun hv => value_no_step hv h2) he1 hr2)
        (fun hr' => sim_of_ready hρc (Ready.box2 hv1 he1 hr'))
    | letres hv1' he1 hr2 =>
      have hc1 := elab_value he1 hv1'
      exact simstep_lift (fun x => .proj (.mrg _ x) 0) hρc
        (fun hs => Step.sproj hρc (Step.smrgr hρc hc1 hs))
        (by simp [letbCount]) (ih (fun hv => value_no_step hv h2) (env_ext henv hv1' he1) hr2)
        (fun hr' => sim_of_ready hρc (Ready.letres hv1' he1 hr'))
  | @ssmrgr _ _ _ e2' hρs hv1 h2 ih =>
    intro ρc Γ A r hnv henv hr
    have hρc := elab_value henv hρs
    cases hr with
    | val hv _ => exact absurd hv hnv
    | mrg1 hnv1 _ _ => exact absurd hv1 hnv1
    | mrg2 _ he1 hr2 =>
      exact simstep_lift (fun x => .mrg _ x) hρc
        (fun hs => Step.smrgr hρc (elab_value he1 hv1) hs)
        (by simp [letbCount]) (ih (fun hv => value_no_step hv h2) (env_ext henv hv1 he1) hr2)
        (fun hr' => sim_of_ready hρc (Ready.mrg2 hv1 he1 hr'))
    | linkres _ he1 hρ' hnY hrY hEF =>
      have hc1 := elab_value he1 hv1
      obtain ⟨c, hpr, r', hm, hr'⟩ :=
        ih (fun hv => value_no_step hv h2) (env_ext henv hv1 he1) hrY
      have hE' := Core.Value.vmrg hρ' hc1
      have hf : ∀ {a b}, Step (.mrg _ _) a b →
          Step ρc ((fun x => Core.Exp.box _ (.mrg _ x)) a) ((fun x => Core.Exp.box _ (.mrg _ x)) b) :=
        fun hs => Step.sboxr hρc hρ' (Step.smrgr hρ' hc1 hs)
      obtain ⟨hpr', hEFc⟩ := envfree_progress hEF hE' hpr
      obtain ⟨hm2, hEF'⟩ := envfree_mstep hm hEFc hE'
      refine ⟨_, ?_, sim_of_mstep (mstep_lift _ hρc hf hm2) ?_⟩
      · rcases hpr' with hp | ⟨hm', hlt⟩
        · exact Or.inl (cplus_lift _ hρc hf hp)
        · exact Or.inr ⟨mstep_lift _ hρc hf hm', by simp [letbCount] at hlt ⊢; omega⟩
      · by_cases hY' : SCE.Value e2'
        · have he' := ready_value hr' hY'
          exact ⟨_, MStep.step (Step.sboxv hρc hρ' (Core.Value.vmrg hc1 (elab_value he' hY')))
            (MStep.refl hρc),
            Ready.val (SCE.Value.vmrg hv1 hY') (elabExp.edmrg _ _ _ _ _ _ _ he1 he')⟩
        · exact sim_of_ready hρc (Ready.linkres hv1 he1 hρ' hY' hr' hEF')
  | ssclos hρs =>
    intro ρc Γ A r hnv henv hr
    have hρc := elab_value henv hρs
    cases hr with
    | val hv _ => exact absurd hv hnv
    | lam h =>
      exact simstep_redex1 hρs henv (Step.sclos hρc)
        (elabExp.eclos _ _ _ _ _ _ _ _ hρs henv h)
  | ssbeta hρs hv1 hv2 =>
    intro ρc Γ A r hnv henv hr
    have hρc := elab_value henv hρs
    cases hr with
    | val hv _ => exact absurd hv hnv
    | app1 hnv1 _ _ => exact absurd (SCE.Value.vclos hv2) hnv1
    | app2 _ he1 hr2 =>
      have he2 := ready_value hr2 hv1
      cases he1 with
      | eclos _ _ _ _ _ _ _ _ _ henv2 hbody =>
        exact simstep_redex1 hρs henv
          (Step.sbeta hρc (elab_value he2 hv1) (elab_value henv2 hv2))
          (elabExp.ebox _ _ _ _ _ _ _
            (elabExp.edmrg _ _ _ _ _ _ _ (elab_value_weaken henv2 hv2 _)
              (elab_value_weaken he2 hv1 _)) hbody)
  | ssboxv hρs hv1 hv2 =>
    intro ρc Γ A r hnv henv hr
    have hρc := elab_value henv hρs
    cases hr with
    | val hv _ => exact absurd hv hnv
    | box1 hnv1 _ _ => exact absurd hv1 hnv1
    | box2 _ he1 hr2 =>
      have he2 := ready_value hr2 hv2
      exact simstep_redex1 hρs henv
        (Step.sboxv hρc (elab_value he1 hv1) (elab_value he2 hv2))
        (elab_value_weaken he2 hv2 _)
    | letres hv1' he1 hr2 =>
      have he2 := ready_value hr2 hv2
      exact simstep_redex1 hρs henv
        (Step.sprojv hρc (Core.Value.vmrg (elab_value he1 hv1') (elab_value he2 hv2))
          Core.LookupV.lvzero)
        (elab_value_weaken he2 hv2 _)
  | ssproj hρs h1 ih =>
    intro ρc Γ A r hnv henv hr
    have hρc := elab_value henv hρs
    cases hr with
    | val hv _ => exact absurd hv hnv
    | proj hr1 hl =>
      exact simstep_lift (fun x => .proj x _) hρc (fun hs => Step.sproj hρc hs)
        (by simp [letbCount]) (ih (fun hv => value_no_step hv h1) henv hr1)
        (fun hr' => sim_of_ready hρc (Ready.proj hr' hl))
  | ssprojv hρs hv1 hlook =>
    intro ρc Γ A r hnv henv hr
    have hρc := elab_value henv hρs
    cases hr with
    | val hv _ => exact absurd hv hnv
    | proj hr1 hl =>
      have he1 := ready_value hr1 hv1
      obtain ⟨vc', hl', he'⟩ :=
        lookup_preservation hv1 (elab_value_weaken he1 hv1 .top) hlook hl
      exact simstep_redex1 hρs henv (Step.sprojv hρc (elab_value he1 hv1) hl')
        (elab_value_weaken he' (source_lookupv_value hv1 hlook) _)
  | sslrec hρs h1 ih =>
    intro ρc Γ A r hnv henv hr
    have hρc := elab_value henv hρs
    cases hr with
    | val hv _ => exact absurd hv hnv
    | lrec hr1 =>
      exact simstep_lift (fun x => .lrec _ x) hρc (fun hs => Step.slrec hρc hs)
        (by simp [letbCount]) (ih (fun hv => value_no_step hv h1) henv hr1)
        (fun hr' => sim_of_ready hρc (Ready.lrec hr'))
  | ssrproj hρs h1 ih =>
    intro ρc Γ A r hnv henv hr
    have hρc := elab_value henv hρs
    cases hr with
    | val hv _ => exact absurd hv hnv
    | rproj hr1 hl =>
      exact simstep_lift (fun x => .rproj x _) hρc (fun hs => Step.srproj hρc hs)
        (by simp [letbCount]) (ih (fun hv => value_no_step hv h1) henv hr1)
        (fun hr' => sim_of_ready hρc (Ready.rproj hr' hl))
  | ssrprojv hρs hv1 hsel =>
    intro ρc Γ A r hnv henv hr
    have hρc := elab_value henv hρs
    cases hr with
    | val hv _ => exact absurd hv hnv
    | rproj hr1 hl =>
      have he1 := ready_value hr1 hv1
      obtain ⟨vc', hl', he'⟩ :=
        sel_preservation hv1 (elab_value_weaken he1 hv1 .top) hsel hl
      exact simstep_redex1 hρs henv (Step.srprojv hρc (elab_value he1 hv1) hl')
        (elab_value_weaken he' (source_sel_value hv1 hsel) _)
  | ssmstruct hρs h1 ih =>
    intro ρc Γ A r hnv henv hr
    have hρc := elab_value henv hρs
    cases hr with
    | val hv _ => exact absurd hv hnv
    | mstruct hr1 =>
      exact simstep_lift (fun x => x) hρc (fun hs => hs)
        (by simp [letbCount]) (ih (fun hv => value_no_step hv h1) henv hr1)
        (fun hr' => sim_of_ready hρc (Ready.mstruct hr'))
  | ssmfunctor_sandboxed hρs =>
    intro ρc Γ A r hnv henv hr
    have hρc := elab_value henv hρs
    cases hr with
    | val hv _ => exact absurd hv hnv
    | mfunctor helab =>
      cases helab with
      | mfunctor _ _ _ _ _ _ _ hs1 _ hb =>
        rw [hs1 rfl] at hb
        exact simstep_redex hρs henv
          ⟨_, Step.sboxr hρc Core.Value.vunit (Step.sclos Core.Value.vunit),
            mstep_one (Step.sboxv hρc Core.Value.vunit (Core.Value.vclos Core.Value.vunit))⟩
          (elabExp.mclos _ _ _ _ _ _ _ _ SCE.Value.vunit (elabExp.eunit _) hb)
  | ssmfunctor_open hρs =>
    intro ρc Γ A r hnv henv hr
    have hρc := elab_value henv hρs
    cases hr with
    | val hv _ => exact absurd hv hnv
    | mfunctor helab =>
      cases helab with
      | mfunctor _ _ _ _ _ _ _ _ hs2 hb =>
        rw [hs2 rfl] at hb
        exact simstep_redex1 hρs henv (Step.sclos hρc)
          (elabExp.mclos _ _ _ _ _ _ _ _ hρs henv hb)
  | ssmappl hρs h1 ih =>
    intro ρc Γ A r hnv henv hr
    have hρc := elab_value henv hρs
    cases hr with
    | val hv _ => exact absurd hv hnv
    | mapp1 hnv1 hr1 he2 =>
      exact simstep_lift (fun x => .app x _) hρc (fun hs => Step.sappl hρc hs)
        (by simp [letbCount]) (ih (fun hv => value_no_step hv h1) henv hr1)
        (fun hr' => mapp_ready hρc hr' he2 (fun _ => sim_init he2 hρs henv))
    | mapp2 hv1 _ _ => exact absurd h1 (value_no_step hv1)
  | ssmappr hρs hv1 h2 ih =>
    intro ρc Γ A r hnv henv hr
    have hρc := elab_value henv hρs
    cases hr with
    | val hv _ => exact absurd hv hnv
    | mapp1 hnv1 _ _ => exact absurd hv1 hnv1
    | mapp2 _ he1 hr2 =>
      exact simstep_lift (fun x => .app _ x) hρc
        (fun hs => Step.sappr hρc (elab_value he1 hv1) hs)
        (by simp [letbCount]) (ih (fun hv => value_no_step hv h2) henv hr2)
        (fun hr' => sim_of_ready hρc (Ready.mapp2 hv1 he1 hr'))
  | ssmbeta hρs hv1 hv2 =>
    intro ρc Γ A r hnv henv hr
    have hρc := elab_value henv hρs
    cases hr with
    | val hv _ => exact absurd hv hnv
    | mapp1 hnv1 _ _ => exact absurd (SCE.Value.vmclos hv2) hnv1
    | mapp2 _ he1 hr2 =>
      have he2 := ready_value hr2 hv1
      cases he1 with
      | mclos _ _ _ _ _ _ _ _ _ henv2 hbody =>
        exact simstep_redex1 hρs henv
          (Step.sbeta hρc (elab_value he2 hv1) (elab_value henv2 hv2))
          (elabExp.ebox _ _ _ _ _ _ _
            (elabExp.edmrg _ _ _ _ _ _ _ (elab_value_weaken henv2 hv2 _)
              (elab_value_weaken he2 hv1 _)) hbody)
  | ssnmrgl hρs h1 ih =>
    intro ρc Γ A r hnv henv hr
    have hρc := elab_value henv hρs
    have E := Core.Value.vmrg hρc hρc
    cases hr with
    | val hv _ => exact absurd hv hnv
    | nmrg1 hnv1 hr1 he2 =>
      exact simstep_lift (fun x => .proj (.mrg ρc (.mrg (.box ρc x) _)) 0) hρc
        (fun hs => Step.sproj hρc (Step.smrgr hρc hρc (Step.smrgl E (Step.sboxr E hρc hs))))
        (by simp [letbCount]) (ih (fun hv => value_no_step hv h1) henv hr1)
        (fun hr' => nmrg_ready hρc hr' he2 (fun _ => sim_init he2 hρs henv))
    | nmrg2 hv1 _ _ => exact absurd h1 (value_no_step hv1)
  | ssnmrgr hρs hv1 h2 ih =>
    intro ρc Γ A r hnv henv hr
    have hρc := elab_value henv hρs
    have E := Core.Value.vmrg hρc hρc
    cases hr with
    | val hv _ => exact absurd hv hnv
    | nmrg1 hnv1 _ _ => exact absurd hv1 hnv1
    | nmrg2 _ he1 hr2 =>
      have hc1 := elab_value he1 hv1
      exact simstep_lift (fun x => .proj (.mrg ρc (.mrg _ (.box ρc x))) 0) hρc
        (fun hs => Step.sproj hρc (Step.smrgr hρc hρc
          (Step.smrgr E hc1 (Step.sboxr (Core.Value.vmrg E hc1) hρc hs))))
        (by simp [letbCount]) (ih (fun hv => value_no_step hv h2) henv hr2)
        (fun hr' => sim_of_ready hρc (Ready.nmrg2 hv1 he1 hr'))
  | ssnmrgv hρs hv1 hv2 =>
    intro ρc Γ A r hnv henv hr
    have hρc := elab_value henv hρs
    have E := Core.Value.vmrg hρc hρc
    cases hr with
    | val hv _ => exact absurd hv hnv
    | nmrg1 hnv1 _ _ => exact absurd hv1 hnv1
    | nmrg2 _ he1 hr2 =>
      have hc1 := elab_value he1 hv1
      have he2 := ready_value hr2 hv2
      have hc2 := elab_value he2 hv2
      exact simstep_redex hρs henv
        ⟨_, Step.sproj hρc (Step.smrgr hρc hρc
            (Step.smrgr E hc1 (Step.sboxv (Core.Value.vmrg E hc1) hρc hc2))),
          mstep_one (Step.sprojv hρc (Core.Value.vmrg hρc (Core.Value.vmrg hc1 hc2))
            Core.LookupV.lvzero)⟩
        (elabExp.edmrg _ _ _ _ _ _ _ he1 (elab_value_weaken he2 hv2 _))
  | ssletbl hρs h1 ih =>
    intro ρc Γ A r hnv henv hr
    have hρc := elab_value henv hρs
    cases hr with
    | val hv _ => exact absurd hv hnv
    | letb hr1 he2 =>
      exact simstep_lift (fun x => .proj (.mrg x _) 0) hρc
        (fun hs => Step.sproj hρc (Step.smrgl hρc hs))
        (by simp [letbCount]) (ih (fun hv => value_no_step hv h1) henv hr1)
        (fun hr' => sim_of_ready hρc (Ready.letb hr' he2))
  | ssletbv hρs hv1 =>
    intro ρc Γ A r hnv henv hr
    have hρc := elab_value henv hρs
    cases hr with
    | val hv _ => exact absurd hv hnv
    | letb hr1 he2 =>
      have he1 := ready_value hr1 hv1
      have hc1 := elab_value he1 hv1
      obtain ⟨r2, hm, hr2⟩ := sim_init he2 (SCE.Value.vmrg hρs hv1) (env_ext henv hv1 he1)
      exact ⟨_, Or.inr ⟨MStep.refl hρc,
          by simp [letbCount, letbCount_value hρs, letbCount_value hv1]⟩,
        ⟨_, mstep_proj (mstep_mrg_right hρc hc1 hm), Ready.letres hv1 he1 hr2⟩⟩
  | ssmlinkl hρs h1 ih =>
    intro ρc Γ A r hnv henv hr
    have hρc := elab_value henv hρs
    cases hr with
    | val hv _ => exact absurd hv hnv
    | mlink1 hnv1 hr1 he2 hl =>
      exact simstep_lift (fun x => .app (.app (.clos ρc _ _) x) _) hρc
        (fun hs => Step.sappl hρc (Step.sappr hρc (Core.Value.vclos hρc) hs))
        (by simp [letbCount]) (ih (fun hv => value_no_step hv h1) henv hr1)
        (fun hr' => mlink_ready hρc hr' he2 hl (fun _ => sim_init he2 hρs henv))
    | mlink2 hv1 _ _ _ => exact absurd h1 (value_no_step hv1)
  | ssmlinkr hρs hv1 h2 ih =>
    intro ρc Γ A r hnv henv hr
    have hρc := elab_value henv hρs
    cases hr with
    | val hv _ => exact absurd hv hnv
    | mlink1 hnv1 _ _ _ => exact absurd hv1 hnv1
    | mlink2 _ he1 hr2 hl =>
      have hc1 := elab_value he1 hv1
      exact simstep_lift (fun x => .app (.clos (.mrg ρc _) _ _) x) hρc
        (fun hs => Step.sappr hρc (Core.Value.vclos (Core.Value.vmrg hρc hc1)) hs)
        (by simp [letbCount]) (ih (fun hv => value_no_step hv h2) henv hr2)
        (fun hr' => sim_of_ready hρc (Ready.mlink2 hv1 he1 hr' hl))
  | @ssmlinkbeta _ _ _ _ A0 _ l0 hρs hv1 hv2 hsel =>
    intro ρc Γ A r hnv henv hr
    have hρc := elab_value henv hρs
    cases hr with
    | val hv _ => exact absurd hv hnv
    | mlink1 hnv1 _ _ _ => exact absurd hv1 hnv1
    | mlink2 _ he1 hr2 hl =>
      have he2 := ready_value hr2 (SCE.Value.vmclos hv2)
      cases he2 with
      | mclos _ _ _ _ _ _ cv2 cb _ henv2 hbody =>
        have hc1 := elab_value he1 hv1
        have hcv2 := elab_value henv2 hv2
        have hcf := Core.Value.vclos (A := elabTyp (.rcd l0 A0)) (e := cb) hcv2
        obtain ⟨vcl, hrlv, helab_vl⟩ :=
          sel_preservation hv1 (elab_value_weaken he1 hv1 .top) hsel hl
        have hvl := source_sel_value hv1 hsel
        have hcvl := elab_value helab_vl hvl
        have hE1 := Core.Value.vmrg (Core.Value.vmrg hρc hc1) hcf
        have hE2 := Core.Value.vmrg hE1 hc1
        have hw := ebig_sound (wire_eval_rcd (A := elabTyp A0) hρc hc1 hcf hrlv)
        have hcpkg := Core.Value.vrcd (l := l0) hcvl
        have hW := Core.Value.vmrg hcv2 hcpkg
        have henvb := env_ext henv2 (SCE.Value.vlrec hvl)
          (elab_value_weaken (elabExp.elrec _ _ _ _ l0 helab_vl) (SCE.Value.vlrec hvl) _)
        obtain ⟨rb, hmb, hrb⟩ := sim_init hbody (SCE.Value.vmrg hv2 (SCE.Value.vlrec hvl)) henvb
        refine ⟨_, Or.inl ⟨_, Step.sbeta hρc hcf (Core.Value.vmrg hρc hc1), ?_⟩,
          ⟨_, mstep_box_right hρc hE1 (mstep_mrg_right hE1 hc1 (mstep_box_right hE2 hW hmb)),
            Ready.linkres hv1 he1 hE1 (fun h => nomatch h)
              (Ready.box2 (SCE.Value.vmrg hv2 (SCE.Value.vlrec hvl)) henvb hrb)
              (Or.inr ⟨_, _, rfl, hW⟩)⟩⟩
        refine MStep.step (Step.sboxr hρc hE1 (Step.smrgl hE1 (Step.sproj hE1 (Step.squery hE1)))) ?_
        refine MStep.step (Step.sboxr hρc hE1 (Step.smrgl hE1
          (Step.sprojv hE1 hE1 (Core.LookupV.lvsucc Core.LookupV.lvzero)))) ?_
        refine MStep.step (Step.sboxr hρc hE1 (Step.smrgr hE1 hc1
          (Step.sappl hE2 (Step.sproj hE2 (Step.squery hE2))))) ?_
        refine MStep.step (Step.sboxr hρc hE1 (Step.smrgr hE1 hc1
          (Step.sappl hE2 (Step.sprojv hE2 hE2 (Core.LookupV.lvsucc Core.LookupV.lvzero))))) ?_
        refine mstep_trans (mstep_box_right hρc hE1 (mstep_mrg_right hE1 hc1
          (mstep_app_right hcf hw))) ?_
        exact mstep_one (Step.sboxr hρc hE1 (Step.smrgr hE1 hc1 (Step.sbeta hE2 hcpkg hcv2)))
  | ssopenml hρs h1 ih =>
    intro ρc Γ A r hnv henv hr
    have hρc := elab_value henv hρs
    cases hr with
    | val hv _ => exact absurd hv hnv
    | openm hr1 he2 =>
      exact simstep_lift (fun x => .app (.clos ρc _ _) (.rproj x _)) hρc
        (fun hs => Step.sappr hρc (Core.Value.vclos hρc) (Step.srproj hρc hs))
        (by simp [letbCount]) (ih (fun hv => value_no_step hv h1) henv hr1)
        (fun hr' => sim_of_ready hρc (Ready.openm hr' he2))
  | ssopenm hρs hv' =>
    intro ρc Γ A r hnv henv hr
    have hρc := elab_value henv hρs
    cases hr with
    | val hv _ => exact absurd hv hnv
    | openm hr1 he2 =>
      have he1 := ready_value hr1 (SCE.Value.vlrec hv')
      cases he1 with
      | elrec _ _ _ _ _ hcv =>
        have hc' := elab_value hcv hv'
        exact simstep_redex hρs henv
          ⟨_, Step.sappr hρc (Core.Value.vclos hρc)
              (Step.srprojv hρc (Core.Value.vrcd hc') Core.RLookupV.rvlzero),
            mstep_one (Step.sbeta hρc hc' hρc)⟩
          (elabExp.ebox _ _ _ _ _ _ _
            (elabExp.edmrg _ _ _ _ _ _ _ (elab_value_weaken henv hρs _)
              (elab_value_weaken hcv hv' _)) he2)
  | ssinl hρs h1 ih =>
    intro ρc Γ A r hnv henv hr
    have hρc := elab_value henv hρs
    cases hr with
    | val hv _ => exact absurd hv hnv
    | inl hr1 =>
      exact simstep_lift (fun x => .inl _ x) hρc (fun hs => Step.sinl hρc hs)
        (by simp [letbCount]) (ih (fun hv => value_no_step hv h1) henv hr1)
        (fun hr' => sim_of_ready hρc (Ready.inl hr'))
  | ssinr hρs h1 ih =>
    intro ρc Γ A r hnv henv hr
    have hρc := elab_value henv hρs
    cases hr with
    | val hv _ => exact absurd hv hnv
    | inr hr1 =>
      exact simstep_lift (fun x => .inr _ x) hρc (fun hs => Step.sinr hρc hs)
        (by simp [letbCount]) (ih (fun hv => value_no_step hv h1) henv hr1)
        (fun hr' => sim_of_ready hρc (Ready.inr hr'))
  | sscase hρs h1 ih =>
    intro ρc Γ A r hnv henv hr
    have hρc := elab_value henv hρs
    cases hr with
    | val hv _ => exact absurd hv hnv
    | case hr1 h1' h2' =>
      exact simstep_lift (fun x => .case x _ _) hρc (fun hs => Step.scase hρc hs)
        (by simp [letbCount]) (ih (fun hv => value_no_step hv h1) henv hr1)
        (fun hr' => sim_of_ready hρc (Ready.case hr' h1' h2'))
  | sscasel hρs hv1 =>
    intro ρc Γ A r hnv henv hr
    have hρc := elab_value henv hρs
    cases hr with
    | val hv _ => exact absurd hv hnv
    | case hr1 h1' _ =>
      have he := ready_value hr1 (SCE.Value.vinl hv1)
      cases he with
      | einl _ _ _ _ _ hcv =>
        exact simstep_redex1 hρs henv (Step.scasel hρc (elab_value hcv hv1))
          (elabExp.ebox _ _ _ _ _ _ _
            (elabExp.edmrg _ _ _ _ _ _ _ (elab_value_weaken henv hρs _)
              (elab_value_weaken hcv hv1 _)) h1')
  | sscaser hρs hv1 =>
    intro ρc Γ A r hnv henv hr
    have hρc := elab_value henv hρs
    cases hr with
    | val hv _ => exact absurd hv hnv
    | case hr1 _ h2' =>
      have he := ready_value hr1 (SCE.Value.vinr hv1)
      cases he with
      | einr _ _ _ _ _ hcv =>
        exact simstep_redex1 hρs henv (Step.scaser hρc (elab_value hcv hv1))
          (elabExp.ebox _ _ _ _ _ _ _
            (elabExp.edmrg _ _ _ _ _ _ _ (elab_value_weaken henv hρs _)
              (elab_value_weaken hcv hv1 _)) h2')
  | ssfclos hρs =>
    intro ρc Γ A r hnv henv hr
    have hρc := elab_value henv hρs
    cases hr with
    | val hv _ => exact absurd hv hnv
    | flam h =>
      exact simstep_redex1 hρs henv (Step.sfclos hρc)
        (elabExp.efclos _ _ _ _ _ _ _ _ hρs henv h)
  | ssfbeta hρs hv1 hv2 =>
    intro ρc Γ A r hnv henv hr
    have hρc := elab_value henv hρs
    cases hr with
    | val hv _ => exact absurd hv hnv
    | app1 hnv1 _ _ => exact absurd (SCE.Value.vfclos hv2) hnv1
    | app2 _ he1 hr2 =>
      have he2 := ready_value hr2 hv1
      cases he1 with
      | efclos _ _ _ _ _ _ _ _ _ henv2 hbody =>
        exact simstep_redex1 hρs henv
          (Step.sfbeta hρc (elab_value he2 hv1) (elab_value henv2 hv2))
          (elabExp.ebox _ _ _ _ _ _ _
            (elabExp.edmrg _ _ _ _ _ _ _
              (elabExp.edmrg _ _ _ _ _ _ _ (elab_value_weaken henv2 hv2 _)
                (elabExp.efclos _ _ _ _ _ _ _ _ hv2 henv2 hbody))
              (elab_value_weaken he2 hv1 _)) hbody)
  | ssfold hρs h1 ih =>
    intro ρc Γ A r hnv henv hr
    have hρc := elab_value henv hρs
    cases hr with
    | val hv _ => exact absurd hv hnv
    | fold hr1 =>
      exact simstep_lift (fun x => .fold _ x) hρc (fun hs => Step.sfold hρc hs)
        (by simp [letbCount]) (ih (fun hv => value_no_step hv h1) henv hr1)
        (fun hr' => sim_of_ready hρc (Ready.fold hr'))
  | ssunfold hρs h1 ih =>
    intro ρc Γ A r hnv henv hr
    have hρc := elab_value henv hρs
    cases hr with
    | val hv _ => exact absurd hv hnv
    | unfold hr1 heq =>
      exact simstep_lift (fun x => .unfold x) hρc (fun hs => Step.sunfold hρc hs)
        (by simp [letbCount]) (ih (fun hv => value_no_step hv h1) henv hr1)
        (fun hr' => sim_of_ready hρc (Ready.unfold hr' heq))
  | ssunfoldv hρs hv1 =>
    intro ρc Γ A r hnv henv hr
    have hρc := elab_value henv hρs
    cases hr with
    | val hv _ => exact absurd hv hnv
    | unfold hr1 heq =>
      have he := ready_value hr1 (SCE.Value.vfold hv1)
      cases he with
      | efold _ _ _ _ hcv =>
        subst heq
        exact simstep_redex1 hρs henv (Step.sunfoldv hρc (elab_value hcv hv1)) hcv
  | ssmlinknl hρs h1 ih =>
    intro ρc Γ A r hnv henv hr
    have hρc := elab_value henv hρs
    cases hr with
    | val hv _ => exact absurd hv hnv
    | mlinkn1 hnv1 hr1 he2 hok =>
      exact simstep_lift (fun x => .app (.app (.clos ρc _ _) x) _) hρc
        (fun hs => Step.sappl hρc (Step.sappr hρc (Core.Value.vclos hρc) hs))
        (by simp [letbCount]) (ih (fun hv => value_no_step hv h1) henv hr1)
        (fun hr' => mlinkn_ready hρc hr' he2 hok (fun _ => sim_init he2 hρs henv))
    | mlinkn2 hv1 _ _ _ => exact absurd h1 (value_no_step hv1)
  | ssmlinknr hρs hv1 h2 ih =>
    intro ρc Γ A r hnv henv hr
    have hρc := elab_value henv hρs
    cases hr with
    | val hv _ => exact absurd hv hnv
    | mlinkn1 hnv1 _ _ _ => exact absurd hv1 hnv1
    | mlinkn2 _ he1 hr2 hok =>
      have hc1 := elab_value he1 hv1
      exact simstep_lift (fun x => .app (.clos (.mrg ρc _) _ _) x) hρc
        (fun hs => Step.sappr hρc (Core.Value.vclos (Core.Value.vmrg hρc hc1)) hs)
        (by simp [letbCount]) (ih (fun hv => value_no_step hv h2) henv hr2)
        (fun hr' => sim_of_ready hρc (Ready.mlinkn2 hv1 he1 hr' hok))
  | @ssmlinknbeta _ _ _ _ D0 _ hρs hv1 hv2 hsp =>
    intro ρc Γ A r hnv henv hr
    have hρc := elab_value henv hρs
    cases hr with
    | val hv _ => exact absurd hv hnv
    | mlinkn1 hnv1 _ _ _ => exact absurd hv1 hnv1
    | mlinkn2 _ he1 hr2 hok =>
      have he2 := ready_value hr2 (SCE.Value.vmclos hv2)
      cases he2 with
      | mclos _ _ _ _ _ _ cv2 cb _ henv2 hbody =>
        have hc1 := elab_value he1 hv1
        have hcv2 := elab_value henv2 hv2
        have hcf := Core.Value.vclos (A := elabTyp D0) (e := cb) hcv2
        have hE1 := Core.Value.vmrg (Core.Value.vmrg hρc hc1) hcf
        have hE2 := Core.Value.vmrg hE1 hc1
        obtain ⟨cpkg, hbigw, helab_pkg⟩ :=
          wire_eval hok hsp hv1 (elab_value_weaken he1 hv1 .top) hE2 Core.LookupV.lvzero
        have hvpkg := S_Sem.selpkg_value hsp hv1
        have hcpkg := elab_value helab_pkg hvpkg
        have hw := ebig_sound hbigw
        have hW := Core.Value.vmrg hcv2 hcpkg
        have henvb := env_ext henv2 hvpkg (elab_value_weaken helab_pkg hvpkg _)
        obtain ⟨rb, hmb, hrb⟩ := sim_init hbody (SCE.Value.vmrg hv2 hvpkg) henvb
        refine ⟨_, Or.inl ⟨_, Step.sbeta hρc hcf (Core.Value.vmrg hρc hc1), ?_⟩,
          ⟨_, mstep_box_right hρc hE1 (mstep_mrg_right hE1 hc1 (mstep_box_right hE2 hW hmb)),
            Ready.linkres hv1 he1 hE1 (fun h => nomatch h)
              (Ready.box2 (SCE.Value.vmrg hv2 hvpkg) henvb hrb)
              (Or.inr ⟨_, _, rfl, hW⟩)⟩⟩
        refine MStep.step (Step.sboxr hρc hE1 (Step.smrgl hE1 (Step.sproj hE1 (Step.squery hE1)))) ?_
        refine MStep.step (Step.sboxr hρc hE1 (Step.smrgl hE1
          (Step.sprojv hE1 hE1 (Core.LookupV.lvsucc Core.LookupV.lvzero)))) ?_
        refine MStep.step (Step.sboxr hρc hE1 (Step.smrgr hE1 hc1
          (Step.sappl hE2 (Step.sproj hE2 (Step.squery hE2))))) ?_
        refine MStep.step (Step.sboxr hρc hE1 (Step.smrgr hE1 hc1
          (Step.sappl hE2 (Step.sprojv hE2 hE2 (Core.LookupV.lvsucc Core.LookupV.lvzero))))) ?_
        refine mstep_trans (mstep_box_right hρc hE1 (mstep_mrg_right hE1 hc1
          (mstep_app_right hcf hw))) ?_
        exact mstep_one (Step.sboxr hρc hE1 (Step.smrgr hE1 hc1 (Step.sbeta hE2 hcpkg hcv2)))

/-! ## Forward simulation -/

/-- **Forward simulation (star with measure).**  If the source takes a small
step, a `Sim`-related Core term takes one or more steps, or zero or more steps
while the stutter measure strictly decreases, to a term related to the source
reduct. -/
theorem elab_forward_simulation
    {ρs : SCE.Exp} {ρc : Core.Exp} {Γ A : SCE.Typ} {es es' : SCE.Exp} {ec : Core.Exp}
    (henv : elabExp .top ρs Γ ρc)
    (hstep : SStep ρs es es')
    (hsim : Sim ρs ρc Γ es A ec)
    : ∃ ec', (CPlus ρc ec ec' ∨ (MStep ρc ec ec' ∧ letbCount es' < letbCount es))
             ∧ Sim ρs ρc Γ es' A ec' := by
  obtain ⟨r, hm, hr⟩ := hsim
  obtain ⟨c, hpr, hs⟩ := sim_step_ready hstep (fun hv => value_no_step hv hstep) henv hr
  refine ⟨c, ?_, hs⟩
  rcases hpr with hp | ⟨hm', hlt⟩
  · exact Or.inl (mstep_cplus_trans hm hp)
  · exact Or.inr ⟨mstep_trans hm hm', hlt⟩

/-- An elaboration is related to its source term. -/
theorem elab_sim {ρs ρc Γ es A ec}
    (helab : elabExp Γ es A ec) (hρs : SCE.Value ρs) (henv : elabExp .top ρs Γ ρc) :
    Sim ρs ρc Γ es A ec :=
  sim_init helab hρs henv

/-- At a source value, the related Core term reaches the elaboration of it. -/
theorem sim_final {ρs ρc Γ v A ec} (hsim : Sim ρs ρc Γ v A ec) (hv : SCE.Value v) :
    ∃ vc, MStep ρc ec vc ∧ Core.Value vc ∧ elabExp Γ v A vc := by
  obtain ⟨r, hm, hr⟩ := hsim
  have he := ready_value hr hv
  exact ⟨r, hm, elab_value he hv, he⟩
