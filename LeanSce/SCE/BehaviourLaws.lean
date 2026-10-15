import LeanSce.SCE.Divergence
import LeanSce.SCE.LinkingLaws
import LeanSce.SCE.UnitChains
import LeanSce.SCE.Confinement

/-!
# Behaviour versions of the termination-only results

Whole-program correctness, unit chains, interface abstraction and confinement
were first stated for terminating runs.  This file adds their divergence
counterparts.

* For whole programs and unit chains, `elab_behaviour_equiv` applies directly.
* For interface abstraction, a well-typed term diverges iff it does not
  terminate (`sdiverges_iff_not_terminates`, from source type safety and Core
  determinism), so divergence equivalence follows from the existing
  termination equivalence.
* For confinement, the ambient environment need not be typed, so we argue on
  the small-step relation: the two runs make the same deterministic initial
  steps and then run the same body under the same (sandboxed) environment.
-/

open SCE S_Sem

/-! ## General helpers -/

/-- For a well-typed source term under a well-typed value environment,
divergence is exactly non-termination. -/
theorem sdiverges_iff_not_terminates
    {Γ A : SCE.Typ} {es ρs : SCE.Exp} {ec ρc : Core.Exp}
    (helab : elabExp Γ es A ec)
    (henv : elabExp SCE.Typ.top ρs Γ ρc)
    (henv_val : SCE.Value ρs) :
    SDiverges ρs es ↔ ¬ ∃ vs, BStep ρs es vs := by
  constructor
  · rintro hdiv ⟨vs, hb⟩
    obtain ⟨ht, hρ⟩ := core_typed_of_elab helab henv
    obtain ⟨vc, hbig, _⟩ := semantic_preservation helab hb henv henv_val
    exact core_diverges_not_terminates ht hρ
      (elab_preserves_divergence helab henv henv_val hdiv)
      (ebig_sound hbig) (ebig_produces_value (elab_value henv henv_val) hbig)
  · intro hnt
    rcases source_terminates_or_diverges helab henv henv_val with h | h
    · exact absurd h hnt
    · exact h

/-- A step that is the only step available does not change divergence. -/
theorem sdiverges_step_iff {ρ e e' : SCE.Exp} (hs : SStep ρ e e')
    (huniq : ∀ e'', SStep ρ e e'' → e'' = e') :
    SDiverges ρ e ↔ SDiverges ρ e' := by
  constructor
  · rintro ⟨f, hf0, hf⟩
    exact ⟨fun n => f (n + 1), huniq _ (hf0 ▸ hf 0), fun n => hf (n + 1)⟩
  · rintro ⟨f, hf0, hf⟩
    refine ⟨fun n => match n with | 0 => e | m + 1 => f m, rfl, ?_⟩
    intro n
    cases n with
    | zero => show SStep ρ e (f 0); rw [hf0]; exact hs
    | succ m => exact hf m

/-- Divergence through an evaluation frame `W` whose steps under `ρ` are exactly
the steps of the hole under `ρ'`, except for steps to a normal form. -/
theorem sdiverges_frame {ρ ρ' : SCE.Exp} (W : SCE.Exp → SCE.Exp)
    (hfwd : ∀ x x', SStep ρ' x x' → SStep ρ (W x) (W x'))
    (hinv : ∀ x y, SStep ρ (W x) y →
      (∃ x', y = W x' ∧ SStep ρ' x x') ∨ ∀ z, ¬ SStep ρ y z)
    {e : SCE.Exp} :
    SDiverges ρ (W e) ↔ SDiverges ρ' e := by
  constructor
  · intro hdiv
    refine infinite_chain (SStep ρ') (fun x => SDiverges ρ (W x)) ?_ hdiv
    rintro x ⟨f, hf0, hf⟩
    rcases hinv x (f 1) (hf0 ▸ hf 0) with ⟨x', hx', hs⟩ | hstuck
    · exact ⟨x', hs, fun n => f (n + 1), hx', fun n => hf (n + 1)⟩
    · exact (hstuck _ (hf 1)).elim
  · rintro ⟨f, hf0, hf⟩
    exact ⟨fun n => W (f n), hf0 ▸ rfl, fun n => hfwd _ _ (hf n)⟩

/-- A `box` with a value environment ignores the ambient environment. -/
theorem sdiverges_box_iff {ρ v e : SCE.Exp} (hρ : SCE.Value ρ) (hv : SCE.Value v) :
    SDiverges ρ (.box v e) ↔ SDiverges v e :=
  sdiverges_frame (Exp.box v) (fun _ _ hs => SStep.ssboxr hρ hv hs)
    (fun x y hs => by
      cases hs with
      | ssboxl _ h => exact (value_no_step hv h).elim
      | ssboxr _ _ h => exact Or.inl ⟨_, rfl, h⟩
      | ssboxv _ _ hy => exact Or.inr fun _ h => value_no_step hy h)

/-- The right component of a merge with a value on the left runs under the
extended environment. -/
theorem sdiverges_mrg_right_iff {ρ p e : SCE.Exp} (hρ : SCE.Value ρ) (hp : SCE.Value p) :
    SDiverges ρ (.mrg p e) ↔ SDiverges (.mrg ρ p) e :=
  sdiverges_frame (Exp.mrg p) (fun _ _ hs => SStep.ssmrgr hρ hp hs)
    (fun x y hs => by
      cases hs with
      | ssmrgl _ h => exact (value_no_step hp h).elim
      | ssmrgr _ _ h => exact Or.inl ⟨_, rfl, h⟩)

/-- Unique selection for a well-typed package (public copy of the private
`selpkg_deterministic` of `SCE.Semantics.Determinism`). -/
theorem selpkg_unique
    {Γ₁ D : SCE.Typ} (hok : LinkOk Γ₁ D)
    {v : SCE.Exp} {vc : Core.Exp}
    (hval : SCE.Value v)
    (helab : elabExp SCE.Typ.top v Γ₁ vc)
    : ∀ {pkg₁ pkg₂ : SCE.Exp}, SelPkg v D pkg₁ → SelPkg v D pkg₂ → pkg₁ = pkg₂ := by
  induction hok with
  | one hrl =>
    intro pkg₁ pkg₂ hsp₁ hsp₂
    cases hsp₁ with | one hsel₁ =>
    cases hsp₂ with | one hsel₂ =>
    rw [sel_deterministic hval helab hrl hsel₁ hsel₂]
  | more hok' hrl ih =>
    intro pkg₁ pkg₂ hsp₁ hsp₂
    cases hsp₁ with | more hsp₁' hsel₁ =>
    cases hsp₂ with | more hsp₂' hsel₂ =>
    rw [ih hsp₁' hsp₂', sel_deterministic hval helab hrl hsel₁ hsel₂]

/-! ## 1. Whole programs -/

/-- **Whole-program correctness, behaviour.**  A closed program and its
elaboration have the same behaviour: same results, and divergence iff
divergence. -/
theorem whole_program_behaviour
    {A : SCE.Typ} {es : SCE.Exp} {ec : Core.Exp}
    (helab : elabExp SCE.Typ.top es A ec)
    : SameBehaviour A .unit es .unit ec :=
  elab_behaviour_equiv helab (elabExp.eunit SCE.Typ.top) SCE.Value.vunit

/-! ## 2. Unit chains -/

/-- **Unit chains, behaviour.** -/
theorem unit_chain_behaviour
    {n : Nat} {S : SCE.Exp} {I : SCE.Typ} {L : Core.Exp}
    (hchain : UnitChain n S I L) : SameBehaviour I .unit S .unit L :=
  whole_program_behaviour (unit_chain_elaboration hchain)

/-- **Multi-import unit chains, behaviour.** -/
theorem unit_chain_n_behaviour
    {n : Nat} {S : SCE.Exp} {I : SCE.Typ} {L : Core.Exp}
    (hchain : UnitChainN n S I L) : SameBehaviour I .unit S .unit L :=
  whole_program_behaviour (unit_chain_n_elaboration hchain)

/-! ## 3. Interface abstraction -/

namespace S_Sem

/-- **Interface abstraction, divergence.**  Under the hypotheses of
`interface_abstraction`, the client linked against either provider diverges
iff it diverges against the other. -/
theorem interface_abstraction_diverges
    {Γ A B P₁ P₂ : Typ} {l : String} {ρ e p₁ p₂ vl : Exp}
    {ec ρc pc₁ pc₂ : Core.Exp}
    (he : elabExp Γ e (.marr (.rcd l A) B) ec)
    (hρ : elabExp Typ.top ρ Γ ρc) (hρv : Value ρ)
    (hp₁v : Value p₁) (hp₂v : Value p₂)
    (hp₁ : elabExp Typ.top p₁ P₁ pc₁) (hp₂ : elabExp Typ.top p₂ P₂ pc₂)
    (hl₁ : SRLookup P₁ l A) (hl₂ : SRLookup P₂ l A)
    (hs₁ : Sel p₁ l vl) (hs₂ : Sel p₂ l vl)
    : SDiverges ρ (.mlink p₁ e) ↔ SDiverges ρ (.mlink p₂ e) := by
  have ht₁ := elabExp.mlink _ _ _ _ _ _ _ _ _ (elab_value_weaken hp₁ hp₁v Γ) he hl₁
  have ht₂ := elabExp.mlink _ _ _ _ _ _ _ _ _ (elab_value_weaken hp₂ hp₂v Γ) he hl₂
  rw [sdiverges_iff_not_terminates ht₁ hρ hρv, sdiverges_iff_not_terminates ht₂ hρ hρv]
  have hia := fun w =>
    interface_abstraction (w := w) he hρ hρv hp₁v hp₂v hp₁ hp₂ hl₁ hl₂ hs₁ hs₂
  refine not_congr ⟨?_, ?_⟩
  · rintro ⟨v, hb⟩
    cases hb with
    | mlink hρ' hP hC hsel hbody =>
      cases sbig_value_eq hP hp₁v
      exact ⟨_, (hia _).mp (BStep.mlink hρ' hP hC hsel hbody)⟩
  · rintro ⟨v, hb⟩
    cases hb with
    | mlink hρ' hP hC hsel hbody =>
      cases sbig_value_eq hP hp₂v
      exact ⟨_, (hia _).mpr (BStep.mlink hρ' hP hC hsel hbody)⟩

/-- **Interface abstraction, behaviour.**  The same exports on termination, and
divergence iff divergence. -/
theorem interface_abstraction_behaviour
    {Γ A B P₁ P₂ : Typ} {l : String} {ρ e p₁ p₂ vl : Exp}
    {ec ρc pc₁ pc₂ : Core.Exp}
    (he : elabExp Γ e (.marr (.rcd l A) B) ec)
    (hρ : elabExp Typ.top ρ Γ ρc) (hρv : Value ρ)
    (hp₁v : Value p₁) (hp₂v : Value p₂)
    (hp₁ : elabExp Typ.top p₁ P₁ pc₁) (hp₂ : elabExp Typ.top p₂ P₂ pc₂)
    (hl₁ : SRLookup P₁ l A) (hl₂ : SRLookup P₂ l A)
    (hs₁ : Sel p₁ l vl) (hs₂ : Sel p₂ l vl)
    : (∀ w, BStep ρ (.mlink p₁ e) (.mrg p₁ w) ↔ BStep ρ (.mlink p₂ e) (.mrg p₂ w))
      ∧ (SDiverges ρ (.mlink p₁ e) ↔ SDiverges ρ (.mlink p₂ e)) :=
  ⟨fun _ => interface_abstraction he hρ hρv hp₁v hp₂v hp₁ hp₂ hl₁ hl₂ hs₁ hs₂,
   interface_abstraction_diverges he hρ hρv hp₁v hp₂v hp₁ hp₂ hl₁ hl₂ hs₁ hs₂⟩

/-- One direction of `interface_abstraction_n`. -/
private theorem interface_abstraction_n_dir
    {Γ D B P₁ : Typ} {ρ e p₁ p₂ pkg w : Exp}
    {ec ρc pc₁ : Core.Exp}
    (he : elabExp Γ e (.marr D B) ec)
    (hρ : elabExp Typ.top ρ Γ ρc) (hρv : Value ρ)
    (hp₁v : Value p₁) (hp₂v : Value p₂)
    (hp₁ : elabExp Typ.top p₁ P₁ pc₁)
    (hok₁ : LinkOk P₁ D)
    (hs₁ : SelPkg p₁ D pkg) (hs₂ : SelPkg p₂ D pkg)
    (h : BStep ρ (.mlinkn p₁ e) (.mrg p₁ w))
    : BStep ρ (.mlinkn p₂ e) (.mrg p₂ w) := by
  cases h with
  | mlinkn hρ' _ hC hsp hbody =>
    obtain ⟨_, _, hclos⟩ := semantic_preservation he hC hρ hρv
    cases hclos
    cases selpkg_unique hok₁ hp₁v hp₁ hs₁ hsp
    exact BStep.mlinkn hρ' (sbig_value_refl hp₂v hρv) hC hs₂ hbody

/-- **Interface abstraction (n-ary `linkall`).**  Two well-typed provider values
that select the same package at the client's import interface `D` drive the
client to the same exports. -/
theorem interface_abstraction_n
    {Γ D B P₁ P₂ : Typ} {ρ e p₁ p₂ pkg w : Exp}
    {ec ρc pc₁ pc₂ : Core.Exp}
    (he : elabExp Γ e (.marr D B) ec)
    (hρ : elabExp Typ.top ρ Γ ρc) (hρv : Value ρ)
    (hp₁v : Value p₁) (hp₂v : Value p₂)
    (hp₁ : elabExp Typ.top p₁ P₁ pc₁) (hp₂ : elabExp Typ.top p₂ P₂ pc₂)
    (hok₁ : LinkOk P₁ D) (hok₂ : LinkOk P₂ D)
    (hs₁ : SelPkg p₁ D pkg) (hs₂ : SelPkg p₂ D pkg)
    : BStep ρ (.mlinkn p₁ e) (.mrg p₁ w) ↔ BStep ρ (.mlinkn p₂ e) (.mrg p₂ w) :=
  ⟨interface_abstraction_n_dir he hρ hρv hp₁v hp₂v hp₁ hok₁ hs₁ hs₂,
   interface_abstraction_n_dir he hρ hρv hp₂v hp₁v hp₂ hok₂ hs₂ hs₁⟩

/-- **Interface abstraction (n-ary `linkall`), divergence.** -/
theorem interface_abstraction_n_diverges
    {Γ D B P₁ P₂ : Typ} {ρ e p₁ p₂ pkg : Exp}
    {ec ρc pc₁ pc₂ : Core.Exp}
    (he : elabExp Γ e (.marr D B) ec)
    (hρ : elabExp Typ.top ρ Γ ρc) (hρv : Value ρ)
    (hp₁v : Value p₁) (hp₂v : Value p₂)
    (hp₁ : elabExp Typ.top p₁ P₁ pc₁) (hp₂ : elabExp Typ.top p₂ P₂ pc₂)
    (hok₁ : LinkOk P₁ D) (hok₂ : LinkOk P₂ D)
    (hs₁ : SelPkg p₁ D pkg) (hs₂ : SelPkg p₂ D pkg)
    : SDiverges ρ (.mlinkn p₁ e) ↔ SDiverges ρ (.mlinkn p₂ e) := by
  have ht₁ := elabExp.mlinkn _ _ _ _ _ _ _ _ (elab_value_weaken hp₁ hp₁v Γ) he hok₁
  have ht₂ := elabExp.mlinkn _ _ _ _ _ _ _ _ (elab_value_weaken hp₂ hp₂v Γ) he hok₂
  rw [sdiverges_iff_not_terminates ht₁ hρ hρv, sdiverges_iff_not_terminates ht₂ hρ hρv]
  have hia := fun w =>
    interface_abstraction_n (w := w) he hρ hρv hp₁v hp₂v hp₁ hp₂ hok₁ hok₂ hs₁ hs₂
  refine not_congr ⟨?_, ?_⟩
  · rintro ⟨v, hb⟩
    cases hb with
    | mlinkn hρ' hP hC hsp hbody =>
      cases sbig_value_eq hP hp₁v
      exact ⟨_, (hia _).mp (BStep.mlinkn hρ' hP hC hsp hbody)⟩
  · rintro ⟨v, hb⟩
    cases hb with
    | mlinkn hρ' hP hC hsp hbody =>
      cases sbig_value_eq hP hp₂v
      exact ⟨_, (hia _).mpr (BStep.mlinkn hρ' hP hC hsp hbody)⟩

/-- **Interface abstraction (n-ary `linkall`), behaviour.** -/
theorem interface_abstraction_n_behaviour
    {Γ D B P₁ P₂ : Typ} {ρ e p₁ p₂ pkg : Exp}
    {ec ρc pc₁ pc₂ : Core.Exp}
    (he : elabExp Γ e (.marr D B) ec)
    (hρ : elabExp Typ.top ρ Γ ρc) (hρv : Value ρ)
    (hp₁v : Value p₁) (hp₂v : Value p₂)
    (hp₁ : elabExp Typ.top p₁ P₁ pc₁) (hp₂ : elabExp Typ.top p₂ P₂ pc₂)
    (hok₁ : LinkOk P₁ D) (hok₂ : LinkOk P₂ D)
    (hs₁ : SelPkg p₁ D pkg) (hs₂ : SelPkg p₂ D pkg)
    : (∀ w, BStep ρ (.mlinkn p₁ e) (.mrg p₁ w) ↔ BStep ρ (.mlinkn p₂ e) (.mrg p₂ w))
      ∧ (SDiverges ρ (.mlinkn p₁ e) ↔ SDiverges ρ (.mlinkn p₂ e)) :=
  ⟨fun _ => interface_abstraction_n he hρ hρv hp₁v hp₂v hp₁ hp₂ hok₁ hok₂ hs₁ hs₂,
   interface_abstraction_n_diverges he hρ hρv hp₁v hp₂v hp₁ hp₂ hok₁ hok₂ hs₁ hs₂⟩

end S_Sem

/-! ## 4. Confinement -/

/-- A sandboxed functor applied to a value diverges exactly when its body
diverges under `ε ; varg`, whatever the ambient value environment. -/
theorem sandboxed_functor_app_diverges_iff
    {A : Typ} {body varg ρ : Exp} (hρ : Value ρ) (hvarg : Value varg) :
    SDiverges ρ (.mapp (.mfunctor .sandboxed A body) varg)
      ↔ SDiverges (.mrg .unit varg) body := by
  have hclos : Value (.mclos .unit A body) := Value.vmclos Value.vunit
  rw [sdiverges_step_iff (SStep.ssmappl hρ (SStep.ssmfunctor_sandboxed hρ)) (by
        intro e'' hs
        cases hs with
        | ssmappl _ h => cases h; rfl
        | ssmappr _ hv _ => cases hv),
      sdiverges_step_iff (SStep.ssmbeta hρ hvarg Value.vunit) (by
        intro e'' hs
        cases hs with
        | ssmappl _ h => exact (value_no_step hclos h).elim
        | ssmappr _ _ h => exact (value_no_step hvarg h).elim
        | ssmbeta => rfl),
      sdiverges_box_iff hρ (Value.vmrg Value.vunit hvarg)]

/-- **Sandboxed functor confinement, divergence.**  The application diverges
under one ambient value environment iff it diverges under any other. -/
theorem sandboxed_functor_confinement_diverges
    {A : Typ} {body varg ρ₁ ρ₂ : Exp}
    (hρ₁ : Value ρ₁) (hρ₂ : Value ρ₂) (hvarg : Value varg)
    : SDiverges ρ₁ (.mapp (.mfunctor .sandboxed A body) varg)
      ↔ SDiverges ρ₂ (.mapp (.mfunctor .sandboxed A body) varg) := by
  rw [sandboxed_functor_app_diverges_iff hρ₁ hvarg,
    sandboxed_functor_app_diverges_iff hρ₂ hvarg]

/-- A link of a provider value whose only `l` is `a` against an evaluated
sandboxed client diverges exactly when the client body diverges under
`ε ; {l = a}`. -/
theorem sandboxed_closure_link_diverges_iff
    {A : Typ} {l : String} {body a p ρ : Exp}
    (hρ : Value ρ) (hp : Value p) (hsel : Sel p l a)
    (himport : ∀ {v}, Sel p l v → v = a) :
    SDiverges ρ (.mlink p (.mclos .unit (.rcd l A) body))
      ↔ SDiverges (.mrg .unit (.lrec l a)) body := by
  have hclos : Value (.mclos .unit (.rcd l A) body) := Value.vmclos Value.vunit
  have ha : Value a := sel_value hsel hp
  rw [sdiverges_step_iff (SStep.ssmlinkbeta hρ hp Value.vunit hsel) (by
        intro e'' hs
        cases hs with
        | ssmlinkl _ h => exact (value_no_step hp h).elim
        | ssmlinkr _ _ h => exact (value_no_step hclos h).elim
        | ssmlinkbeta _ _ _ h => cases himport h; rfl),
      sdiverges_mrg_right_iff hρ hp,
      sdiverges_box_iff (Value.vmrg hρ hp) (Value.vmrg Value.vunit (Value.vlrec ha))]

/-- **Link confinement, divergence (evaluated clients).**  Two links whose
clients are the same sandboxed closure, and whose provider values supply the
same unique import `a`, diverge together, whatever the providers' other
contents and the ambient value environments. -/
theorem sandboxed_link_confinement_diverges
    {A : Typ} {l : String} {body a p₁ p₂ ρ₁ ρ₂ : Exp}
    (hρ₁ : Value ρ₁) (hρ₂ : Value ρ₂)
    (hp₁ : Value p₁) (hp₂ : Value p₂)
    (hsel₁ : Sel p₁ l a) (hsel₂ : Sel p₂ l a)
    (himport₁ : ∀ {v}, Sel p₁ l v → v = a)
    (himport₂ : ∀ {v}, Sel p₂ l v → v = a)
    : SDiverges ρ₁ (.mlink p₁ (.mclos .unit (.rcd l A) body))
      ↔ SDiverges ρ₂ (.mlink p₂ (.mclos .unit (.rcd l A) body)) := by
  rw [sandboxed_closure_link_diverges_iff hρ₁ hp₁ hsel₁ himport₁,
    sandboxed_closure_link_diverges_iff hρ₂ hp₂ hsel₂ himport₂]

/-- **Link confinement, divergence (literal sandboxed functors).** -/
theorem sandboxed_functor_link_confinement_diverges
    {A : Typ} {l : String} {body a p₁ p₂ ρ₁ ρ₂ : Exp}
    (hρ₁ : Value ρ₁) (hρ₂ : Value ρ₂)
    (hp₁ : Value p₁) (hp₂ : Value p₂)
    (hsel₁ : Sel p₁ l a) (hsel₂ : Sel p₂ l a)
    (himport₁ : ∀ {v}, Sel p₁ l v → v = a)
    (himport₂ : ∀ {v}, Sel p₂ l v → v = a)
    : SDiverges ρ₁ (.mlink p₁ (.mfunctor .sandboxed (.rcd l A) body))
      ↔ SDiverges ρ₂ (.mlink p₂ (.mfunctor .sandboxed (.rcd l A) body)) := by
  have step : ∀ {ρ p}, Value ρ → Value p →
      (SDiverges ρ (.mlink p (.mfunctor .sandboxed (.rcd l A) body))
        ↔ SDiverges ρ (.mlink p (.mclos .unit (.rcd l A) body))) := by
    intro ρ p hρ hp
    exact sdiverges_step_iff (SStep.ssmlinkr hρ hp (SStep.ssmfunctor_sandboxed hρ)) (by
      intro e'' hs
      cases hs with
      | ssmlinkl _ h => exact (value_no_step hp h).elim
      | ssmlinkr _ _ h => cases h; rfl)
  rw [step hρ₁ hp₁, step hρ₂ hp₂]
  exact sandboxed_link_confinement_diverges hρ₁ hρ₂ hp₁ hp₂ hsel₁ hsel₂ himport₁ himport₂

/-- **Link confinement, same behaviour** (the paper's restated Link Confinement).
    Provider values that each select the import `a` exactly once, linked with
    the same sandboxed client under arbitrary ambient environments, give the
    client the same exports, and one link diverges iff the other does. -/
theorem sandboxed_link_confinement_behaviour
    {A B : Typ} {l : String} {body a p₁ p₂ ρ₁ ρ₂ : Exp}
    {ec_body ec_a : Core.Exp}
    (ha : Value a)
    (hbody_elab : elabExp (Typ.and Typ.top (Typ.rcd l A)) body B ec_body)
    (ha_elab : elabExp Typ.top a A ec_a)
    (hρ₁ : Value ρ₁) (hρ₂ : Value ρ₂)
    (hp₁ : Value p₁) (hp₂ : Value p₂)
    (hsel₁ : Sel p₁ l a) (hsel₂ : Sel p₂ l a)
    (himport₁ : ∀ {v}, Sel p₁ l v → v = a)
    (himport₂ : ∀ {v}, Sel p₂ l v → v = a)
    : (∀ {w₁ w₂},
        BStep ρ₁ (.mlink p₁ (.mclos .unit (.rcd l A) body)) (.mrg p₁ w₁) →
        BStep ρ₂ (.mlink p₂ (.mclos .unit (.rcd l A) body)) (.mrg p₂ w₂) →
        w₁ = w₂)
      ∧ (SDiverges ρ₁ (.mlink p₁ (.mclos .unit (.rcd l A) body))
          ↔ SDiverges ρ₂ (.mlink p₂ (.mclos .unit (.rcd l A) body))) := by
  have hclos : Value (Exp.mclos Exp.unit (Typ.rcd l A) body) :=
    Value.vmclos Value.vunit
  refine ⟨fun h₁ h₂ => ?_,
    sandboxed_link_confinement_diverges hρ₁ hρ₂ hp₁ hp₂ hsel₁ hsel₂ himport₁ himport₂⟩
  exact sandboxed_link_confinement ha hbody_elab ha_elab
    (fun hc => (sbig_value_eq hc hclos).symm)
    (fun hc => (sbig_value_eq hc hclos).symm)
    (fun hp hs => by cases sbig_value_eq hp hp₁; exact himport₁ hs)
    (fun hp hs => by cases sbig_value_eq hp hp₂; exact himport₂ hs)
    h₁ h₂
