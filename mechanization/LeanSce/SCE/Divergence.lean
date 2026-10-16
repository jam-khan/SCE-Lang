import LeanSce.Core.Syntax
import LeanSce.Core.Typing.Typing
import LeanSce.Core.Semantics.SmallStep
import LeanSce.Core.Semantics.BigStep
import LeanSce.Core.Semantics.Equivalence
import LeanSce.Core.Semantics.Determinism
import LeanSce.Core.Preservation
import LeanSce.SCE.Semantics.SmallStep
import LeanSce.SCE.Semantics.Equivalence
import LeanSce.SCE.Elaboration.Elaboration
import LeanSce.SCE.Elaboration.Preservation
import LeanSce.SCE.Preservation
import LeanSce.SCE.Progress
import LeanSce.SCE.SemanticsPreservation
import LeanSce.SCE.Sepcomp
import LeanSce.SCE.Simulation

/-!
# Divergence preservation and behaviour equivalence

Divergence is an infinite small-step sequence (`SDiverges`, `CDiverges`).  The
forward simulation of `SCE.Simulation` turns an infinite source sequence into an
infinite Core sequence: between two `CPlus` steps the source can stutter only
finitely often, since each stutter strictly decreases `letbCount`.

With type safety of both calculi and determinism of Core, termination and
divergence are then each preserved *and* reflected: a well-typed source term
and its elaboration have the same behaviour.
-/

open SCE S_Sem

/-! ## Divergence -/

/-- A source term diverges: it starts an infinite small-step sequence. -/
def SDiverges (ρ e : SCE.Exp) : Prop :=
  ∃ f : Nat → SCE.Exp, f 0 = e ∧ ∀ n, SStep ρ (f n) (f (n + 1))

/-- A Core term diverges: it starts an infinite small-step sequence. -/
def CDiverges (ρ e : Core.Exp) : Prop :=
  ∃ f : Nat → Core.Exp, f 0 = e ∧ ∀ n, Step ρ (f n) (f (n + 1))

/-- An invariant that always admits a further step yields an infinite sequence. -/
theorem infinite_chain {α : Type} (R : α → α → Prop) (Q : α → Prop)
    (H : ∀ a, Q a → ∃ b, R a b ∧ Q b) {a : α} (ha : Q a) :
    ∃ f : Nat → α, f 0 = a ∧ ∀ n, R (f n) (f (n + 1)) := by
  let g : Nat → {x // Q x} := fun n =>
    Nat.rec ⟨a, ha⟩ (fun _ x => ⟨Classical.choose (H x.1 x.2),
      (Classical.choose_spec (H x.1 x.2)).2⟩) n
  exact ⟨fun n => (g n).1, rfl, fun n => (Classical.choose_spec (H (g n).1 (g n).2)).1⟩

theorem cdiverges_of_cplus {ρ : Core.Exp} (P : Core.Exp → Prop)
    (H : ∀ c, P c → ∃ c', CPlus ρ c c' ∧ P c') {c : Core.Exp} (hc : P c) :
    CDiverges ρ c := by
  refine infinite_chain (Step ρ) (fun c => ∃ c', CPlus ρ c c' ∧ P c') ?_ (H c hc)
  intro a ⟨c1, ⟨a', hs, hm⟩, hp⟩
  refine ⟨a', hs, ?_⟩
  cases hm with
  | refl _ => exact H _ hp
  | step hs' hm' => exact ⟨c1, ⟨_, hs', hm'⟩, hp⟩

/-! ## Divergence preservation for elaboration -/

/-- **Elaboration preserves divergence.** -/
theorem elab_preserves_divergence
    {Γ A : SCE.Typ} {es ρs : SCE.Exp} {ec ρc : Core.Exp}
    (helab : elabExp Γ es A ec)
    (henv : elabExp SCE.Typ.top ρs Γ ρc)
    (henv_val : SCE.Value ρs)
    (hdiv : SDiverges ρs es)
    : CDiverges ρc ec := by
  obtain ⟨f, hf0, hf⟩ := hdiv
  have key : ∀ k n c, letbCount (f n) = k → Sim ρs ρc Γ (f n) A c →
      ∃ m c', CPlus ρc c c' ∧ Sim ρs ρc Γ (f m) A c' := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro n c hk hs
      obtain ⟨c1, hpr, hs1⟩ := elab_forward_simulation henv (hf n) hs
      rcases hpr with hp | ⟨hm, hlt⟩
      · exact ⟨n + 1, c1, hp, hs1⟩
      · obtain ⟨m, c', hp, hs'⟩ := ih _ (hk ▸ hlt) (n + 1) c1 rfl hs1
        exact ⟨m, c', mstep_cplus_trans hm hp, hs'⟩
  refine cdiverges_of_cplus (fun c => ∃ n, Sim ρs ρc Γ (f n) A c) ?_
    ⟨0, hf0 ▸ elab_sim helab henv_val henv⟩
  intro c ⟨n, hs⟩
  obtain ⟨m, c', hp, hs'⟩ := key _ n c rfl hs
  exact ⟨c', hp, m, hs'⟩

/-! ## Divergence for separate compilation -/

/-- **Separate compilation (binary `link`), divergence.** -/
theorem separate_compilation_diverges
    {Γ Γ₁ A B : SCE.Typ} {l : String}
    {es₁ es₂ : SCE.Exp} {ec₁ ec₂ ec : Core.Exp}
    {ρs : SCE.Exp} {ρc : Core.Exp}
    (helab₁ : elabExp Γ es₁ Γ₁ ec₁)
    (helab₂ : elabExp Γ es₂ (.marr (.rcd l A) B) ec₂)
    (hlookup : SRLookup Γ₁ l A)
    (hlink : CoreLink l (elabTyp Γ₁) (elabTyp A) (elabTyp B) ec₁ ec₂ ec)
    (hdiv : SDiverges ρs (.mlink es₁ es₂))
    (henv : elabExp SCE.Typ.top ρs Γ ρc)
    (henv_val : SCE.Value ρs)
    : CDiverges ρc ec := by
  cases hlink with
  | link =>
    exact elab_preserves_divergence
      (elabExp.mlink Γ Γ₁ A B l es₁ es₂ ec₁ ec₂ helab₁ helab₂ hlookup) henv henv_val hdiv

/-- Sandboxed client, binary `link`, divergence. -/
theorem separate_compilation_sandboxed_diverges
    {Γ Γ₁ A B : SCE.Typ} {l : String}
    {es₁ body : SCE.Exp} {ec₁ ec₂ ec : Core.Exp}
    {ρs : SCE.Exp} {ρc : Core.Exp}
    (helab₁ : elabExp Γ es₁ Γ₁ ec₁)
    (helab₂ : elabExp SCE.Typ.top (.mfunctor .sandboxed (.rcd l A) body)
      (.marr (.rcd l A) B) ec₂)
    (hlookup : SRLookup Γ₁ l A)
    (hlink : CoreLink l (elabTyp Γ₁) (elabTyp A) (elabTyp B) ec₁ ec₂ ec)
    (hdiv : SDiverges ρs (.mlink es₁ (.mfunctor .sandboxed (.rcd l A) body)))
    (henv : elabExp SCE.Typ.top ρs Γ ρc)
    (henv_val : SCE.Value ρs)
    : CDiverges ρc ec :=
  separate_compilation_diverges helab₁ (sandboxed_functor_elab_context_independent helab₂)
    hlookup hlink hdiv henv henv_val

/-- Closed units, empty environment, binary `link`, divergence. -/
theorem separate_compilation_closed_diverges
    {Γ₁ A B : SCE.Typ} {l : String}
    {es₁ es₂ : SCE.Exp} {ec₁ ec₂ : Core.Exp}
    (helab₁ : elabExp SCE.Typ.top es₁ Γ₁ ec₁)
    (helab₂ : elabExp SCE.Typ.top es₂ (.marr (.rcd l A) B) ec₂)
    (hlookup : SRLookup Γ₁ l A)
    (hdiv : SDiverges .unit (.mlink es₁ es₂))
    : CDiverges .unit
        (linkedCore (elabTyp Γ₁) (elabTyp (SCE.Typ.rcd l A)) (elabTyp B) ec₁ ec₂) :=
  separate_compilation_diverges helab₁ helab₂ hlookup
    (CoreLink.link _ _ _ _ _ _ (type_safe_record_lookup hlookup)) hdiv
    (elabExp.eunit .top) SCE.Value.vunit

/-- **Separate compilation (n-ary `linkall`), divergence.** -/
theorem separate_compilation_n_diverges
    {Γ Γ₁ D B : SCE.Typ}
    {es₁ es₂ : SCE.Exp} {ec₁ ec₂ ec : Core.Exp}
    {ρs : SCE.Exp} {ρc : Core.Exp}
    (helab₁ : elabExp Γ es₁ Γ₁ ec₁)
    (helab₂ : elabExp Γ es₂ (.marr D B) ec₂)
    (hok : LinkOk Γ₁ D)
    (hlink : CoreLinkN D (elabTyp Γ₁) (elabTyp B) ec₁ ec₂ ec)
    (hdiv : SDiverges ρs (.mlinkn es₁ es₂))
    (henv : elabExp SCE.Typ.top ρs Γ ρc)
    (henv_val : SCE.Value ρs)
    : CDiverges ρc ec := by
  cases hlink with
  | link =>
    exact elab_preserves_divergence
      (elabExp.mlinkn Γ Γ₁ D B es₁ es₂ ec₁ ec₂ helab₁ helab₂ hok) henv henv_val hdiv

/-- Sandboxed client, n-ary `linkall`, divergence. -/
theorem separate_compilation_n_sandboxed_diverges
    {Γ Γ₁ D B : SCE.Typ}
    {es₁ body : SCE.Exp} {ec₁ ec₂ ec : Core.Exp}
    {ρs : SCE.Exp} {ρc : Core.Exp}
    (helab₁ : elabExp Γ es₁ Γ₁ ec₁)
    (helab₂ : elabExp SCE.Typ.top (.mfunctor .sandboxed D body) (.marr D B) ec₂)
    (hok : LinkOk Γ₁ D)
    (hlink : CoreLinkN D (elabTyp Γ₁) (elabTyp B) ec₁ ec₂ ec)
    (hdiv : SDiverges ρs (.mlinkn es₁ (.mfunctor .sandboxed D body)))
    (henv : elabExp SCE.Typ.top ρs Γ ρc)
    (henv_val : SCE.Value ρs)
    : CDiverges ρc ec :=
  separate_compilation_n_diverges helab₁ (sandboxed_functor_elab_context_independent helab₂)
    hok hlink hdiv henv henv_val

/-- Closed units, empty environment, n-ary `linkall`, divergence. -/
theorem separate_compilation_n_closed_diverges
    {Γ₁ D B : SCE.Typ}
    {es₁ es₂ : SCE.Exp} {ec₁ ec₂ : Core.Exp}
    (helab₁ : elabExp SCE.Typ.top es₁ Γ₁ ec₁)
    (helab₂ : elabExp SCE.Typ.top es₂ (.marr D B) ec₂)
    (hok : LinkOk Γ₁ D)
    (hdiv : SDiverges .unit (.mlinkn es₁ es₂))
    : CDiverges .unit (linkedCore (elabTyp Γ₁) (elabTyp D) (elabTyp B) ec₁ ec₂) :=
  separate_compilation_n_diverges helab₁ helab₂ hok (CoreLinkN.link _ _ _ _ _) hdiv
    (elabExp.eunit .top) SCE.Value.vunit

/-! ## Behaviour equivalence -/

/-- Source type safety: a well-typed source term terminates or diverges. -/
theorem source_terminates_or_diverges
    {Γ A : SCE.Typ} {es ρs : SCE.Exp} {ec ρc : Core.Exp}
    (helab : elabExp Γ es A ec)
    (henv : elabExp SCE.Typ.top ρs Γ ρc)
    (henv_val : SCE.Value ρs)
    : (∃ vs, BStep ρs es vs) ∨ SDiverges ρs es := by
  by_cases h : ∃ vs, BStep ρs es vs
  · exact Or.inl h
  · refine Or.inr (infinite_chain (SStep ρs)
      (fun e => SCE.HasType Γ e A ∧ ¬ ∃ vs, BStep ρs e vs) ?_ ⟨⟨ec, helab⟩, h⟩)
    intro e ⟨ht, hnt⟩
    rcases sgprogress ht henv_val ⟨ρc, henv⟩ with hv | ⟨e', hs⟩
    · exact absurd ⟨e, sbig_value_refl hv henv_val⟩ hnt
    · exact ⟨e', hs, sgpreservation hs ht henv_val ⟨ρc, henv⟩,
        fun ⟨vs, hb⟩ => hnt ⟨vs, sstep_sbig hs hb⟩⟩

/-- A well-typed Core term cannot both diverge and reach a value. -/
theorem core_diverges_not_terminates
    {E A : Core.Typ} {ρ e v : Core.Exp}
    (ht : HasType E e A) (hρ : HasType .top ρ E)
    (hdiv : CDiverges ρ e) (hm : MStep ρ e v) (hv : Core.Value v) : False := by
  induction hm generalizing A with
  | refl _ =>
    obtain ⟨f, hf0, hf⟩ := hdiv
    exact core_value_no_step hv (hf0 ▸ hf 0)
  | step hs _ ih =>
    obtain ⟨f, hf0, hf⟩ := hdiv
    have h1 := core_step_deterministic hs (hf0 ▸ hf 0) ht hρ
    exact ih (gpreservation hs ht hρ) ⟨fun n => f (n + 1), h1.symm, fun n => hf (n + 1)⟩ hv

/-- Well-typed Core multi-step evaluation has at most one value. -/
theorem core_mstep_value_unique
    {E A : Core.Typ} {ρ e v1 v2 : Core.Exp}
    (ht : HasType E e A) (hρ : HasType .top ρ E)
    (hm1 : MStep ρ e v1) (hv1 : Core.Value v1)
    (hm2 : MStep ρ e v2) (hv2 : Core.Value v2) : v1 = v2 := by
  induction hm1 generalizing A with
  | refl _ =>
    cases hm2 with
    | refl _ => rfl
    | step hs _ => exact absurd hs (core_value_no_step hv1)
  | step hs _ ih =>
    cases hm2 with
    | refl _ => exact absurd hs (core_value_no_step hv2)
    | step hs' hm2' =>
      have h := core_step_deterministic hs hs' ht hρ
      subst h
      exact ih (gpreservation hs ht hρ) hv1 hm2'

theorem core_typed_of_elab
    {Γ A : SCE.Typ} {es ρs : SCE.Exp} {ec ρc : Core.Exp}
    (helab : elabExp Γ es A ec) (henv : elabExp SCE.Typ.top ρs Γ ρc) :
    HasType (elabTyp Γ) ec (elabTyp A) ∧ HasType .top ρc (elabTyp Γ) :=
  ⟨type_preservation helab, type_preservation henv⟩

/-- **Termination is reflected**: if the elaboration terminates, so does the
source, at a value whose elaboration is the Core result. -/
theorem elab_reflects_termination
    {Γ A : SCE.Typ} {es ρs : SCE.Exp} {ec ρc vc : Core.Exp}
    (helab : elabExp Γ es A ec)
    (henv : elabExp SCE.Typ.top ρs Γ ρc)
    (henv_val : SCE.Value ρs)
    (hbig : EBig ρc ec vc)
    : ∃ vs, BStep ρs es vs ∧ elabExp SCE.Typ.top vs A vc := by
  obtain ⟨ht, hρ⟩ := core_typed_of_elab helab henv
  have hρc := elab_value henv henv_val
  rcases source_terminates_or_diverges helab henv henv_val with ⟨vs, hb⟩ | hdiv
  · obtain ⟨vc', hbig', helab'⟩ := semantic_preservation helab hb henv henv_val
    have heq := core_mstep_value_unique ht hρ (ebig_sound hbig) (ebig_produces_value hρc hbig)
      (ebig_sound hbig') (ebig_produces_value hρc hbig')
    exact ⟨vs, hb, heq ▸ helab'⟩
  · exact (core_diverges_not_terminates ht hρ
      (elab_preserves_divergence helab henv henv_val hdiv)
      (ebig_sound hbig) (ebig_produces_value hρc hbig)).elim

/-- **Divergence is reflected**: if the elaboration diverges, so does the source. -/
theorem elab_reflects_divergence
    {Γ A : SCE.Typ} {es ρs : SCE.Exp} {ec ρc : Core.Exp}
    (helab : elabExp Γ es A ec)
    (henv : elabExp SCE.Typ.top ρs Γ ρc)
    (henv_val : SCE.Value ρs)
    (hdiv : CDiverges ρc ec)
    : SDiverges ρs es := by
  obtain ⟨ht, hρ⟩ := core_typed_of_elab helab henv
  have hρc := elab_value henv henv_val
  rcases source_terminates_or_diverges helab henv henv_val with ⟨vs, hb⟩ | hsdiv
  · obtain ⟨vc, hbig, _⟩ := semantic_preservation helab hb henv henv_val
    exact (core_diverges_not_terminates ht hρ hdiv (ebig_sound hbig)
      (ebig_produces_value hρc hbig)).elim
  · exact hsdiv

/-- The behaviour of a well-typed term and of its elaboration: the same values
(up to elaboration) on termination, and divergence iff divergence. -/
def SameBehaviour (A : SCE.Typ) (ρs es : SCE.Exp) (ρc ec : Core.Exp) : Prop :=
  (∀ vs, BStep ρs es vs → ∃ vc, EBig ρc ec vc ∧ elabExp SCE.Typ.top vs A vc)
  ∧ (∀ vc, EBig ρc ec vc → ∃ vs, BStep ρs es vs ∧ elabExp SCE.Typ.top vs A vc)
  ∧ (SDiverges ρs es ↔ CDiverges ρc ec)

/-- **Behaviour equivalence for elaboration.** -/
theorem elab_behaviour_equiv
    {Γ A : SCE.Typ} {es ρs : SCE.Exp} {ec ρc : Core.Exp}
    (helab : elabExp Γ es A ec)
    (henv : elabExp SCE.Typ.top ρs Γ ρc)
    (henv_val : SCE.Value ρs)
    : SameBehaviour A ρs es ρc ec :=
  ⟨fun _ hb => semantic_preservation helab hb henv henv_val,
   fun _ hbig => elab_reflects_termination helab henv henv_val hbig,
   ⟨elab_preserves_divergence helab henv henv_val,
    elab_reflects_divergence helab henv henv_val⟩⟩

/-! ## Behaviour equivalence for separate compilation -/

/-- **Separate compilation (binary `link`), behaviour equivalence.** -/
theorem separate_compilation_behaviour
    {Γ Γ₁ A B : SCE.Typ} {l : String}
    {es₁ es₂ : SCE.Exp} {ec₁ ec₂ ec : Core.Exp}
    {ρs : SCE.Exp} {ρc : Core.Exp}
    (helab₁ : elabExp Γ es₁ Γ₁ ec₁)
    (helab₂ : elabExp Γ es₂ (.marr (.rcd l A) B) ec₂)
    (hlookup : SRLookup Γ₁ l A)
    (hlink : CoreLink l (elabTyp Γ₁) (elabTyp A) (elabTyp B) ec₁ ec₂ ec)
    (henv : elabExp SCE.Typ.top ρs Γ ρc)
    (henv_val : SCE.Value ρs)
    : SameBehaviour (.and Γ₁ B) ρs (.mlink es₁ es₂) ρc ec := by
  cases hlink with
  | link =>
    exact elab_behaviour_equiv
      (elabExp.mlink Γ Γ₁ A B l es₁ es₂ ec₁ ec₂ helab₁ helab₂ hlookup) henv henv_val

/-- Sandboxed client, binary `link`, behaviour equivalence. -/
theorem separate_compilation_sandboxed_behaviour
    {Γ Γ₁ A B : SCE.Typ} {l : String}
    {es₁ body : SCE.Exp} {ec₁ ec₂ ec : Core.Exp}
    {ρs : SCE.Exp} {ρc : Core.Exp}
    (helab₁ : elabExp Γ es₁ Γ₁ ec₁)
    (helab₂ : elabExp SCE.Typ.top (.mfunctor .sandboxed (.rcd l A) body)
      (.marr (.rcd l A) B) ec₂)
    (hlookup : SRLookup Γ₁ l A)
    (hlink : CoreLink l (elabTyp Γ₁) (elabTyp A) (elabTyp B) ec₁ ec₂ ec)
    (henv : elabExp SCE.Typ.top ρs Γ ρc)
    (henv_val : SCE.Value ρs)
    : SameBehaviour (.and Γ₁ B) ρs
        (.mlink es₁ (.mfunctor .sandboxed (.rcd l A) body)) ρc ec :=
  separate_compilation_behaviour helab₁ (sandboxed_functor_elab_context_independent helab₂)
    hlookup hlink henv henv_val

/-- Closed units, empty environment, binary `link`, behaviour equivalence. -/
theorem separate_compilation_closed_behaviour
    {Γ₁ A B : SCE.Typ} {l : String}
    {es₁ es₂ : SCE.Exp} {ec₁ ec₂ : Core.Exp}
    (helab₁ : elabExp SCE.Typ.top es₁ Γ₁ ec₁)
    (helab₂ : elabExp SCE.Typ.top es₂ (.marr (.rcd l A) B) ec₂)
    (hlookup : SRLookup Γ₁ l A)
    : SameBehaviour (.and Γ₁ B) .unit (.mlink es₁ es₂) .unit
        (linkedCore (elabTyp Γ₁) (elabTyp (SCE.Typ.rcd l A)) (elabTyp B) ec₁ ec₂) :=
  separate_compilation_behaviour helab₁ helab₂ hlookup
    (CoreLink.link _ _ _ _ _ _ (type_safe_record_lookup hlookup))
    (elabExp.eunit .top) SCE.Value.vunit

/-- **Separate compilation (n-ary `linkall`), behaviour equivalence.** -/
theorem separate_compilation_n_behaviour
    {Γ Γ₁ D B : SCE.Typ}
    {es₁ es₂ : SCE.Exp} {ec₁ ec₂ ec : Core.Exp}
    {ρs : SCE.Exp} {ρc : Core.Exp}
    (helab₁ : elabExp Γ es₁ Γ₁ ec₁)
    (helab₂ : elabExp Γ es₂ (.marr D B) ec₂)
    (hok : LinkOk Γ₁ D)
    (hlink : CoreLinkN D (elabTyp Γ₁) (elabTyp B) ec₁ ec₂ ec)
    (henv : elabExp SCE.Typ.top ρs Γ ρc)
    (henv_val : SCE.Value ρs)
    : SameBehaviour (.and Γ₁ B) ρs (.mlinkn es₁ es₂) ρc ec := by
  cases hlink with
  | link =>
    exact elab_behaviour_equiv
      (elabExp.mlinkn Γ Γ₁ D B es₁ es₂ ec₁ ec₂ helab₁ helab₂ hok) henv henv_val

/-- Sandboxed client, n-ary `linkall`, behaviour equivalence. -/
theorem separate_compilation_n_sandboxed_behaviour
    {Γ Γ₁ D B : SCE.Typ}
    {es₁ body : SCE.Exp} {ec₁ ec₂ ec : Core.Exp}
    {ρs : SCE.Exp} {ρc : Core.Exp}
    (helab₁ : elabExp Γ es₁ Γ₁ ec₁)
    (helab₂ : elabExp SCE.Typ.top (.mfunctor .sandboxed D body) (.marr D B) ec₂)
    (hok : LinkOk Γ₁ D)
    (hlink : CoreLinkN D (elabTyp Γ₁) (elabTyp B) ec₁ ec₂ ec)
    (henv : elabExp SCE.Typ.top ρs Γ ρc)
    (henv_val : SCE.Value ρs)
    : SameBehaviour (.and Γ₁ B) ρs (.mlinkn es₁ (.mfunctor .sandboxed D body)) ρc ec :=
  separate_compilation_n_behaviour helab₁ (sandboxed_functor_elab_context_independent helab₂)
    hok hlink henv henv_val

/-- Closed units, empty environment, n-ary `linkall`, behaviour equivalence. -/
theorem separate_compilation_n_closed_behaviour
    {Γ₁ D B : SCE.Typ}
    {es₁ es₂ : SCE.Exp} {ec₁ ec₂ : Core.Exp}
    (helab₁ : elabExp SCE.Typ.top es₁ Γ₁ ec₁)
    (helab₂ : elabExp SCE.Typ.top es₂ (.marr D B) ec₂)
    (hok : LinkOk Γ₁ D)
    : SameBehaviour (.and Γ₁ B) .unit (.mlinkn es₁ es₂) .unit
        (linkedCore (elabTyp Γ₁) (elabTyp D) (elabTyp B) ec₁ ec₂) :=
  separate_compilation_n_behaviour helab₁ helab₂ hok (CoreLinkN.link _ _ _ _ _)
    (elabExp.eunit .top) SCE.Value.vunit
