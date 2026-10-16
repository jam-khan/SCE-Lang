import LeanSce.SCE.Syntax
import LeanSce.SCE.Semantics.BigStep
import LeanSce.SCE.Elaboration.Elaboration
import LeanSce.SCE.Semantics.Equivalence
import LeanSce.SCE.Semantics.Determinism

open SCE S_Sem

/-
  Capability-safety for λSCE via the sandboxed-functor pattern.

  A module written as `functor_■(A) body` and applied to an argument `varg`
  executes `body` under the environment `ε ; varg` regardless of the caller's
  ambient `ρ`. Consequently, the result depends only on `body` and `varg` —
  never on the rest of the ambient. This realises the Wyvern-style capability
  discipline: authority flows through explicit argument passing, not ambient.
-/

/-- **Sandboxed Functor Confinement.**

    A sandboxed functor applied to a value argument produces a result that
    is independent of the ambient environment at the call site. -/
theorem sandboxed_functor_confinement
    {A B : Typ} {body varg v₁ v₂ ρ₁ ρ₂ : Exp} {ec_body ec_varg : Core.Exp}
    (_hρ₁ : Value ρ₁) (_hρ₂ : Value ρ₂) (hvarg : Value varg)
    (hbody_elab : elabExp (Typ.and Typ.top A) body B ec_body)
    (hvarg_elab : elabExp Typ.top varg A ec_varg)
    (h₁ : BStep ρ₁ (Exp.mapp (Exp.mfunctor Sandbox.sandboxed A body) varg) v₁)
    (h₂ : BStep ρ₂ (Exp.mapp (Exp.mfunctor Sandbox.sandboxed A body) varg) v₂)
    : v₁ = v₂ := by
  -- Invert the outer mapp reductions.
  cases h₁ with
  | app_mclos _ hfun₁ harg₁ hbody₁ =>
    cases hfun₁ with
    | mfunctor_sandboxed _ =>
      cases h₂ with
      | app_mclos _ hfun₂ harg₂ hbody₂ =>
        cases hfun₂ with
        | mfunctor_sandboxed _ =>
          -- harg₁ / harg₂ evaluate the value argument `varg`;
          -- by value self-evaluation, both produce `varg` itself.
          have e₁ := sbig_value_eq harg₁ hvarg
          have e₂ := sbig_value_eq harg₂ hvarg
          subst e₁
          subst e₂
          -- Both bodies now execute under `.mrg .unit varg` — the same env.
          -- Build the elaboration witness for that env under the empty context.
          have hvarg_weak : elabExp (Typ.and Typ.top Typ.top) varg A ec_varg :=
            elab_value_weaken hvarg_elab hvarg _
          have henv_elab :
              elabExp Typ.top (Exp.mrg Exp.unit varg) (Typ.and Typ.top A)
                (Core.Exp.mrg Core.Exp.unit ec_varg) :=
            elabExp.edmrg Typ.top Typ.top A Exp.unit varg
              Core.Exp.unit ec_varg
              (elabExp.eunit Typ.top) hvarg_weak
          have henv_val : Value (Exp.mrg Exp.unit varg) :=
            Value.vmrg Value.vunit hvarg
          -- Close via big-step determinism.
          exact bigstep_deterministic_gen hbody_elab henv_elab henv_val
            hbody₁ hbody₂

/-- **Link Confinement.**

    Two terminating links produce the same client result when their clients
    evaluate only to the same sandboxed closure and their providers supply
    the same import value. The retained provider values may differ.

    The client expressions need not be literal functors: they may, for
    example, look up a previously constructed sandboxed closure. -/
theorem sandboxed_link_confinement
    {A B : Typ} {l : String}
    {body a e₁ e₂ c₁ c₂ p₁ p₂ w₁ w₂ ρ₁ ρ₂ : Exp}
    {ec_body ec_a : Core.Exp}
    (ha : Value a)
    (hbody_elab : elabExp (Typ.and Typ.top (Typ.rcd l A)) body B ec_body)
    (ha_elab : elabExp Typ.top a A ec_a)
    (hclient₁ : ∀ {v}, BStep ρ₁ c₁ v →
      v = Exp.mclos Exp.unit (Typ.rcd l A) body)
    (hclient₂ : ∀ {v}, BStep ρ₂ c₂ v →
      v = Exp.mclos Exp.unit (Typ.rcd l A) body)
    (himport₁ : ∀ {p v}, BStep ρ₁ e₁ p → Sel p l v → v = a)
    (himport₂ : ∀ {p v}, BStep ρ₂ e₂ p → Sel p l v → v = a)
    (h₁ : BStep ρ₁ (Exp.mlink e₁ c₁) (Exp.mrg p₁ w₁))
    (h₂ : BStep ρ₂ (Exp.mlink e₂ c₂) (Exp.mrg p₂ w₂))
    : w₁ = w₂ := by
  cases h₁ with
  | mlink _ hp₁ hc₁ hs₁ hb₁ =>
    cases h₂ with
    | mlink _ hp₂ hc₂ hs₂ hb₂ =>
      -- The client hypotheses fix both closure environments and import labels.
      cases hclient₁ hc₁
      cases hclient₂ hc₂
      -- The provider hypotheses fix the selected values, not the whole providers.
      cases himport₁ hp₁ hs₁
      cases himport₂ hp₂ hs₂
      have ha_weak : elabExp (Typ.and Typ.top Typ.top) a A ec_a :=
        elab_value_weaken ha_elab ha _
      have henv_elab :
          elabExp Typ.top (Exp.mrg Exp.unit (Exp.lrec l a))
            (Typ.and Typ.top (Typ.rcd l A))
            (Core.Exp.mrg Core.Exp.unit (Core.Exp.lrec l ec_a)) :=
        elabExp.edmrg _ _ _ _ _ _ _ (elabExp.eunit _)
          (elabExp.elrec _ _ _ _ _ ha_weak)
      exact bigstep_deterministic_gen hbody_elab henv_elab
        (Value.vmrg Value.vunit (Value.vlrec ha)) hb₁ hb₂

/-- Literal sandboxed functors satisfy the client premise of link confinement
    independently of their call-site environments. -/
theorem sandboxed_functor_link_confinement
    {A B : Typ} {l : String}
    {body a e₁ e₂ p₁ p₂ w₁ w₂ ρ₁ ρ₂ : Exp}
    {ec_body ec_a : Core.Exp}
    (ha : Value a)
    (hbody_elab : elabExp (Typ.and Typ.top (Typ.rcd l A)) body B ec_body)
    (ha_elab : elabExp Typ.top a A ec_a)
    (himport₁ : ∀ {p v}, BStep ρ₁ e₁ p → Sel p l v → v = a)
    (himport₂ : ∀ {p v}, BStep ρ₂ e₂ p → Sel p l v → v = a)
    (h₁ : BStep ρ₁
      (Exp.mlink e₁ (Exp.mfunctor Sandbox.sandboxed (Typ.rcd l A) body))
      (Exp.mrg p₁ w₁))
    (h₂ : BStep ρ₂
      (Exp.mlink e₂ (Exp.mfunctor Sandbox.sandboxed (Typ.rcd l A) body))
      (Exp.mrg p₂ w₂))
    : w₁ = w₂ := by
  apply sandboxed_link_confinement ha hbody_elab ha_elab
      (fun h => by cases h; rfl) (fun h => by cases h; rfl)
      himport₁ himport₂ h₁ h₂
