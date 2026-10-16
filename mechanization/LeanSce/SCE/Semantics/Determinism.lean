import LeanSce.Core.Syntax
import LeanSce.Core.Semantics.BigStep
import LeanSce.Core.Semantics.Equivalence
import LeanSce.Core.Typing.Typing
import LeanSce.SCE.Syntax
import LeanSce.SCE.Semantics.BigStep
import LeanSce.SCE.Elaboration.Elaboration
import LeanSce.SCE.Elaboration.Uniqueness
import LeanSce.SCE.Elaboration.Preservation
import LeanSce.SCE.Preservation
import LeanSce.SCE.SemanticsPreservation

open SCE Core

/-!
Determinism of SCE evaluation, proved through elaboration: the elaboration
hypothesis rules out ambiguous label selection.
-/

-- Determinism

private theorem lookupV_deterministic
    {v v₁ v₂ : SCE.Exp} {n : Nat}
    (h₁ : S_Sem.LookupV v n v₁)
    (h₂ : S_Sem.LookupV v n v₂)
    : v₁ = v₂ := by
  induction h₁ generalizing v₂ with
  | dmrg_zero => cases h₂ with | dmrg_zero => rfl
  | dmrg_succ _ ih => cases h₂ with | dmrg_succ h₂' => exact ih h₂'
  | nmrg_zero => cases h₂ with | nmrg_zero => rfl
  | nmrg_succ _ ih => cases h₂ with | nmrg_succ h₂' => exact ih h₂'

theorem sel_deterministic
    {v v₁ v₂ : SCE.Exp} {vc : Core.Exp} {A B : SCE.Typ} {l : String}
    (hval : SCE.Value v)
    (helab : elabExp SCE.Typ.top v A vc)
    (hlookup : SCE.SRLookup A l B)
    (hsel₁ : S_Sem.Sel v l v₁)
    (hsel₂ : S_Sem.Sel v l v₂)
    : v₁ = v₂ := by
  induction hsel₁ generalizing v₂ A B vc with
  | rcd =>
    cases hval with | vlrec hv =>
    cases helab with | elrec _ _ _ _ _ h =>
    cases hlookup with | zero =>
    cases hsel₂ with | rcd => rfl
  | dmrg_left hsel_inner ih =>
    cases hval with | vmrg hv1 hv2 =>
    cases helab with | edmrg _ A' B' _ _ ce1 ce2 h1 h2 =>
    cases hlookup with
    | andl _ _ _ _ hrl hcond =>
      cases hsel₂ with
      | dmrg_left hsel₂' => exact ih hv1 h1 hrl hsel₂'
      | dmrg_right hsel₂' =>
        have hlin := sel_implies_label_in hv2
          (elab_value_weaken h2 hv2 (SCE.Typ.top)) hsel₂'
        exact absurd hlin hcond
    | andr _ _ _ _ hrl hcond =>
      have hlin := sel_implies_label_in hv1 h1 hsel_inner
      exact absurd hlin hcond
  | dmrg_right hsel_inner ih =>
    cases hval with | vmrg hv1 hv2 =>
    cases helab with | edmrg _ A' B' _ _ ce1 ce2 h1 h2 =>
    have h2_weak := elab_value_weaken h2 hv2 (SCE.Typ.top)
    cases hlookup with
    | andr _ _ _ _ hrl hcond =>
      cases hsel₂ with
      | dmrg_right hsel₂' => exact ih hv2 h2_weak hrl hsel₂'
      | dmrg_left hsel₂' =>
        have hlin := sel_implies_label_in hv1 h1 hsel₂'
        exact absurd hlin hcond
    | andl _ _ _ _ hrl hcond =>
      have hlin := sel_implies_label_in hv2 h2_weak hsel_inner
      exact absurd hlin hcond
  | nmrg_left   => cases hval
  | nmrg_right  => cases hval
  | mstruct hsel_inner ih =>
    cases hval with | vmstruct hv =>
    cases helab with
    | mstruct _ _ _ _ h =>
      cases hlookup with | sig _ _ _ hrl =>
      cases hsel₂ with | mstruct hsel₂' => exact ih hv h hrl hsel₂'

private theorem selpkg_deterministic
    {Γ₁ D : SCE.Typ} (hok : LinkOk Γ₁ D)
    {v : SCE.Exp} {vc : Core.Exp}
    (hval : SCE.Value v)
    (helab : elabExp SCE.Typ.top v Γ₁ vc)
    : ∀ {pkg₁ pkg₂ : SCE.Exp},
      S_Sem.SelPkg v D pkg₁
      → S_Sem.SelPkg v D pkg₂
      → pkg₁ = pkg₂ := by
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

theorem bigstep_deterministic_gen
    {Γ A : SCE.Typ} {e ρ v₁ v₂ : SCE.Exp} {ec ρc : Core.Exp}
    (helab : elabExp Γ e A ec)
    (henv : elabExp SCE.Typ.top ρ Γ ρc)
    (henv_val : SCE.Value ρ)
    (heval₁ : S_Sem.BStep ρ e v₁)
    (heval₂ : S_Sem.BStep ρ e v₂)
    : v₁ = v₂ := by
  induction heval₁ generalizing v₂ Γ A ec ρc with
  | query _ =>
    cases helab; cases heval₂; rfl
  | lit _ =>
    cases helab; cases heval₂; rfl
  | unit _ =>
    cases helab; cases heval₂; rfl
  | clos_val _ _ =>
    cases helab with
    | eclos _ _ _ _ _ _ _ _ _ h1 h2 =>
      cases heval₂ with | clos_val => rfl
  | mclos_val _ _ =>
    cases helab with
    | mclos _ _ _ _ _ _ _ _ _ h1 h2 =>
      cases heval₂ with | mclos_val => rfl
  | proj hval₁ hstep₁ hlook₁ ih₁ =>
    cases helab with
    | eproj _ A' _ _ ce _ h_elab h_slook =>
      cases heval₂ with
      | proj _ hstep₂ hlook₂ =>
        have := ih₁ h_elab henv henv_val hstep₂
        rw [this] at hlook₁
        exact lookupV_deterministic hlook₁ hlook₂
  | lam _ =>
    cases helab; cases heval₂; rfl
  | box hval₁ hstep₁a hstep₁b ih₁a ih₁b =>
    cases helab with
    | ebox _ ctx' _ _ _ ce1 ce2 h_elab1 h_elab2 =>
      cases heval₂ with
      | box _ hstep₂a hstep₂b =>
        have heq_a := ih₁a h_elab1 henv henv_val hstep₂a
        rw [← heq_a] at hstep₂b
        have hv₁_val := eval_produces_value henv_val hstep₁a
        have ⟨_, _, hv₁_elab⟩ := semantic_preservation h_elab1 hstep₁a henv henv_val
        exact ih₁b h_elab2 hv₁_elab hv₁_val hstep₂b
  | app_clos hval₁ hstep₁f hstep₁a hstep₁b ih₁f ih₁a ih₁b =>
    cases helab with
    | eapp _ A_param B _ _ ce1 ce2 h_elab1 h_elab2 =>
      cases heval₂ with
      | app_clos _ hstep₂f hstep₂a hstep₂b =>
        have heq_f := ih₁f h_elab1 henv henv_val hstep₂f
        cases heq_f
        have heq_a := ih₁a h_elab2 henv henv_val hstep₂a
        rw [← heq_a] at hstep₂b
        have hvclos := eval_produces_value henv_val hstep₁f
        cases hvclos with
        | vclos hval_inner =>
          have hva := eval_produces_value henv_val hstep₁a
          have ⟨_, _, helab_clos⟩ := semantic_preservation h_elab1 hstep₁f henv henv_val
          cases helab_clos with
          | eclos _ _ _ _ _ _ _ _ _ h_env_inner h_body =>
            have ⟨_, _, helab_arg⟩ := semantic_preservation h_elab2 hstep₁a henv henv_val
            have hval_body_env := SCE.Value.vmrg hval_inner hva
            have helab_body_env := elabExp.edmrg .top _ _ _ _ _ _ h_env_inner
              (elab_value_weaken helab_arg hva _)
            exact ih₁b h_body helab_body_env hval_body_env hstep₂b
      | app_fclos _ hstep₂f hstep₂a hstep₂b =>
        have heq_f := ih₁f h_elab1 henv henv_val hstep₂f
        cases heq_f
  | app_mclos hval₁ hstep₁f hstep₁a hstep₁b ih₁f ih₁a ih₁b =>
    cases helab with
    | mapp _ A_param B _ _ ce1 ce2 h_elab1 h_elab2 =>
      cases heval₂ with
      | app_mclos _ hstep₂f hstep₂a hstep₂b =>
        have heq_f := ih₁f h_elab1 henv henv_val hstep₂f
        cases heq_f
        have heq_a := ih₁a h_elab2 henv henv_val hstep₂a
        rw [← heq_a] at hstep₂b
        have hvclos := eval_produces_value henv_val hstep₁f
        cases hvclos with
        | vmclos hval_inner =>
          have hva := eval_produces_value henv_val hstep₁a
          have ⟨_, _, helab_clos⟩ := semantic_preservation h_elab1 hstep₁f henv henv_val
          cases helab_clos with
          | mclos _ _ _ _ _ _ _ _ _ h_env_inner h_body =>
            have ⟨_, _, helab_arg⟩ := semantic_preservation h_elab2 hstep₁a henv henv_val
            have hval_body_env := SCE.Value.vmrg hval_inner hva
            have helab_body_env := elabExp.edmrg .top _ _ _ _ _ _ h_env_inner
              (elab_value_weaken helab_arg hva _)
            exact ih₁b h_body helab_body_env hval_body_env hstep₂b
  | dmrg hval₁ hstep₁a hstep₁b ih₁a ih₁b =>
    cases helab with
    | edmrg _ A' B' _ _ ce1 ce2 h_elab1 h_elab2 =>
      cases heval₂ with
      | dmrg _ hstep₂a hstep₂b =>
        have heq_a := ih₁a h_elab1 henv henv_val hstep₂a
        rw [← heq_a] at hstep₂b
        have hv1_val := eval_produces_value henv_val hstep₁a
        have ⟨_, _, helab_v1⟩ := semantic_preservation h_elab1 hstep₁a henv henv_val
        have hval_mrg := SCE.Value.vmrg henv_val hv1_val
        have helab_mrg := elabExp.edmrg .top _ _ _ _ _ _ henv
          (elab_value_weaken helab_v1 hv1_val _)
        have heq_b := ih₁b h_elab2 helab_mrg hval_mrg hstep₂b
        rw [heq_a, heq_b]
  | nmrg hval₁ hstep₁a hstep₁b ih₁a ih₁b =>
    cases helab with
    | enmrg _ A' B' _ _ ce1 ce2 h_elab1 h_elab2 =>
      cases heval₂ with
      | nmrg _ hstep₂a hstep₂b =>
        have heq_a := ih₁a h_elab1 henv henv_val hstep₂a
        have heq_b := ih₁b h_elab2 henv henv_val hstep₂b
        rw [heq_a, heq_b]
  | lrec hval₁ hstep₁ ih₁ =>
    cases helab with
    | elrec _ _ _ _ _ h_elab =>
      cases heval₂ with
      | lrec _ hstep₂ =>
        have := ih₁ h_elab henv henv_val hstep₂
        rw [this]
  | rproj hval₁ hstep₁ hsel₁ ih₁ =>
    cases helab with
    | erproj _ A' B' _ _ l h_elab h_slook =>
      cases heval₂ with
      | rproj _ hstep₂ hsel₂ =>
        have heq := ih₁ h_elab henv henv_val hstep₂
        rw [heq] at hsel₁
        have hv_val := eval_produces_value henv_val hstep₂
        have ⟨_, _, helab_v⟩ := semantic_preservation h_elab hstep₂ henv henv_val
        exact sel_deterministic hv_val helab_v h_slook hsel₁ hsel₂
  | letb hval₁ hstep₁a hstep₁b ih₁a ih₁b =>
    cases helab with
    | letb _ A' B' _ _ ce1 ce2 h_elab1 h_elab2 =>
      cases heval₂ with
      | letb _ hstep₂a hstep₂b =>
        have heq_a := ih₁a h_elab1 henv henv_val hstep₂a
        rw [← heq_a] at hstep₂b
        have hv1_val := eval_produces_value henv_val hstep₁a
        have ⟨_, _, helab_v1⟩ := semantic_preservation h_elab1 hstep₁a henv henv_val
        have hval_mrg := SCE.Value.vmrg henv_val hv1_val
        have helab_mrg := elabExp.edmrg .top _ _ _ _ _ _ henv
          (elab_value_weaken helab_v1 hv1_val _)
        exact ih₁b h_elab2 helab_mrg hval_mrg hstep₂b
  | openm hval₁ hstep₁a hstep₁b ih₁a ih₁b =>
    cases helab with
    | openm _ A' B' _ _ ce1 ce2 l h_elab1 h_elab2 =>
      cases heval₂ with
      | openm _ hstep₂a hstep₂b =>
        have heq_a := ih₁a h_elab1 henv henv_val hstep₂a
        cases heq_a
        have hv_val := eval_produces_value henv_val hstep₂a
        cases hv_val with
        | vlrec hval_inner =>
          have ⟨_, _, helab_rcd⟩ := semantic_preservation h_elab1 hstep₂a henv henv_val
          cases helab_rcd with
          | elrec _ _ _ _ _ helab_inner =>
            have hval_mrg := SCE.Value.vmrg henv_val hval_inner
            have helab_mrg := elabExp.edmrg .top _ _ _ _ _ _ henv
              (elab_value_weaken helab_inner hval_inner _)
            exact ih₁b h_elab2 helab_mrg hval_mrg hstep₂b
  | mstruct hval₁ hstep₁ ih₁ =>
    cases helab with
    | mstruct _ _ _ _ h_elab =>
      cases heval₂ with
      | mstruct _ hstep₂ =>
        rw [ih₁ h_elab henv henv_val hstep₂]
  | mfunctor_sandboxed _ =>
    cases helab with | mfunctor => cases heval₂ with | mfunctor_sandboxed => rfl
  | mfunctor_open _ =>
    cases helab with | mfunctor => cases heval₂ with | mfunctor_open => rfl
  | mlink hval₁ hstep₁a hstep₁b hsel₁ hstep₁c ih₁a ih₁b ih₁c =>
    rename_i _ _ _ _ _ _ _ l_bstep
    cases helab with
    | mlink _ Γ₁ A_inner B_inner l_elab _ _ ce1 ce2 h_elab1 h_elab2 h_lookup =>
      cases heval₂ with
      | mlink _ hstep₂a hstep₂b hsel₂ hstep₂c =>
        -- e₁ produces the same value
        have heq_a := ih₁a h_elab1 henv henv_val hstep₂a
        -- e₂ produces the same mclos (unifies labels, bodies, etc.)
        have heq_b := ih₁b h_elab2 henv henv_val hstep₂b
        cases heq_b
        -- Now hsel₁ and hsel₂ use the same label (l_bstep from BStep)
        -- but h_lookup uses l_elab. Connect them via semantic_preservation.
        have hv1_val := eval_produces_value henv_val hstep₁a
        have ⟨_, _, helab_v1⟩ := semantic_preservation h_elab1 hstep₁a henv henv_val
        have ⟨_, _, helab_mclos⟩ := semantic_preservation h_elab2 hstep₁b henv henv_val
        cases helab_mclos with
        | mclos _ ctx_inner _ _ _ _ _ _ hval_v2 h_env2 h_body =>
          have htype_eq := elaboration_inference_uniqueness
            (semantic_preservation h_elab2 hstep₁b henv henv_val).choose_spec.2
            (elabExp.mclos .top ctx_inner _ _ _ _ _ _ hval_v2 h_env2 h_body)
          cases htype_eq
          -- Rewrite hsel₂ to use heval₁'s v₁
          rw [← heq_a] at hsel₂
          -- sel deterministic: vₗ₁ = vₗ₂, then subst to unify
          have heq_sel := sel_deterministic hv1_val helab_v1 h_lookup hsel₁ hsel₂
          subst heq_sel
          -- build env elaboration for body
          have hvl_val := source_sel_value hv1_val hsel₁
          obtain ⟨_, _, helab_vl⟩ := sel_preservation hv1_val helab_v1 hsel₁ h_lookup
          have helab_lrec := elabExp.elrec .top _ _ _ l_bstep helab_vl
          have hval_lrec := SCE.Value.vlrec (l := l_bstep) hvl_val
          have hval_env := SCE.Value.vmrg hval_v2 hval_lrec
          have helab_lrec_weak :=
            elab_value_weaken helab_lrec hval_lrec (SCE.Typ.and .top ctx_inner)
          have helab_env := elabExp.edmrg .top _ _ _ _ _ _ h_env2 helab_lrec_weak
          have heq_c := ih₁c h_body helab_env hval_env hstep₂c
          rw [heq_a, heq_c]
  | mlinkn hval₁ hstep₁a hstep₁b hsp₁ hstep₁c ih₁a ih₁b ih₁c =>
    cases helab with
    | mlinkn _ Γ₁ D_e B_e _ _ ce1 ce2 h_elab1 h_elab2 hok =>
      cases heval₂ with
      | mlinkn _ hstep₂a hstep₂b hsp₂ hstep₂c =>
        have heq_a := ih₁a h_elab1 henv henv_val hstep₂a
        have heq_b := ih₁b h_elab2 henv henv_val hstep₂b
        cases heq_b
        have hv1_val := eval_produces_value henv_val hstep₁a
        have ⟨_, _, helab_v1⟩ := semantic_preservation h_elab1 hstep₁a henv henv_val
        have ⟨_, _, helab_mclos⟩ := semantic_preservation h_elab2 hstep₁b henv henv_val
        cases helab_mclos with
        | mclos _ ctx_inner _ _ _ _ _ _ hval_v2 h_env2 h_body =>
          rw [← heq_a] at hsp₂
          have heq_pkg := selpkg_deterministic hok hv1_val helab_v1 hsp₁ hsp₂
          subst heq_pkg
          have hvpkg := S_Sem.selpkg_value hsp₁ hv1_val
          have ⟨_, helab_pkg⟩ := selpkg_elab hok hsp₁ hv1_val helab_v1
          have hval_env := SCE.Value.vmrg hval_v2 hvpkg
          have helab_env := elabExp.edmrg .top _ _ _ _ _ _ h_env2
            (elab_value_weaken helab_pkg hvpkg _)
          have heq_c := ih₁c h_body helab_env hval_env hstep₂c
          rw [heq_a, heq_c]
  | inl hval₁ hstep₁ ih₁ =>
    cases helab with
    | einl _ _ _ _ _ h_elab =>
      cases heval₂ with
      | inl _ hstep₂ =>
        have := ih₁ h_elab henv henv_val hstep₂
        rw [this]
  | inr hval₁ hstep₁ ih₁ =>
    cases helab with
    | einr _ _ _ _ _ h_elab =>
      cases heval₂ with
      | inr _ hstep₂ =>
        have := ih₁ h_elab henv henv_val hstep₂
        rw [this]
  | case_inl hval₁ hstep₁a hstep₁b ih₁a ih₁b =>
    cases helab with
    | ecase _ A' B' C' _ _ _ ce ce1 ce2 h_elab h_elab1 h_elab2 =>
      cases heval₂ with
      | case_inl _ hstep₂a hstep₂b =>
        have heq_a := ih₁a h_elab henv henv_val hstep₂a
        cases heq_a
        have h_inl_val := eval_produces_value henv_val hstep₁a
        cases h_inl_val with
        | vinl hv1 =>
          have ⟨_, _, helab_inl⟩ := semantic_preservation h_elab hstep₁a henv henv_val
          cases helab_inl with
          | einl _ _ _ _ _ h_v =>
            have hval_mrg := SCE.Value.vmrg henv_val hv1
            have helab_mrg := elabExp.edmrg .top _ _ _ _ _ _
              henv (elab_value_weaken h_v hv1 _)
            exact ih₁b h_elab1 helab_mrg hval_mrg hstep₂b
      | case_inr _ hstep₂a hstep₂b =>
        have heq_a := ih₁a h_elab henv henv_val hstep₂a
        cases heq_a
  | case_inr hval₁ hstep₁a hstep₁b ih₁a ih₁b =>
    cases helab with
    | ecase _ A' B' C' _ _ _ ce ce1 ce2 h_elab h_elab1 h_elab2 =>
      cases heval₂ with
      | case_inr _ hstep₂a hstep₂b =>
        have heq_a := ih₁a h_elab henv henv_val hstep₂a
        cases heq_a
        have h_inr_val := eval_produces_value henv_val hstep₁a
        cases h_inr_val with
        | vinr hv1 =>
          have ⟨_, _, helab_inr⟩ := semantic_preservation h_elab hstep₁a henv henv_val
          cases helab_inr with
          | einr _ _ _ _ _ h_v =>
            have hval_mrg := SCE.Value.vmrg henv_val hv1
            have helab_mrg := elabExp.edmrg .top _ _ _ _ _ _
              henv (elab_value_weaken h_v hv1 _)
            exact ih₁b h_elab2 helab_mrg hval_mrg hstep₂b
      | case_inl _ hstep₂a hstep₂b =>
        have heq_a := ih₁a h_elab henv henv_val hstep₂a
        cases heq_a
  | fclos_val _ _ =>
    cases helab with
    | efclos _ _ _ _ _ _ _ _ _ h1 h2 =>
      cases heval₂ with | fclos_val => rfl
  | flam _ =>
    cases helab; cases heval₂; rfl
  | app_fclos hval₁ hstep₁f hstep₁a hstep₁b ih₁f ih₁a ih₁b =>
    cases helab with
    | eapp _ A_param B _ _ ce1 ce2 h_elab1 h_elab2 =>
      cases heval₂ with
      | app_clos _ hstep₂f hstep₂a hstep₂b =>
        have heq_f := ih₁f h_elab1 henv henv_val hstep₂f
        cases heq_f
      | app_fclos _ hstep₂f hstep₂a hstep₂b =>
        have heq_f := ih₁f h_elab1 henv henv_val hstep₂f
        cases heq_f
        have heq_a := ih₁a h_elab2 henv henv_val hstep₂a
        rw [← heq_a] at hstep₂b
        have hvclos := eval_produces_value henv_val hstep₁f
        cases hvclos with
        | vfclos hval_inner =>
          have hva := eval_produces_value henv_val hstep₁a
          have ⟨_, _, helab_clos⟩ := semantic_preservation h_elab1 hstep₁f henv henv_val
          cases helab_clos with
          | efclos _ _ _ _ _ _ _ _ _ h_env_inner h_body =>
            have ⟨_, _, helab_arg⟩ := semantic_preservation h_elab2 hstep₁a henv henv_val
            have helab_body_env := elabExp.edmrg .top _ _ _ _ _ _
              (elabExp.edmrg .top _ _ _ _ _ _ h_env_inner
                (elabExp.efclos _ _ _ _ _ _ _ _ hval_inner h_env_inner h_body))
              (elab_value_weaken helab_arg hva _)
            exact ih₁b h_body helab_body_env
              (SCE.Value.vmrg (SCE.Value.vmrg hval_inner (SCE.Value.vfclos hval_inner)) hva)
              hstep₂b
  | fold hval₁ hstep₁ ih₁ =>
    cases helab with
    | efold _ _ _ _ h_elab =>
      cases heval₂ with
      | fold _ hstep₂ =>
        have := ih₁ h_elab henv henv_val hstep₂
        rw [this]
  | unfold hval₁ hstep₁ ih₁ =>
    cases helab with
    | eunfold _ _ _ _ _ h_elab heq =>
      cases heval₂ with
      | unfold _ hstep₂ =>
        have heq_f := ih₁ h_elab henv henv_val hstep₂
        cases heq_f
        rfl

theorem bigstep_deterministic
    {A : SCE.Typ} {e v₁ v₂ : SCE.Exp}
    (helab : ∃ ec, elabExp SCE.Typ.top e A ec)
    (heval₁ : S_Sem.BStep SCE.Exp.unit e v₁)
    (heval₂ : S_Sem.BStep SCE.Exp.unit e v₂)
    : v₁ = v₂ := by
  obtain ⟨ec, helab⟩ := helab
  exact bigstep_deterministic_gen helab (elabExp.eunit .top) SCE.Value.vunit heval₁ heval₂
