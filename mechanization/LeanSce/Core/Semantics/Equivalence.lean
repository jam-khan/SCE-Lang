import LeanSce.Core.Syntax
import LeanSce.Core.Semantics.SmallStep
import LeanSce.Core.Semantics.BigStep

/-!
Equivalence of the Core small-step and big-step semantics: `MStep` congruences,
soundness (`ebig_sound`), completeness (`ebig_complete`), and `step_ebig_eq`.
-/

open Core

-- step implies that environment is value
theorem step_env_value {v e e' : Core.Exp} (h : Step v e e') : Core.Value v := by
  cases h <;> assumption

-- mstep implies that environment is a value
theorem mstep_env_value {v e e' : Core.Exp} (h : MStep v e e') : Core.Value v := by
  cases h with
  | refl hv => exact hv
  | step hs _ => exact step_env_value hs

theorem mstep_trans {v e1 e2 e3 : Core.Exp}
    (h1 : MStep v e1 e2) (h2 : MStep v e2 e3) : MStep v e1 e3 := by
  induction h1 with
  | refl _ => assumption
  | step hs ih1 ih2 =>
    rename_i e' e1' e2'
    exact MStep.step hs (ih2 h2)

theorem mstep_mrg_left {v e1 e1' : Core.Exp}
    (h : MStep v e1 e1') (e2 : Core.Exp)
    : MStep v (.mrg e1 e2) (.mrg e1' e2) := by
  induction h with
  | refl hv =>
    rename_i e
    exact MStep.refl hv
  | step hs ih1 ih2 =>
    rename_i e' e1'' e2'
    apply MStep.step <;> try assumption
    apply Step.smrgl <;> try assumption
    apply step_env_value hs

theorem mstep_mrg_right {v v1 e2 e2' : Core.Exp}
    (hv : Core.Value v) (hv1 : Core.Value v1)
    (h : MStep (.mrg v v1) e2 e2')
    : MStep v (.mrg v1 e2) (.mrg v1 e2') := by
  induction h with
  | refl _ => exact MStep.refl hv
  | step hs _ ih => exact MStep.step (Step.smrgr hv hv1 hs) ih

theorem mstep_app_left {v e1 e1' : Core.Exp}
    (h : MStep v e1 e1') (e2 : Core.Exp)
    : MStep v (.app e1 e2) (.app e1' e2) := by
  induction h with
  | refl hv => exact MStep.refl hv
  | step hs _ ih => exact MStep.step (Step.sappl (step_env_value hs) hs) ih

theorem mstep_app_right {v v1 e2 e2': Core.Exp}
    (hv1 : Core.Value v1)
    (h : MStep v e2 e2')
    : MStep v (.app v1 e2) (.app v1 e2') := by
  induction h with
  | refl hv => exact MStep.refl hv
  | step hs _ ih =>
    exact MStep.step (Step.sappr (step_env_value hs) hv1 hs) ih

theorem mstep_box_left {v e1 e1' : Core.Exp}
    (h : MStep v e1 e1') (e2 : Core.Exp)
    : MStep v (.box e1 e2) (.box e1' e2) := by
  induction h with
  | refl hv => exact MStep.refl hv
  | step hs _ ih => exact MStep.step (Step.sboxl (step_env_value hs) hs) ih

theorem mstep_box_right {v v1 e2 e2' : Core.Exp}
    (hv : Core.Value v) (hv1 : Core.Value v1)
    (h : MStep v1 e2 e2')
    : MStep v (.box v1 e2) (.box v1 e2') := by
  induction h with
  | refl _ => exact MStep.refl hv
  | step hs _ ih => exact MStep.step (Step.sboxr hv hv1 hs) ih

theorem box_mstep_drop_env {e e1 v2 : Core.Exp}
    (hm : MStep e e1 v2) (hv2 : Core.Value v2)
    {v : Core.Exp} (hv : Core.Value v)
    : MStep v (.box e e1) v2 := by
  have hve := mstep_env_value hm
  exact mstep_trans
    (mstep_box_right hv hve hm)
    (MStep.step (Step.sboxv hv hve hv2) (MStep.refl hv))

theorem mstep_proj {v e1 e2 : Core.Exp} {n : Nat}
    (h : MStep v e1 e2)
    : MStep v (.proj e1 n) (.proj e2 n) := by
  induction h with
  | refl hv => exact MStep.refl hv
  | step hs _ ih => exact MStep.step (Step.sproj (step_env_value hs) hs) ih

theorem mstep_lrec {v e1 e2 : Core.Exp} {l : String}
    (h : MStep v e1 e2)
    : MStep v (.lrec l e1) (.lrec l e2) := by
  induction h with
  | refl hv => exact MStep.refl hv
  | step hs _ ih => exact MStep.step (Step.slrec (step_env_value hs) hs) ih

theorem mstep_rproj {v e1 e2 : Core.Exp} {l : String}
    (h : MStep v e1 e2)
    : MStep v (.rproj e1 l) (.rproj e2 l) := by
  induction h with
  | refl hv => exact MStep.refl hv
  | step hs _ ih => exact MStep.step (Step.srproj (step_env_value hs) hs) ih

theorem mstep_inl {v e1 e2 : Core.Exp} {B : Core.Typ}
    (h : MStep v e1 e2)
    : MStep v (.inl B e1) (.inl B e2) := by
  induction h with
  | refl hv => exact MStep.refl hv
  | step hs _ ih => exact MStep.step (Step.sinl (step_env_value hs) hs) ih

theorem mstep_inr {v e1 e2 : Core.Exp} {A : Core.Typ}
    (h : MStep v e1 e2)
    : MStep v (.inr A e1) (.inr A e2) := by
  induction h with
  | refl hv => exact MStep.refl hv
  | step hs _ ih => exact MStep.step (Step.sinr (step_env_value hs) hs) ih

theorem mstep_case {v e e' e1 e2 : Core.Exp}
    (h : MStep v e e')
    : MStep v (.case e e1 e2) (.case e' e1 e2) := by
  induction h with
  | refl hv => exact MStep.refl hv
  | step hs _ ih => exact MStep.step (Step.scase (step_env_value hs) hs) ih

theorem mstep_fold {v e1 e2 : Core.Exp} {T : Core.Typ}
    (h : MStep v e1 e2)
    : MStep v (.fold T e1) (.fold T e2) := by
  induction h with
  | refl hv => exact MStep.refl hv
  | step hs _ ih => exact MStep.step (Step.sfold (step_env_value hs) hs) ih

theorem mstep_unfold {v e1 e2 : Core.Exp}
    (h : MStep v e1 e2)
    : MStep v (.unfold e1) (.unfold e2) := by
  induction h with
  | refl hv => exact MStep.refl hv
  | step hs _ ih => exact MStep.step (Step.sunfold (step_env_value hs) hs) ih

-- Soundness: big-step → multi-step
theorem ebig_sound {env e v : Core.Exp}
    (h : EBig env e v)
    : MStep env e v := by
  induction h with
  | ebunit hv =>
    rename_i v'
    exact MStep.refl hv
  | eblit hv =>
    rename_i v' n
    exact MStep.refl hv
  | equery hv =>
    rename_i e'
    apply MStep.step
    · exact Step.squery hv
    · apply MStep.refl hv
  | ebmrg hb1 hb2 ih1 ih2 =>
    rename_i v' e1 e2 v1 v2
    have hv := mstep_env_value ih1
    have hv1 := ebig_produces_value hv hb1
    exact mstep_trans (mstep_mrg_left ih1 _) (mstep_mrg_right hv hv1 ih2)
  | ebclos hv =>
    rename_i v' A e'
    apply MStep.step
    · apply Step.sclos <;> try assumption
    · apply MStep.refl hv
  | ebapp hb1 hb2 hb3 ih1 ih2 ih3 =>
    have hv := ebig_env_value hb1
    have hv1 := ebig_produces_value hv hb1  -- Value (clos v3 A v5)
    have hv2 := ebig_produces_value hv hb2  -- Value e2
    have hv4 := ebig_produces_value (Value.vmrg (by cases hv1; assumption) hv2) hb3
    cases hv1 with
    | vclos hv3 =>
      exact mstep_trans (mstep_app_left ih1 _)
        (mstep_trans (mstep_app_right (.vclos hv3) ih2)
          (mstep_trans
            (MStep.step (Step.sbeta hv hv2 hv3) (MStep.refl hv))
            (box_mstep_drop_env ih3 hv4 hv)))
  | ebbox hb1 hb2 ih1 ih2 =>
    have hv' := ebig_env_value hb1
    have hv2 := ebig_produces_value (ebig_produces_value hv' hb1) hb2
    exact mstep_trans (mstep_box_left ih1 _) (box_mstep_drop_env ih2 hv2 hv')
  | eclos hv1 hv2 =>
    exact MStep.refl hv1
  | ebproj ib ilookup ih =>
    have hv := ebig_env_value ib
    have hv' := ebig_produces_value hv ib
    exact mstep_trans (mstep_proj ih) (MStep.step (Step.sprojv hv hv' ilookup) (MStep.refl hv))
  | ebrec ib ih =>
    exact mstep_lrec ih
  | ebsel ib ilookup ih =>
    have hv := ebig_env_value ib
    have hv' := ebig_produces_value hv ib
    exact mstep_trans (mstep_rproj ih) (MStep.step (Step.srprojv hv hv' ilookup) (MStep.refl hv))
  | ebinl ib ih => exact mstep_inl ih
  | ebinr ib ih => exact mstep_inr ih
  | ebcasel ib1 ib2 ih1 ih2 =>
    have hv := ebig_env_value ib1
    have hinl := ebig_produces_value hv ib1
    cases hinl with
    | vinl hv1 =>
      have hvr := ebig_produces_value (Value.vmrg hv hv1) ib2
      exact mstep_trans (mstep_case ih1)
        (MStep.step (Step.scasel hv hv1) (box_mstep_drop_env ih2 hvr hv))
  | ebcaser ib1 ib2 ih1 ih2 =>
    have hv := ebig_env_value ib1
    have hinr := ebig_produces_value hv ib1
    cases hinr with
    | vinr hv1 =>
      have hvr := ebig_produces_value (Value.vmrg hv hv1) ib2
      exact mstep_trans (mstep_case ih1)
        (MStep.step (Step.scaser hv hv1) (box_mstep_drop_env ih2 hvr hv))
  | ebflam hv => exact MStep.step (Step.sfclos hv) (MStep.refl hv)
  | efclos hv hv1 => exact MStep.refl hv
  | ebfapp hb1 hb2 hb3 ih1 ih2 ih3 =>
    have hv := ebig_env_value hb1
    have hv1 := ebig_produces_value hv hb1  -- Value (fclos v2 A B e)
    have hv2 := ebig_produces_value hv hb2
    cases hv1 with
    | vfclos hv3 =>
      have hv4 := ebig_produces_value
        (Value.vmrg (Value.vmrg hv3 (Value.vfclos hv3)) hv2) hb3
      exact mstep_trans (mstep_app_left ih1 _)
        (mstep_trans (mstep_app_right (.vfclos hv3) ih2)
          (mstep_trans
            (MStep.step (Step.sfbeta hv hv2 hv3) (MStep.refl hv))
            (box_mstep_drop_env ih3 hv4 hv)))
  | ebfold ib ih => exact mstep_fold ih
  | ebunfold ib ih =>
    have hv := ebig_env_value ib
    have hfold := ebig_produces_value hv ib
    cases hfold with
    | vfold hv1 =>
      exact mstep_trans (mstep_unfold ih)
        (MStep.step (Step.sunfoldv hv hv1) (MStep.refl hv))

theorem ebig_value_refl {e v : Core.Exp}
    (hve : Core.Value e) (hvv : Core.Value v)
    : EBig v e e := by
  induction hve generalizing v with
  | vint => exact EBig.eblit hvv
  | vunit => exact EBig.ebunit hvv
  | vclos hv' => exact EBig.eclos hvv hv'
  | vrcd hv' ih => exact EBig.ebrec (ih hvv)
  | vinl hv' ih => exact EBig.ebinl (ih hvv)
  | vinr hv' ih => exact EBig.ebinr (ih hvv)
  | vfclos hv' ih => exact EBig.efclos hvv hv'
  | vfold hv' ih => exact EBig.ebfold (ih hvv)
  | vmrg hv1 hv2 ih1 ih2 =>
    have h1 := ih1 hvv
    exact EBig.ebmrg h1 (ih2 (Value.vmrg hvv (ebig_produces_value hvv h1)))

-- Determinism for values
theorem ebig_val_det {env e v1 : Core.Exp}
    (h1 : EBig env e v1) (hv : Core.Value e)
    {v2 : Core.Exp} (h2 : EBig env e v2)
    : v1 = v2 := by
  induction h1 generalizing v2 with
  | eblit _ => cases h2; rfl
  | ebunit _ => cases h2; rfl
  | eclos _ _ => cases h2; rfl
  | efclos _ _ => cases h2; rfl
  | equery _ => cases hv
  | ebclos _ => cases hv
  | ebflam _ => cases hv
  | ebapp _ _ _ _ _ _ => cases hv
  | ebfapp _ _ _ _ _ _ => cases hv
  | ebbox _ _ _ _ => cases hv
  | ebproj _ _ _ => cases hv
  | ebsel _ _ _ => cases hv
  | ebcasel _ _ _ _ => cases hv
  | ebcaser _ _ _ _ => cases hv
  | ebunfold _ _ => cases hv
  | ebfold hb1 ih1 =>
    cases hv with
    | vfold hv' =>
      cases h2 with
      | ebfold hb2 =>
        congr 1
        exact ih1 hv' hb2
  | ebinl hb1 ih1 =>
    cases hv with
    | vinl hv' =>
      cases h2 with
      | ebinl hb2 =>
        congr 1
        exact ih1 hv' hb2
  | ebinr hb1 ih1 =>
    cases hv with
    | vinr hv' =>
      cases h2 with
      | ebinr hb2 =>
        congr 1
        exact ih1 hv' hb2
  | ebrec hb1 ih1 =>
    cases hv with
    | vrcd hv' =>
      cases h2 with
      | ebrec hb2 =>
        congr 1
        exact ih1 hv' hb2
  | ebmrg hb1 hb2 ih1 ih2 =>
    cases hv with
    | vmrg hv1 hv2 =>
      cases h2 with
      | ebmrg hb1' hb2' =>
        have heq1 := ih1 hv1 hb1'
        subst heq1
        have heq2 := ih2 hv2 hb2'
        subst heq2
        rfl

-- Values big-step to themselves
theorem ebig_value_eq {env v e : Core.Exp}
    (h : EBig env v e) (hv : Core.Value v)
    : v = e := by
  have henv := ebig_env_value h
  exact ebig_val_det (ebig_value_refl hv henv) hv h

-- If e steps to e', and e' big-steps to v, then e big-steps to v
theorem step_ebig {env e1 e2 v : Core.Exp}
    (hs : Step env e1 e2) (hb : EBig env e2 v)
    : EBig env e1 v := by
  induction hs generalizing v with
  | squery hv =>
      rename_i v'
      have hvt := ebig_value_eq hb hv
      rw [hvt]
      apply EBig.equery
      rw [← hvt]; assumption
  | sappl hv hstep ih =>
    rename_i v' e1' e1'' e2'
    cases hb with
    | ebapp hb1 hb2 hb3 =>
      rename_i v1' v2' e'' A
      apply EBig.ebapp <;> try assumption
      apply ih
      assumption
    | ebfapp hb1 hb2 hb3 =>
      exact EBig.ebfapp (ih hb1) hb2 hb3
  | sboxl hv hstep ih =>
    rename_i v' e1' e1'' e2'
    cases hb with
    | ebbox ib1 ib2 =>
      rename_i v2'
      have ib3 := ih ib1
      apply EBig.ebbox <;> try assumption
  | smrgl hv hstep ih =>
    cases hb with
    | ebmrg hb1 hb2 =>
      exact EBig.ebmrg (ih hb1) hb2
  | sappr hv1 hv2 hstep ih =>
    cases hb with
    | ebapp hb1 hb2 hb3 =>
      exact EBig.ebapp hb1 (ih hb2) hb3
    | ebfapp hb1 hb2 hb3 =>
      exact EBig.ebfapp hb1 (ih hb2) hb3
  | sboxr hv hv1 hstep ih =>
    cases hb with
    | ebbox hb1 hb2 =>
      have heq := ebig_value_eq hb1 hv1
      subst heq
      exact EBig.ebbox hb1 (ih hb2)
  | smrgr hv hv1 hstep ih =>
    cases hb with
    | ebmrg hb1 hb2 =>
      have heq := ebig_value_eq hb1 hv1
      subst heq
      exact EBig.ebmrg hb1 (ih hb2)
  | sclos hv =>
    rename_i v' A e'
    cases hb with
    | eclos hv1 hv2 =>
      exact EBig.ebclos hv
  | sbeta hv1 hv2 hv3 =>
    -- hb : EBig env (.box (.mrg v2 v1) e) v
    cases hb with
    | ebbox hb1 hb2 =>
      -- hb1 : EBig env (.mrg v2 v1) v1', hb2 : EBig v1' e v
      -- (.mrg v2 v1) is a value, so v1' = .mrg v2 v1
      have heq := ebig_value_eq hb1 (Value.vmrg hv3 hv2)
      subst heq
      exact EBig.ebapp (EBig.eclos hv1 hv3) (ebig_value_refl hv2 hv1) hb2
  | sboxv hv hv1 hv2 =>
    -- hb : EBig env v2 v, where v2 is a value, so v = v2
    have heq := ebig_value_eq hb hv2
    subst heq
    exact EBig.ebbox (ebig_value_refl hv1 hv) (ebig_value_refl hv2 hv1)
  | sproj hv hstep ih =>
    cases hb with
    | ebproj hb1 hlook =>
      exact EBig.ebproj (ih hb1) hlook
  | sprojv hv hv1 hlook =>
    have heq := ebig_value_eq hb (lookupv_value hlook hv1)
    subst heq
    exact EBig.ebproj (ebig_value_refl hv1 hv) hlook
  | slrec hv hstep ih =>
    cases hb with
    | ebrec hb1 =>
      exact EBig.ebrec (ih hb1)
  | srproj hv hstep ih =>
    cases hb with
    | ebsel hb1 hlook =>
      exact EBig.ebsel (ih hb1) hlook
  | srprojv hv hv1 hlook =>
    have heq := ebig_value_eq hb (rlookupv_value hlook hv1)
    subst heq
    exact EBig.ebsel (ebig_value_refl hv1 hv) hlook
  | sinl hv hstep ih =>
    cases hb with
    | ebinl hb1 =>
      exact EBig.ebinl (ih hb1)
  | sinr hv hstep ih =>
    cases hb with
    | ebinr hb1 =>
      exact EBig.ebinr (ih hb1)
  | scase hv hstep ih =>
    cases hb with
    | ebcasel hb1 hb2 => exact EBig.ebcasel (ih hb1) hb2
    | ebcaser hb1 hb2 => exact EBig.ebcaser (ih hb1) hb2
  | scasel hv hv1 =>
    -- hb : EBig env (.box (.mrg env v1) e1) v
    cases hb with
    | ebbox hb1 hb2 =>
      have heq := ebig_value_eq hb1 (Value.vmrg hv hv1)
      subst heq
      exact EBig.ebcasel (ebig_value_refl (Value.vinl hv1) hv) hb2
  | scaser hv hv1 =>
    cases hb with
    | ebbox hb1 hb2 =>
      have heq := ebig_value_eq hb1 (Value.vmrg hv hv1)
      subst heq
      exact EBig.ebcaser (ebig_value_refl (Value.vinr hv1) hv) hb2
  | sfclos hv =>
    cases hb with
    | efclos hv1 hv2 => exact EBig.ebflam hv
  | sfbeta hv hv1 hv2 =>
    -- hb : EBig env (.box (.mrg (.mrg v2 (fclos v2 A B e)) v1) e) v
    cases hb with
    | ebbox hb1 hb2 =>
      have heq := ebig_value_eq hb1 (Value.vmrg (Value.vmrg hv2 (Value.vfclos hv2)) hv1)
      subst heq
      exact EBig.ebfapp (EBig.efclos hv hv2) (ebig_value_refl hv1 hv) hb2
  | sfold hv hstep ih =>
    cases hb with
    | ebfold hb1 => exact EBig.ebfold (ih hb1)
  | sunfold hv hstep ih =>
    cases hb with
    | ebunfold hb1 => exact EBig.ebunfold (ih hb1)
  | sunfoldv hv hv1 =>
    -- hb : EBig env v1 v, where v1 is a value
    have heq := ebig_value_eq hb hv1
    subst heq
    exact EBig.ebunfold (ebig_value_refl (Value.vfold hv1) hv)

-- Completeness: multi-step + value → big-step
theorem ebig_complete {env e v : Core.Exp}
    (hm : MStep env e v) (hv : Core.Value v)
    : EBig env e v := by
  induction hm with
  | refl hv_env => exact ebig_value_refl hv hv_env
  | step hs _ ih => exact step_ebig hs (ih hv)

-- Equivalence
theorem step_ebig_eq {env a v : Core.Exp}
    : EBig env a v ↔ (Core.Value v ∧ MStep env a v) := by
  constructor
  · intro h; exact ⟨ebig_produces_value (ebig_env_value h) h, ebig_sound h⟩
  · intro ⟨hv, hm⟩; exact ebig_complete hm hv
