import LeanSce.SCE.Semantics.SmallStep
import LeanSce.SCE.Semantics.BigStep
import LeanSce.SCE.Syntax

open SCE S_Sem

-- Multi-step relation for SCE
inductive SMStep : Exp → Exp → Exp → Prop where
  | refl {v e : Exp}
    : Value v
    → SMStep v e e
  | step {v e e' e'' : Exp}
    : SStep v e e'
    → SMStep v e' e''
    → SMStep v e e''

-- BStep produces values (delegates to existing theorem in Theories)
theorem sbig_produces_value
    {v e v' : Exp}
    (hval : Value v)
    (hbig : BStep v e v')
    : Value v' := eval_produces_value hval hbig

-- BStep env is always a value (every BStep constructor requires Value ρ)
theorem sbig_env_value {env e v : Exp} (h : BStep env e v) : Value env := by
  cases h <;> assumption

-- SStep implies env is a value
theorem sstep_env_value {v e e' : Exp} (h : SStep v e e') : Value v := by
  cases h <;> assumption

-- SMStep implies env is a value
theorem smstep_env_value {v e e' : Exp} (h : SMStep v e e') : Value v := by
  cases h with
  | refl hv => exact hv
  | step hs _ => exact sstep_env_value hs

-- Multi-step transitivity
theorem smstep_trans {v e1 e2 e3 : Exp}
    (h1 : SMStep v e1 e2) (h2 : SMStep v e2 e3) : SMStep v e1 e3 := by
  induction h1 with
  | refl _ => assumption
  | step hs _ ih => exact SMStep.step hs (ih h2)

-- Congruence: mrg left
theorem smstep_mrg_left {v e1 e1' : Exp}
    (h : SMStep v e1 e1') (e2 : Exp)
    : SMStep v (.mrg e1 e2) (.mrg e1' e2) := by
  induction h with
  | refl hv => exact SMStep.refl hv
  | step hs _ ih => exact SMStep.step (SStep.ssmrgl (sstep_env_value hs) hs) ih

-- Congruence: mrg right
theorem smstep_mrg_right {v v1 e2 e2' : Exp}
    (hv : Value v) (hv1 : Value v1)
    (h : SMStep (.mrg v v1) e2 e2')
    : SMStep v (.mrg v1 e2) (.mrg v1 e2') := by
  induction h with
  | refl _ => exact SMStep.refl hv
  | step hs _ ih => exact SMStep.step (SStep.ssmrgr hv hv1 hs) ih

-- Congruence: app left
theorem smstep_app_left {v e1 e1' : Exp}
    (h : SMStep v e1 e1') (e2 : Exp)
    : SMStep v (.app e1 e2) (.app e1' e2) := by
  induction h with
  | refl hv => exact SMStep.refl hv
  | step hs _ ih => exact SMStep.step (SStep.ssappl (sstep_env_value hs) hs) ih

-- Congruence: app right
theorem smstep_app_right {v v1 e2 e2' : Exp}
    (hv1 : Value v1)
    (h : SMStep v e2 e2')
    : SMStep v (.app v1 e2) (.app v1 e2') := by
  induction h with
  | refl hv => exact SMStep.refl hv
  | step hs _ ih => exact SMStep.step (SStep.ssappr (sstep_env_value hs) hv1 hs) ih

-- Congruence: box left
theorem smstep_box_left {v e1 e1' : Exp}
    (h : SMStep v e1 e1') (e2 : Exp)
    : SMStep v (.box e1 e2) (.box e1' e2) := by
  induction h with
  | refl hv => exact SMStep.refl hv
  | step hs _ ih => exact SMStep.step (SStep.ssboxl (sstep_env_value hs) hs) ih

-- Congruence: box right
theorem smstep_box_right {v v1 e2 e2' : Exp}
    (hv : Value v) (hv1 : Value v1)
    (h : SMStep v1 e2 e2')
    : SMStep v (.box v1 e2) (.box v1 e2') := by
  induction h with
  | refl _ => exact SMStep.refl hv
  | step hs _ ih => exact SMStep.step (SStep.ssboxr hv hv1 hs) ih

-- Box env drop
theorem sbox_mstep_drop_env {e e1 v2 : Exp}
    (hm : SMStep e e1 v2) (hv2 : Value v2)
    {v : Exp} (hv : Value v)
    : SMStep v (.box e e1) v2 := by
  have hve := smstep_env_value hm
  exact smstep_trans
    (smstep_box_right hv hve hm)
    (SMStep.step (SStep.ssboxv hv hve hv2) (SMStep.refl hv))

-- Congruence: proj
theorem smstep_proj {v e1 e2 : Exp} {n : Nat}
    (h : SMStep v e1 e2)
    : SMStep v (.proj e1 n) (.proj e2 n) := by
  induction h with
  | refl hv => exact SMStep.refl hv
  | step hs _ ih => exact SMStep.step (SStep.ssproj (sstep_env_value hs) hs) ih

-- Congruence: lrec
theorem smstep_lrec {v e1 e2 : Exp} {l : String}
    (h : SMStep v e1 e2)
    : SMStep v (.lrec l e1) (.lrec l e2) := by
  induction h with
  | refl hv => exact SMStep.refl hv
  | step hs _ ih => exact SMStep.step (SStep.sslrec (sstep_env_value hs) hs) ih

-- Congruence: rproj
theorem smstep_rproj {v e1 e2 : Exp} {l : String}
    (h : SMStep v e1 e2)
    : SMStep v (.rproj e1 l) (.rproj e2 l) := by
  induction h with
  | refl hv => exact SMStep.refl hv
  | step hs _ ih => exact SMStep.step (SStep.ssrproj (sstep_env_value hs) hs) ih

-- Congruence: structures evaluate their bodies in the ambient environment.
theorem smstep_mstruct {v e1 e2 : Exp}
    (h : SMStep v e1 e2)
    : SMStep v (.mstruct e1) (.mstruct e2) := by
  induction h with
  | refl hv => exact SMStep.refl hv
  | step hs _ ih => exact SMStep.step (SStep.ssmstruct (sstep_env_value hs) hs) ih

-- Congruence: mapp left
theorem smstep_mapp_left {v e1 e1' : Exp}
    (h : SMStep v e1 e1') (e2 : Exp)
    : SMStep v (.mapp e1 e2) (.mapp e1' e2) := by
  induction h with
  | refl hv => exact SMStep.refl hv
  | step hs _ ih => exact SMStep.step (SStep.ssmappl (sstep_env_value hs) hs) ih

-- Congruence: mapp right
theorem smstep_mapp_right {v v1 e2 e2' : Exp}
    (hv1 : Value v1)
    (h : SMStep v e2 e2')
    : SMStep v (.mapp v1 e2) (.mapp v1 e2') := by
  induction h with
  | refl hv => exact SMStep.refl hv
  | step hs _ ih => exact SMStep.step (SStep.ssmappr (sstep_env_value hs) hv1 hs) ih

-- Congruence: nmrg left
theorem smstep_nmrg_left {v e1 e1' : Exp}
    (h : SMStep v e1 e1') (e2 : Exp)
    : SMStep v (.nmrg e1 e2) (.nmrg e1' e2) := by
  induction h with
  | refl hv => exact SMStep.refl hv
  | step hs _ ih => exact SMStep.step (SStep.ssnmrgl (sstep_env_value hs) hs) ih

-- Congruence: nmrg right
theorem smstep_nmrg_right {v v1 e2 e2' : Exp}
    (hv : Value v) (hv1 : Value v1)
    (h : SMStep v e2 e2')
    : SMStep v (.nmrg v1 e2) (.nmrg v1 e2') := by
  induction h with
  | refl _ => exact SMStep.refl hv
  | step hs _ ih => exact SMStep.step (SStep.ssnmrgr hv hv1 hs) ih

-- Congruence: letb
theorem smstep_letb {v e1 e1' : Exp}
    (h : SMStep v e1 e1') (e2 : Exp)
    : SMStep v (.letb e1 e2) (.letb e1' e2) := by
  induction h with
  | refl hv => exact SMStep.refl hv
  | step hs _ ih => exact SMStep.step (SStep.ssletbl (sstep_env_value hs) hs) ih

-- Congruence: mlink left
theorem smstep_mlink_left {v e1 e1' : Exp}
    (h : SMStep v e1 e1') (e2 : Exp)
    : SMStep v (.mlink e1 e2) (.mlink e1' e2) := by
  induction h with
  | refl hv => exact SMStep.refl hv
  | step hs _ ih => exact SMStep.step (SStep.ssmlinkl (sstep_env_value hs) hs) ih

-- Congruence: mlink right
theorem smstep_mlink_right {v v1 e2 e2' : Exp}
    (hv1 : Value v1)
    (h : SMStep v e2 e2')
    : SMStep v (.mlink v1 e2) (.mlink v1 e2') := by
  induction h with
  | refl hv => exact SMStep.refl hv
  | step hs _ ih => exact SMStep.step (SStep.ssmlinkr (sstep_env_value hs) hv1 hs) ih

-- Congruence: mlinkn left
theorem smstep_mlinkn_left {v e1 e1' : Exp}
    (h : SMStep v e1 e1') (e2 : Exp)
    : SMStep v (.mlinkn e1 e2) (.mlinkn e1' e2) := by
  induction h with
  | refl hv => exact SMStep.refl hv
  | step hs _ ih => exact SMStep.step (SStep.ssmlinknl (sstep_env_value hs) hs) ih

-- Congruence: mlinkn right
theorem smstep_mlinkn_right {v v1 e2 e2' : Exp}
    (hv1 : Value v1)
    (h : SMStep v e2 e2')
    : SMStep v (.mlinkn v1 e2) (.mlinkn v1 e2') := by
  induction h with
  | refl hv => exact SMStep.refl hv
  | step hs _ ih => exact SMStep.step (SStep.ssmlinknr (sstep_env_value hs) hv1 hs) ih

-- Congruence: openm
theorem smstep_openm {v e1 e1' : Exp}
    (h : SMStep v e1 e1') (e2 : Exp)
    : SMStep v (.openm e1 e2) (.openm e1' e2) := by
  induction h with
  | refl hv => exact SMStep.refl hv
  | step hs _ ih => exact SMStep.step (SStep.ssopenml (sstep_env_value hs) hs) ih

-- Congruence: inl
theorem smstep_inl {v e1 e2 : Exp} {B : Typ}
    (h : SMStep v e1 e2)
    : SMStep v (.inl B e1) (.inl B e2) := by
  induction h with
  | refl hv => exact SMStep.refl hv
  | step hs _ ih => exact SMStep.step (SStep.ssinl (sstep_env_value hs) hs) ih

-- Congruence: inr
theorem smstep_inr {v e1 e2 : Exp} {A : Typ}
    (h : SMStep v e1 e2)
    : SMStep v (.inr A e1) (.inr A e2) := by
  induction h with
  | refl hv => exact SMStep.refl hv
  | step hs _ ih => exact SMStep.step (SStep.ssinr (sstep_env_value hs) hs) ih

-- Congruence: case scrutinee
theorem smstep_case {v e e' e1 e2 : Exp}
    (h : SMStep v e e')
    : SMStep v (.case e e1 e2) (.case e' e1 e2) := by
  induction h with
  | refl hv => exact SMStep.refl hv
  | step hs _ ih => exact SMStep.step (SStep.sscase (sstep_env_value hs) hs) ih

-- Congruence: fold
theorem smstep_fold {v e1 e2 : Exp} {T : Typ}
    (h : SMStep v e1 e2)
    : SMStep v (.fold T e1) (.fold T e2) := by
  induction h with
  | refl hv => exact SMStep.refl hv
  | step hs _ ih => exact SMStep.step (SStep.ssfold (sstep_env_value hs) hs) ih

-- Congruence: unfold
theorem smstep_unfold {v e1 e2 : Exp}
    (h : SMStep v e1 e2)
    : SMStep v (.unfold e1) (.unfold e2) := by
  induction h with
  | refl hv => exact SMStep.refl hv
  | step hs _ ih => exact SMStep.step (SStep.ssunfold (sstep_env_value hs) hs) ih

-- Soundness: big-step → multi-step (simple cases filled)
theorem sbig_sound {env e v : Exp}
    (h : BStep env e v)
    : SMStep env e v := by
  induction h with
  | lit hv => exact SMStep.refl hv
  | unit hv => exact SMStep.refl hv
  | query hv =>
    exact SMStep.step (SStep.ssquery hv) (SMStep.refl hv)
  | clos_val hv hv1 => exact SMStep.refl hv
  | lam hv =>
    exact SMStep.step (SStep.ssclos hv) (SMStep.refl hv)
  | box hv hb1 hb2 ih1 ih2 =>
    have hv1 := sbig_produces_value hv hb1
    have hv2 := sbig_produces_value hv1 hb2
    exact smstep_trans (smstep_box_left ih1 _) (sbox_mstep_drop_env ih2 hv2 hv)
  | app_clos hv hb1 hb2 hb3 ih1 ih2 ih3 =>
    have hv1 := sbig_produces_value hv hb1
    have hv2 := sbig_produces_value hv hb2
    have hv3 := sbig_produces_value (Value.vmrg (by cases hv1; assumption) hv2) hb3
    cases hv1 with
    | vclos hvc =>
      exact smstep_trans (smstep_app_left ih1 _)
        (smstep_trans (smstep_app_right (.vclos hvc) ih2)
          (smstep_trans
            (SMStep.step (SStep.ssbeta hv hv2 hvc) (SMStep.refl hv))
            (sbox_mstep_drop_env ih3 hv3 hv)))
  | dmrg hv hb1 hb2 ih1 ih2 =>
    have hv1 := sbig_produces_value hv hb1
    exact smstep_trans (smstep_mrg_left ih1 _) (smstep_mrg_right hv hv1 ih2)
  | proj hv hb hlook ih =>
    have hv' := sbig_produces_value hv hb
    exact smstep_trans (smstep_proj ih) (SMStep.step (SStep.ssprojv hv hv' hlook) (SMStep.refl hv))
  | lrec hv hb ih => exact smstep_lrec ih
  | rproj hv hb hsel ih =>
    have hv' := sbig_produces_value hv hb
    exact smstep_trans (smstep_rproj ih) (SMStep.step (SStep.ssrprojv hv hv' hsel) (SMStep.refl hv))
  -- Non-lambdaE cases: no SStep rules yet
  | mclos_val hv hv1 => exact SMStep.refl hv
  | app_mclos hv hb1 hb2 hb3 ih1 ih2 ih3 =>
    have hv1 := sbig_produces_value hv hb1
    have hv2 := sbig_produces_value hv hb2
    have hv3 := sbig_produces_value (Value.vmrg (by cases hv1; assumption) hv2) hb3
    cases hv1 with
    | vmclos hvc =>
      exact smstep_trans (smstep_mapp_left ih1 _)
        (smstep_trans (smstep_mapp_right (.vmclos hvc) ih2)
          (smstep_trans
            (SMStep.step (SStep.ssmbeta hv hv2 hvc) (SMStep.refl hv))
            (sbox_mstep_drop_env ih3 hv3 hv)))
  | nmrg hv hb1 hb2 ih1 ih2 =>
    have hv1 := sbig_produces_value hv hb1
    have hv2 := sbig_produces_value hv hb2
    exact smstep_trans (smstep_nmrg_left ih1 _)
      (smstep_trans (smstep_nmrg_right hv hv1 ih2)
        (SMStep.step (SStep.ssnmrgv hv hv1 hv2) (SMStep.refl hv)))
  | letb hv hb1 hb2 ih1 ih2 =>
    have hv1 := sbig_produces_value hv hb1
    have hv2 := sbig_produces_value (Value.vmrg hv hv1) hb2
    exact smstep_trans (smstep_letb ih1 _)
      (smstep_trans
        (SMStep.step (SStep.ssletbv hv hv1) (SMStep.refl hv))
        (sbox_mstep_drop_env ih2 hv2 hv))
  | openm hv hb1 hb2 ih1 ih2 =>
    have hv1 := sbig_produces_value hv hb1
    cases hv1 with
    | vlrec hv' =>
      have hv2 := sbig_produces_value (Value.vmrg hv hv') hb2
      exact smstep_trans (smstep_openm ih1 _)
        (smstep_trans
          (SMStep.step (SStep.ssopenm hv hv') (SMStep.refl hv))
          (sbox_mstep_drop_env ih2 hv2 hv))
  | mstruct hv hb ih =>
    exact smstep_mstruct ih
  | mfunctor_sandboxed hv =>
    exact SMStep.step (SStep.ssmfunctor_sandboxed hv) (SMStep.refl hv)
  | mfunctor_open hv =>
    exact SMStep.step (SStep.ssmfunctor_open hv) (SMStep.refl hv)
  | mlink hv hb1 hb2 hsel hb3 ih1 ih2 ih3 =>
    have hv1 := sbig_produces_value hv hb1
    have hv2 := sbig_produces_value hv hb2
    cases hv2 with
    | vmclos hvc =>
      have hvl := source_sel_value hv1 hsel
      have hv3 := sbig_produces_value (Value.vmrg hvc (Value.vlrec hvl)) hb3
      exact smstep_trans (smstep_mlink_left ih1 _)
        (smstep_trans (smstep_mlink_right hv1 ih2)
          (smstep_trans
            (SMStep.step (SStep.ssmlinkbeta hv hv1 hvc hsel) (SMStep.refl hv))
            (smstep_mrg_right hv hv1 (sbox_mstep_drop_env ih3 hv3 (Value.vmrg hv hv1)))))
  | mlinkn hv hb1 hb2 hsp hb3 ih1 ih2 ih3 =>
    have hv1 := sbig_produces_value hv hb1
    have hv2 := sbig_produces_value hv hb2
    cases hv2 with
    | vmclos hvc =>
      have hvpkg := selpkg_value hsp hv1
      have hv3 := sbig_produces_value (Value.vmrg hvc hvpkg) hb3
      exact smstep_trans (smstep_mlinkn_left ih1 _)
        (smstep_trans (smstep_mlinkn_right hv1 ih2)
          (smstep_trans
            (SMStep.step (SStep.ssmlinknbeta hv hv1 hvc hsp) (SMStep.refl hv))
            (smstep_mrg_right hv hv1 (sbox_mstep_drop_env ih3 hv3 (Value.vmrg hv hv1)))))
  | inl hv hb ih => exact smstep_inl ih
  | inr hv hb ih => exact smstep_inr ih
  | case_inl hv hb1 hb2 ih1 ih2 =>
    have hinl := sbig_produces_value hv hb1
    cases hinl with
    | vinl hv1 =>
      have hv2 := sbig_produces_value (Value.vmrg hv hv1) hb2
      exact smstep_trans (smstep_case ih1)
        (SMStep.step (SStep.sscasel hv hv1) (sbox_mstep_drop_env ih2 hv2 hv))
  | case_inr hv hb1 hb2 ih1 ih2 =>
    have hinr := sbig_produces_value hv hb1
    cases hinr with
    | vinr hv1 =>
      have hv2 := sbig_produces_value (Value.vmrg hv hv1) hb2
      exact smstep_trans (smstep_case ih1)
        (SMStep.step (SStep.sscaser hv hv1) (sbox_mstep_drop_env ih2 hv2 hv))
  | fclos_val hv hv1 => exact SMStep.refl hv
  | flam hv =>
    exact SMStep.step (SStep.ssfclos hv) (SMStep.refl hv)
  | app_fclos hv hb1 hb2 hb3 ih1 ih2 ih3 =>
    have hv1 := sbig_produces_value hv hb1
    have hv2 := sbig_produces_value hv hb2
    cases hv1 with
    | vfclos hvc =>
      have hv3 := sbig_produces_value
        (Value.vmrg (Value.vmrg hvc (Value.vfclos hvc)) hv2) hb3
      exact smstep_trans (smstep_app_left ih1 _)
        (smstep_trans (smstep_app_right (.vfclos hvc) ih2)
          (smstep_trans
            (SMStep.step (SStep.ssfbeta hv hv2 hvc) (SMStep.refl hv))
            (sbox_mstep_drop_env ih3 hv3 hv)))
  | fold hv hb ih => exact smstep_fold ih
  | unfold hv hb ih =>
    have hfold := sbig_produces_value hv hb
    cases hfold with
    | vfold hv1 =>
      exact smstep_trans (smstep_unfold ih)
        (SMStep.step (SStep.ssunfoldv hv hv1) (SMStep.refl hv))

-- Values big-step to themselves
theorem sbig_value_refl {e v : Exp}
    (hve : Value e) (hvv : Value v)
    : BStep v e e := by
  induction hve generalizing v with
  | vint => exact BStep.lit hvv
  | vunit => exact BStep.unit hvv
  | vclos hv' => exact BStep.clos_val hvv hv'
  | vmclos hv' => exact BStep.mclos_val hvv hv'
  | vlrec hv' ih => exact BStep.lrec hvv (ih hvv)
  | vinl hv' ih => exact BStep.inl hvv (ih hvv)
  | vinr hv' ih => exact BStep.inr hvv (ih hvv)
  | vfclos hv' ih => exact BStep.fclos_val hvv hv'
  | vfold hv' ih => exact BStep.fold hvv (ih hvv)
  | vmstruct hv' ih => exact BStep.mstruct hvv (ih hvv)
  | vmrg hv1 hv2 ih1 ih2 =>
    have h1 := ih1 hvv
    exact BStep.dmrg hvv h1 (ih2 (Value.vmrg hvv (sbig_produces_value hvv h1)))

-- Determinism for values
theorem sbig_val_det {env e v1 : Exp}
    (h1 : BStep env e v1) (hv : Value e)
    {v2 : Exp} (h2 : BStep env e v2)
    : v1 = v2 := by
  induction h1 generalizing v2 with
  | lit _ => cases h2 <;> rfl
  | unit _ => cases h2 <;> rfl
  | clos_val _ _ => cases h2 <;> rfl
  | mclos_val _ _ => cases h2 <;> rfl
  | fclos_val _ _ => cases h2 <;> rfl
  | query _ => cases hv
  | lam _ => cases hv
  | flam _ => cases hv
  | app_fclos _ _ _ _ _ _ _ => cases hv
  | box _ _ _ _ _ => cases hv
  | app_clos _ _ _ _ _ _ _ => cases hv
  | app_mclos _ _ _ _ _ _ _ => cases hv
  | proj _ _ _ _ => cases hv
  | rproj _ _ _ _ => cases hv
  | letb _ _ _ _ _ => cases hv
  | openm _ _ _ _ _ => cases hv
  | mstruct _ _ ih1 =>
    cases hv with
    | vmstruct hv' =>
      cases h2 with
      | mstruct _ hb2 =>
        congr 1
        exact ih1 hv' hb2
  | mfunctor_sandboxed _ => cases hv
  | mfunctor_open _ => cases hv
  | mlink _ _ _ _ _ _ _ _ => cases hv
  | mlinkn _ _ _ _ _ _ _ _ => cases hv
  | nmrg _ _ _ _ _ => cases hv
  | case_inl _ _ _ _ _ => cases hv
  | case_inr _ _ _ _ _ => cases hv
  | unfold _ _ _ => cases hv
  | fold _ hb1 ih1 =>
    cases hv with
    | vfold hv' =>
      cases h2 with
      | fold _ hb2 =>
        congr 1
        exact ih1 hv' hb2
  | inl _ hb1 ih1 =>
    cases hv with
    | vinl hv' =>
      cases h2 with
      | inl _ hb2 =>
        congr 1
        exact ih1 hv' hb2
  | inr _ hb1 ih1 =>
    cases hv with
    | vinr hv' =>
      cases h2 with
      | inr _ hb2 =>
        congr 1
        exact ih1 hv' hb2
  | lrec _ _ ih1 =>
    cases hv with
    | vlrec hv' =>
      cases h2 with
      | lrec _ hb2 =>
        congr 1
        exact ih1 hv' hb2
  | dmrg _ hb1 hb2 ih1 ih2 =>
    cases hv with
    | vmrg hv1 hv2 =>
      cases h2 with
      | dmrg _ hb1' hb2' =>
        have heq1 := ih1 hv1 hb1'
        subst heq1
        have heq2 := ih2 hv2 hb2'
        subst heq2
        rfl

-- Values big-step to themselves (equality version)
theorem sbig_value_eq {env v e : Exp}
    (h : BStep env v e) (hv : Value v)
    : v = e := by
  have henv := sbig_env_value h
  exact sbig_val_det (sbig_value_refl hv henv) hv h

-- If e steps to e', and e' big-steps to v, then e big-steps to v
theorem sstep_sbig {env e1 e2 v : Exp}
    (hs : SStep env e1 e2) (hb : BStep env e2 v)
    : BStep env e1 v := by
  induction hs generalizing v with
  | ssquery hv =>
    have hvt := sbig_value_eq hb hv
    rw [hvt]
    exact BStep.query (by rw [← hvt]; exact sbig_env_value hb)
  | ssclos hv =>
    cases hb with
    | clos_val hv1 hv2 => exact BStep.lam hv
  | ssappl hv _ ih =>
    cases hb with
    | app_clos _ hb1 hb2 hb3 => exact BStep.app_clos hv (ih hb1) hb2 hb3
    | app_fclos _ hb1 hb2 hb3 => exact BStep.app_fclos hv (ih hb1) hb2 hb3
  | ssappr hv hv1 _ ih =>
    cases hb with
    | app_clos _ hb1 hb2 hb3 => exact BStep.app_clos hv hb1 (ih hb2) hb3
    | app_fclos _ hb1 hb2 hb3 => exact BStep.app_fclos hv hb1 (ih hb2) hb3
  | ssbeta hv hv1 hv2 =>
    cases hb with
    | box _ hb1 hb2 =>
      have heq := sbig_value_eq hb1 (Value.vmrg hv2 hv1)
      subst heq
      exact BStep.app_clos hv (BStep.clos_val hv hv2) (sbig_value_refl hv1 hv) hb2
  | ssboxl hv _ ih =>
    cases hb with
    | box _ hb1 hb2 => exact BStep.box hv (ih hb1) hb2
  | ssboxr hv hv1 _ ih =>
    cases hb with
    | box _ hb1 hb2 =>
      have heq := sbig_value_eq hb1 hv1
      subst heq
      exact BStep.box hv hb1 (ih hb2)
  | ssboxv hv hv1 hv2 =>
    have heq := sbig_value_eq hb hv2
    subst heq
    exact BStep.box hv (sbig_value_refl hv1 hv) (sbig_value_refl hv2 hv1)
  | ssmrgl hv _ ih =>
    cases hb with
    | dmrg _ hb1 hb2 => exact BStep.dmrg hv (ih hb1) hb2
  | ssmrgr hv hv1 _ ih =>
    cases hb with
    | dmrg _ hb1 hb2 =>
      have heq := sbig_value_eq hb1 hv1
      subst heq
      exact BStep.dmrg hv hb1 (ih hb2)
  | ssproj hv _ ih =>
    cases hb with
    | proj _ hb1 hlook => exact BStep.proj hv (ih hb1) hlook
  | ssprojv hv hv1 hlook =>
    have heq := sbig_value_eq hb (source_lookupv_value hv1 hlook)
    subst heq
    exact BStep.proj hv (sbig_value_refl hv1 hv) hlook
  | sslrec hv _ ih =>
    cases hb with
    | lrec _ hb1 => exact BStep.lrec hv (ih hb1)
  | ssrproj hv _ ih =>
    cases hb with
    | rproj _ hb1 hsel => exact BStep.rproj hv (ih hb1) hsel
  | ssrprojv hv hv1 hsel =>
    have heq := sbig_value_eq hb (source_sel_value hv1 hsel)
    subst heq
    exact BStep.rproj hv (sbig_value_refl hv1 hv) hsel
  | ssmstruct hv _ ih =>
    cases hb with
    | mstruct _ hb_body => exact BStep.mstruct hv (ih hb_body)
  | ssmfunctor_sandboxed hv =>
    cases hb with
    | mclos_val _ hv' => exact BStep.mfunctor_sandboxed hv
  | ssmfunctor_open hv =>
    cases hb with
    | mclos_val _ hv' => exact BStep.mfunctor_open hv
  | ssmappl hv _ ih =>
    cases hb with
    | app_mclos _ hb1 hb2 hb3 => exact BStep.app_mclos hv (ih hb1) hb2 hb3
  | ssmappr hv hv1 _ ih =>
    cases hb with
    | app_mclos _ hb1 hb2 hb3 => exact BStep.app_mclos hv hb1 (ih hb2) hb3
  | ssmbeta hv hv1 hv2 =>
    cases hb with
    | box _ hb1 hb2 =>
      have heq := sbig_value_eq hb1 (Value.vmrg hv2 hv1)
      subst heq
      exact BStep.app_mclos hv (BStep.mclos_val hv hv2) (sbig_value_refl hv1 hv) hb2
  | ssnmrgl hv _ ih =>
    cases hb with
    | nmrg _ hb1 hb2 => exact BStep.nmrg hv (ih hb1) hb2
  | ssnmrgr hv hv1 _ ih =>
    cases hb with
    | nmrg _ hb1 hb2 => exact BStep.nmrg hv hb1 (ih hb2)
  | ssnmrgv hv hv1 hv2 =>
    cases hb with
    | dmrg _ hb1 hb2 =>
      have heq1 := sbig_value_eq hb1 hv1; subst heq1
      have heq2 := sbig_value_eq hb2 hv2; subst heq2
      exact BStep.nmrg hv (sbig_value_refl hv1 hv) (sbig_value_refl hv2 hv)
  | ssletbl hv _ ih =>
    cases hb with
    | letb _ hb1 hb2 => exact BStep.letb hv (ih hb1) hb2
  | ssletbv hv hv1 =>
    cases hb with
    | box _ hb1 hb2 =>
      have heq := sbig_value_eq hb1 (Value.vmrg hv hv1)
      subst heq
      exact BStep.letb hv (sbig_value_refl hv1 hv) hb2
  | ssmlinkl hv _ ih =>
    cases hb with
    | mlink _ hb1 hb2 hsel hb3 => exact BStep.mlink hv (ih hb1) hb2 hsel hb3
  | ssmlinkr hv hv1 _ ih =>
    cases hb with
    | mlink _ hb1 hb2 hsel hb3 => exact BStep.mlink hv hb1 (ih hb2) hsel hb3
  | ssmlinkbeta hv hv1 hv2 hsel =>
    cases hb with
    | dmrg _ hb1 hb2 =>
      have heq := sbig_value_eq hb1 hv1; subst heq
      cases hb2 with
      | box _ hb_env hb_body =>
        have heq := sbig_value_eq hb_env (Value.vmrg hv2 (Value.vlrec (source_sel_value hv1 hsel)))
        subst heq
        exact BStep.mlink hv (sbig_value_refl hv1 hv) (BStep.mclos_val hv hv2) hsel hb_body
  | ssmlinknl hv _ ih =>
    cases hb with
    | mlinkn _ hb1 hb2 hsp hb3 => exact BStep.mlinkn hv (ih hb1) hb2 hsp hb3
  | ssmlinknr hv hv1 _ ih =>
    cases hb with
    | mlinkn _ hb1 hb2 hsp hb3 => exact BStep.mlinkn hv hb1 (ih hb2) hsp hb3
  | ssmlinknbeta hv hv1 hv2 hsp =>
    cases hb with
    | dmrg _ hb1 hb2 =>
      have heq := sbig_value_eq hb1 hv1; subst heq
      cases hb2 with
      | box _ hb_env hb_body =>
        have heq := sbig_value_eq hb_env (Value.vmrg hv2 (selpkg_value hsp hv1))
        subst heq
        exact BStep.mlinkn hv (sbig_value_refl hv1 hv) (BStep.mclos_val hv hv2) hsp hb_body
  | ssopenml hv _ ih =>
    cases hb with
    | openm _ hb1 hb2 => exact BStep.openm hv (ih hb1) hb2
  | ssopenm hv hv' =>
    cases hb with
    | box _ hb1 hb2 =>
      have heq := sbig_value_eq hb1 (Value.vmrg hv hv')
      subst heq
      exact BStep.openm hv (BStep.lrec hv (sbig_value_refl hv' hv)) hb2
  | ssinl hv _ ih =>
    cases hb with
    | inl _ hb1 => exact BStep.inl hv (ih hb1)
  | ssinr hv _ ih =>
    cases hb with
    | inr _ hb1 => exact BStep.inr hv (ih hb1)
  | sscase hv _ ih =>
    cases hb with
    | case_inl _ hb1 hb2 => exact BStep.case_inl hv (ih hb1) hb2
    | case_inr _ hb1 hb2 => exact BStep.case_inr hv (ih hb1) hb2
  | sscasel hv hv1 =>
    cases hb with
    | box _ hb1 hb2 =>
      have heq := sbig_value_eq hb1 (Value.vmrg hv hv1)
      subst heq
      exact BStep.case_inl hv (sbig_value_refl (Value.vinl hv1) hv) hb2
  | sscaser hv hv1 =>
    cases hb with
    | box _ hb1 hb2 =>
      have heq := sbig_value_eq hb1 (Value.vmrg hv hv1)
      subst heq
      exact BStep.case_inr hv (sbig_value_refl (Value.vinr hv1) hv) hb2
  | ssfclos hv =>
    cases hb with
    | fclos_val hv1 hv2 => exact BStep.flam hv
  | ssfbeta hv hv1 hv2 =>
    cases hb with
    | box _ hb1 hb2 =>
      have heq := sbig_value_eq hb1 (Value.vmrg (Value.vmrg hv2 (Value.vfclos hv2)) hv1)
      subst heq
      exact BStep.app_fclos hv (BStep.fclos_val hv hv2) (sbig_value_refl hv1 hv) hb2
  | ssfold hv _ ih =>
    cases hb with
    | fold _ hb1 => exact BStep.fold hv (ih hb1)
  | ssunfold hv _ ih =>
    cases hb with
    | unfold _ hb1 => exact BStep.unfold hv (ih hb1)
  | ssunfoldv hv hv1 =>
    have heq := sbig_value_eq hb hv1
    subst heq
    exact BStep.unfold hv (sbig_value_refl (Value.vfold hv1) hv)

-- Completeness: multi-step + value → big-step
theorem sbig_complete {env e v : Exp}
    (hm : SMStep env e v) (hv : Value v)
    : BStep env e v := by
  induction hm with
  | refl hv_env => exact sbig_value_refl hv hv_env
  | step hs _ ih => exact sstep_sbig hs (ih hv)

-- Equivalence
theorem sstep_sbig_eq {env a v : Exp}
    : BStep env a v ↔ (Value v ∧ SMStep env a v) := by
  constructor
  · intro h; exact ⟨sbig_produces_value (sbig_env_value h) h, sbig_sound h⟩
  · intro ⟨hv, hm⟩; exact sbig_complete hm hv
