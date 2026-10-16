import LeanSce.Core.Syntax
import LeanSce.Core.Typing.Typing
import LeanSce.Core.Semantics.BigStep
import LeanSce.Core.Semantics.Equivalence
import LeanSce.SCE.Syntax
import LeanSce.SCE.Semantics.BigStep
import LeanSce.SCE.Elaboration.Elaboration
import LeanSce.SCE.Elaboration.Preservation
import LeanSce.SCE.Preservation

/-!
Semantic preservation of elaboration: if a source term evaluates to a value,
its elaboration evaluates in Core to the elaboration of that value.  The
lookup/selection lemmas relate source and Core value lookups; the `*_eval`
lemmas evaluate the composition terms emitted by `nmrg`, `link`, `linkall`.
-/

open SCE Core

theorem sel_implies_label_in
    {v v' : SCE.Exp} {vc : Core.Exp} {A : SCE.Typ} {l : String}
    (hval : SCE.Value v)
    (helab : elabExp SCE.Typ.top v A vc)
    (hsel : S_Sem.Sel v l v')
    : SCE.LabelIn l A := by
  induction hsel generalizing A vc with
  | rcd =>
    cases hval with | vlrec hv =>
    cases helab with | elrec _ _ _ _ _ h =>
    exact SCE.LabelIn.rcd _ _
  | dmrg_left _ ih =>
    cases hval with | vmrg hv1 hv2 =>
    cases helab with | edmrg _ A' B' _ _ ce1 ce2 h1 h2 =>
    exact SCE.LabelIn.andl _ _ _ (ih hv1 h1)
  | dmrg_right _ ih =>
    cases hval with | vmrg hv1 hv2 =>
    cases helab with | edmrg _ A' B' _ _ ce1 ce2 h1 h2 =>
    exact SCE.LabelIn.andr _ _ _ (ih hv2 (elab_value_weaken h2 hv2 _))
  | nmrg_left => cases hval
  | nmrg_right => cases hval
  | mstruct _ ih =>
    cases hval with | vmstruct hv =>
    cases helab with
    | mstruct _ _ _ _ h => exact SCE.LabelIn.sig _ _ (ih hv h)

theorem lookup_preservation
    {v_e v' : SCE.Exp} {vc_e : Core.Exp} {A B : SCE.Typ} {i : Nat}
    (hval : SCE.Value v_e)
    (helab : elabExp SCE.Typ.top v_e A vc_e)
    (hlook : S_Sem.LookupV v_e i v')
    (htyp_look : SCE.SLookup A i B)
    : ∃ vc', Core.LookupV vc_e i vc' ∧ elabExp SCE.Typ.top v' B vc' := by
  induction hlook generalizing A B vc_e with
  | dmrg_zero =>
    cases hval with | vmrg hv1 hv2 =>
    cases helab with | edmrg _ _ _ _ _ ce1 ce2 h1 h2 =>
    cases htyp_look with | zero =>
    exact ⟨ce2, Core.LookupV.lvzero, elab_value_weaken h2 hv2 _⟩
  | dmrg_succ _ ih =>
    cases hval with | vmrg hv1 hv2 =>
    cases helab with | edmrg _ _ _ _ _ ce1 ce2 h1 h2 =>
    cases htyp_look with | succ _ _ _ _ htyp_inner =>
    obtain ⟨vc', hlookvc, helab_v'⟩ := ih hv1 h1 htyp_inner
    exact ⟨vc', Core.LookupV.lvsucc hlookvc, helab_v'⟩
  | nmrg_zero => cases hval
  | nmrg_succ => cases hval

theorem sel_preservation
    {v_e v' : SCE.Exp} {vc_e : Core.Exp} {A B : SCE.Typ} {l : String}
    (hval : SCE.Value v_e)
    (helab : elabExp SCE.Typ.top v_e A vc_e)
    (hlook : S_Sem.Sel v_e l v')
    (htyp_look : SCE.SRLookup A l B)
    : ∃ vc', Core.RLookupV vc_e l vc' ∧ elabExp SCE.Typ.top v' B vc' := by
  induction hlook generalizing A B vc_e with
  | rcd =>
    cases hval with | vlrec hv =>
    cases helab with | elrec _ _ _ vc_inner _ h_inner =>
    cases htyp_look with | zero =>
    exact ⟨vc_inner, Core.RLookupV.rvlzero, h_inner⟩
  | dmrg_left hsel_inner ih =>
    cases hval with | vmrg hv1 hv2 =>
    cases helab with | edmrg _ A' B' _ _ ce1 ce2 h1 h2 =>
    cases htyp_look with
    | andl _ _ _ _ hrl hcond =>
      obtain ⟨vc', hlookvc, helab_v'⟩ := ih hv1 h1 hrl
      exact ⟨vc', Core.RLookupV.vlandl hlookvc, helab_v'⟩
    | andr _ _ _ _ hrl hcond =>
      have hlin := sel_implies_label_in hv1 h1 hsel_inner
      exact absurd hlin hcond
  | dmrg_right hsel_inner ih =>
    cases hval with | vmrg hv1 hv2 =>
    cases helab with | edmrg _ A' B' _ _ ce1 ce2 h1 h2 =>
    rename_i v1 v2 v3 l'
    have h2_weak : elabExp SCE.Typ.top v2 B' ce2 :=
      elab_value_weaken h2 hv2 (SCE.Typ.top)
    cases htyp_look with
    | andr _ _ _ _ hrl hcond =>
      obtain ⟨vc', hlookvc, helab_v'⟩ := ih hv2 h2_weak hrl
      exact ⟨vc', Core.RLookupV.vlandr hlookvc, helab_v'⟩
    | andl _ _ _ _ hrl hcond =>
      have hlin := sel_implies_label_in hv2 h2_weak hsel_inner
      exact absurd hlin hcond
  | nmrg_left => cases hval
  | nmrg_right => cases hval
  | mstruct hsel_inner ih =>
    cases hval with | vmstruct hv =>
    cases helab with
    | mstruct _ _ _ _ h =>
      cases htyp_look with
      | sig _ _ _ hrl => exact ih hv h hrl

/-! ### Evaluation of the composition encodings

Operational lemmas assembling `EBig` derivations for the generated terms.  Note
the premise shapes: each operand evaluation appears **once**, mirroring the terms
themselves. -/

/-- Non-dependent merge saves the ambient environment and restores it for each
operand; the final projection discards the saved environment. -/
theorem nmrgCore_eval
    {ρc vc₁ vc₂ ce₁ ce₂ : Core.Exp}
    (hρ : Core.Value ρc)
    (hbig1 : EBig ρc ce₁ vc₁)
    (hbig2 : EBig ρc ce₂ vc₂)
    : EBig ρc (nmrgCore ce₁ ce₂) (.mrg vc₁ vc₂) := by
  have hv1 := ebig_produces_value hρ hbig1
  have hsaved := Core.Value.vmrg hρ hρ
  simp only [nmrgCore]
  apply EBig.ebproj (EBig.ebmrg (EBig.equery hρ) ?_) Core.LookupV.lvzero
  apply EBig.ebmrg
  · exact EBig.ebbox
      (EBig.ebproj (EBig.equery hsaved) Core.LookupV.lvzero) hbig1
  · exact EBig.ebbox
      (EBig.ebproj (EBig.equery (Core.Value.vmrg hsaved hv1))
        (Core.LookupV.lvsucc Core.LookupV.lvzero)) hbig2

-- the extracted package elaborates at the interface type
theorem selpkg_elab {Γ₁ D : SCE.Typ} (hok : LinkOk Γ₁ D) :
    ∀ {v pkg : SCE.Exp} {vc : Core.Exp},
    S_Sem.SelPkg v D pkg
    → SCE.Value v
    → elabExp SCE.Typ.top v Γ₁ vc
    → ∃ cpkg, elabExp SCE.Typ.top pkg D cpkg := by
  induction hok with
  | one hrl =>
    intro v pkg vc hsp hv helab
    cases hsp with
    | one hsel =>
      obtain ⟨vcl, _, helab_vl⟩ := sel_preservation hv helab hsel hrl
      exact ⟨_, elabExp.elrec _ _ _ _ _ helab_vl⟩
  | more hok' hrl ih =>
    intro v pkg vc hsp hv helab
    cases hsp with
    | more hsp' hsel =>
      obtain ⟨cpkg', helab'⟩ := ih hsp' hv helab
      obtain ⟨vcl, _, helab_vl⟩ := sel_preservation hv helab hsel hrl
      have hvl := source_sel_value hv hsel
      exact ⟨_, elabExp.edmrg _ _ _ _ _ _ _ helab'
        (elab_value_weaken (elabExp.elrec SCE.Typ.top _ _ _ _ helab_vl)
          (SCE.Value.vlrec hvl) _)⟩

/-- The linearized wire evaluates by projection alone.  Generalized over the
environment: wherever the provider *value* `vc₁` is reachable at index `shift`,
`wire_shift ⟦D⟧` evaluates to a package that elaborates the source package.  No
premise about the provider *term* appears, because the wire never mentions it. -/
theorem wire_eval {Γ₁ D : SCE.Typ} (hok : LinkOk Γ₁ D)
    : ∀ {v₁ pkg : SCE.Exp} {ρ' vc₁ : Core.Exp} {shift : Nat},
      S_Sem.SelPkg v₁ D pkg
      → SCE.Value v₁
      → elabExp SCE.Typ.top v₁ Γ₁ vc₁
      → Core.Value ρ'
      → Core.LookupV ρ' shift vc₁
      → ∃ cpkg, EBig ρ' (wire shift (elabTyp D)) cpkg ∧ elabExp SCE.Typ.top pkg D cpkg := by
  induction hok with
  | one hrl =>
    intro v₁ pkg ρ' vc₁ shift hsp hv₁ helab₁ hρ' hlook
    cases hsp with
    | one hsel =>
      obtain ⟨vcl, hrlv, helab_vl⟩ := sel_preservation hv₁ helab₁ hsel hrl
      exact ⟨_,
        EBig.ebrec (EBig.ebsel (EBig.ebproj (EBig.equery hρ') hlook) hrlv),
        elabExp.elrec _ _ _ _ _ helab_vl⟩
  | more hok' hrl ih =>
    intro v₁ pkg ρ' vc₁ shift hsp hv₁ helab₁ hρ' hlook
    cases hsp with
    | more hsp' hsel =>
      obtain ⟨cpkg', hbig', helab'⟩ := ih hsp' hv₁ helab₁ hρ' hlook
      obtain ⟨vcl, hrlv, helab_vl⟩ := sel_preservation hv₁ helab₁ hsel hrl
      have hvl := source_sel_value hv₁ hsel
      have hcpkg' := ebig_produces_value hρ' hbig'
      exact ⟨_,
        EBig.ebmrg hbig'
          (EBig.ebrec (EBig.ebsel
            (EBig.ebproj (EBig.equery (Core.Value.vmrg hρ' hcpkg'))
              (Core.LookupV.lvsucc hlook)) hrlv)),
        elabExp.edmrg _ _ _ _ _ _ _ helab'
          (elab_value_weaken (elabExp.elrec SCE.Typ.top _ _ _ _ helab_vl)
            (SCE.Value.vlrec hvl) _)⟩

/-- The assembly lemma for the linearized composition: one evaluation of each
operand, one wire evaluation under the spine-built environment
`((ρ , v₁) , f) , v₁`, one closure-body evaluation — exactly the derivation
shape of the term.  Shared by `link` and `linkall`. -/
theorem linkStep_eval
    {ρc vc₁ vc₂ cpkg vc₃ : Core.Exp} {g1 D B DT : Core.Typ}
    {ce₁ ce₂ body : Core.Exp}
    (hρ : Core.Value ρc)
    (hbig1 : EBig ρc ce₁ vc₁)
    (hbig2 : EBig ρc ce₂ (.clos vc₂ DT body))
    (hbigw : EBig (.mrg (.mrg (.mrg ρc vc₁) (.clos vc₂ DT body)) vc₁)
               (wire 0 D) cpkg)
    (hbig3 : EBig (.mrg vc₂ cpkg) body vc₃)
    : EBig ρc (linkedCore g1 D B ce₁ ce₂) (.mrg vc₁ vc₃) := by
  have hv1 := ebig_produces_value hρ hbig1
  have hvf := ebig_produces_value hρ hbig2
  simp only [linkedCore, linkStep]
  apply EBig.ebapp
  · exact EBig.ebapp (EBig.ebclos hρ) hbig1 (EBig.ebclos (Core.Value.vmrg hρ hv1))
  · exact hbig2
  · apply EBig.ebmrg
    · exact EBig.ebproj
        (EBig.equery (Core.Value.vmrg (Core.Value.vmrg hρ hv1) hvf))
        (Core.LookupV.lvsucc Core.LookupV.lvzero)
    · exact EBig.ebapp
        (EBig.ebproj
          (EBig.equery
            (Core.Value.vmrg (Core.Value.vmrg (Core.Value.vmrg hρ hv1) hvf) hv1))
          (Core.LookupV.lvsucc Core.LookupV.lvzero))
        hbigw
        hbig3

/-- The single-import wire evaluated in the spine-built environment: the
`link` instance of `wire_eval`, stated directly at the target. -/
theorem wire_eval_rcd
    {ρc vc₁ f vc_l : Core.Exp} {l : String} {A : Core.Typ}
    (hρ : Core.Value ρc) (hv1 : Core.Value vc₁) (hf : Core.Value f)
    (hsel : Core.RLookupV vc₁ l vc_l)
    : EBig (.mrg (.mrg (.mrg ρc vc₁) f) vc₁) (wire 0 (.rcd l A)) (.lrec l vc_l) := by
  simp only [wire]
  exact EBig.ebrec (EBig.ebsel
    (EBig.ebproj
      (EBig.equery (Core.Value.vmrg (Core.Value.vmrg (Core.Value.vmrg hρ hv1) hf) hv1))
      Core.LookupV.lvzero)
    hsel)

theorem semantic_preservation
    {Γ A : SCE.Typ} {es : SCE.Exp} {ec : Core.Exp}
    {ρs vs : SCE.Exp} {ρc : Core.Exp}
    (helab : elabExp Γ es A ec)
    (heval : S_Sem.BStep ρs es vs)
    (henv : elabExp SCE.Typ.top ρs Γ ρc)
    (henv_val : SCE.Value ρs)
    : ∃ vc, EBig ρc ec vc ∧ elabExp SCE.Typ.top vs A vc := by
  induction heval generalizing Γ A ec ρc with
  | query hval=>
    rename_i v
    exists ρc
    constructor
    · cases helab
      refine EBig.equery ?_
      exact elab_value henv hval
    · cases helab
      assumption
  | lit hval =>
    cases helab
    exact ⟨Core.Exp.lit _, EBig.eblit (elab_value henv henv_val), elabExp.elit .top _⟩
  | unit =>
    cases helab
    exists Core.Exp.unit
    constructor
    · apply EBig.ebunit
      (expose_names; exact elab_value henv h)
    · exact elabExp.eunit SCE.Typ.top
  | clos_val henv_src hval =>
    cases helab with
    | eclos _ _ _ _ _ _ _ _ hval' h1 h2 =>
      exact ⟨_, EBig.eclos (elab_value henv henv_val) (elab_value h1 hval),
               elabExp.eclos .top _ _ _ _ _ _ _ hval h1 h2⟩
  | mclos_val henv_src hval =>
    cases helab with
    | mclos _ _ _ _ _ _ _ _ hval' h1 h2 =>
      exact ⟨_, EBig.eclos (elab_value henv henv_val) (elab_value h1 hval),
               elabExp.mclos .top _ _ _ _ _ _ _ hval h1 h2⟩
  | proj ρ1 hstep hlookv ih1 =>
    cases helab with
    | eproj _ A' _ _ ce _ h_elab h_slook =>
      obtain ⟨vc, hbig, helab_v⟩ := ih1 h_elab henv henv_val
      obtain ⟨vc', hlookvc, helab_v'⟩ := lookup_preservation
        (eval_produces_value henv_val hstep)
        helab_v hlookv h_slook
      exact ⟨vc', EBig.ebproj hbig hlookvc, helab_v'⟩
  | lam hval =>
    cases helab with
    | elam _ _ _ _ ce h_body =>
      exact ⟨Core.Exp.clos ρc _ ce,
             EBig.ebclos (elab_value henv henv_val),
             elabExp.eclos .top _ _ _ _ _ _ _ henv_val henv h_body⟩
  | box hval_ρ hstep1 hstep2 ih1 ih2 =>
    cases helab with
    | ebox _ ctx' _ _ _ ce1 ce2 h_elab1 h_elab2 =>
      obtain ⟨vc1, hbig1, helab_v1⟩ := ih1 h_elab1 henv henv_val
      have hv1_val := eval_produces_value henv_val hstep1
      obtain ⟨vc, hbig2, helab_v⟩ := ih2 h_elab2 helab_v1 hv1_val
      exact ⟨vc, EBig.ebbox hbig1 hbig2, helab_v⟩
  | app_clos hval_ρ hstep1 hstep2 hstep_body ih1 ih2 ih3 =>
    cases helab with
    | eapp _ A_param B _ _ ce1 ce2 h_elab1 h_elab2 =>
      obtain ⟨vc_clos, hbig1, helab_clos⟩ := ih1 h_elab1 henv henv_val
      obtain ⟨vc2, hbig2, helab_v2⟩ := ih2 h_elab2 henv henv_val
      cases helab_clos with
      | eclos _ _ _ _ _ _ _ _ hval_v1 h_env_v1 h_body_elab =>
        rename_i ctx_clos ce_env ce_body
        have hv1_val := eval_produces_value henv_val hstep1
        cases hv1_val with
        | vclos hval_inner =>
          have hv2_val := eval_produces_value henv_val hstep2
          have hval_body_env := SCE.Value.vmrg hval_inner hv2_val
          have helab_body_env := elabExp.edmrg .top _ _ _ _ _ _
            h_env_v1 (elab_value_weaken helab_v2 hv2_val (SCE.Typ.and .top ctx_clos))
          obtain ⟨vc_result, hbig3, helab_result⟩ := ih3 h_body_elab helab_body_env hval_body_env
          exact ⟨vc_result,
                 EBig.ebapp hbig1 hbig2 hbig3,
                 helab_result⟩
  | app_mclos hval_ρ hstep1 hstep2 hstep_body ih1 ih2 ih3 =>
    cases helab with
    | mapp _ A_param mt _ _ ce1 ce2 h_elab1 h_elab2 =>
      obtain ⟨vc_clos, hbig1, helab_clos⟩ := ih1 h_elab1 henv henv_val
      obtain ⟨vc2, hbig2, helab_v2⟩ := ih2 h_elab2 henv henv_val
      cases helab_clos with
      | mclos _ _ _ _ _ _ _ _ hval_v1 h_env_v1 h_body_elab =>
        have hv1_val := eval_produces_value henv_val hstep1
        cases hv1_val with
        | vmclos hval_inner =>
          have hv2_val := eval_produces_value henv_val hstep2
          have hval_body_env := SCE.Value.vmrg hval_inner hv2_val
          have helab_body_env := elabExp.edmrg .top _ _ _ _ _ _
            h_env_v1 (elab_value_weaken helab_v2 hv2_val _)
          obtain ⟨vc_result, hbig3, helab_result⟩ := ih3 h_body_elab helab_body_env hval_body_env
          exact ⟨vc_result,
                 EBig.ebapp hbig1 hbig2 hbig3,
                 helab_result⟩
  | dmrg hval_ρ hstep1 hstep2 ih1 ih2 =>
    cases helab with
    | edmrg _ A_inner B_inner _ _ ce1 ce2 h_elab1 h_elab2 =>
      obtain ⟨vc1, hbig1, helab_v1⟩ := ih1 h_elab1 henv henv_val
      have hv1_val := eval_produces_value henv_val hstep1
      have hval_mrg := SCE.Value.vmrg henv_val hv1_val
      have helab_mrg_env := elabExp.edmrg .top _ _ _ _ _ _
        henv (elab_value_weaken helab_v1 hv1_val _)
      obtain ⟨vc2, hbig2, helab_v2⟩ := ih2 h_elab2 helab_mrg_env hval_mrg
      have hv2_val := eval_produces_value hval_mrg hstep2
      have helab_result := elabExp.edmrg .top _ _ _ _ _ _
        helab_v1 (elab_value_weaken helab_v2 hv2_val _)
      exact ⟨.mrg vc1 vc2, EBig.ebmrg hbig1 hbig2, helab_result⟩
  | nmrg hval_ρ hstep1 hstep2 ih1 ih2 =>
    cases helab with
    | enmrg _ A_inner B_inner _ _ ce1 ce2 h_elab1 h_elab2 =>
      obtain ⟨vc1, hbig1, helab_v1⟩ := ih1 h_elab1 henv henv_val
      obtain ⟨vc2, hbig2, helab_v2⟩ := ih2 h_elab2 henv henv_val
      have hv1_val := eval_produces_value henv_val hstep1
      have hv2_val := eval_produces_value henv_val hstep2
      have helab_result := elabExp.edmrg .top _ _ _ _ _ _
        helab_v1 (elab_value_weaken helab_v2 hv2_val _)
      exact ⟨.mrg vc1 vc2,
             nmrgCore_eval (elab_value henv henv_val) hbig1 hbig2,
             helab_result⟩
  | openm hval_ρ hstep1 hstep2 ih1 ih2 =>
    cases helab with
    | openm _ A_inner B_inner _ _ ce1 ce2 l_inner h_elab1 h_elab2 =>
      -- IH on e₁: produces lrec l v'
      obtain ⟨vc_rcd, hbig1, helab_rcd⟩ := ih1 h_elab1 henv henv_val
      -- extract inner value from lrec elaboration
      cases helab_rcd with
      | elrec _ _ _ vc_inner _ helab_inner =>
        -- build env for body: ρ ,, v'
        have hv'_val := eval_produces_value henv_val hstep1
        cases hv'_val with
        | vlrec hval_inner =>
          have hval_mrg := SCE.Value.vmrg henv_val hval_inner
          have helab_mrg_env := elabExp.edmrg .top _ _ _ _ _ _
            henv (elab_value_weaken helab_inner hval_inner _)
          -- IH on e₂
          obtain ⟨vc_result, hbig2, helab_result⟩ := ih2 h_elab2 helab_mrg_env hval_mrg
          -- core big-step: app (lam ce2) (rproj ce1 l)
          exact ⟨vc_result,
                 EBig.ebapp
                   (EBig.ebclos (elab_value henv henv_val))
                   (EBig.ebsel hbig1 Core.RLookupV.rvlzero)
                   hbig2,
                 helab_result⟩
  | letb hval_ρ hstep1 hstep2 ih1 ih2 =>
    cases helab with
    | letb _ A_inner B_inner _ _ ce1 ce2 h_elab1 h_elab2 =>
      obtain ⟨vc1, hbig1, helab_v1⟩ := ih1 h_elab1 henv henv_val
      have hv1_val := eval_produces_value henv_val hstep1
      have hval_mrg := SCE.Value.vmrg henv_val hv1_val
      have helab_mrg_env := elabExp.edmrg .top _ _ _ _ _ _
        henv (elab_value_weaken helab_v1 hv1_val _)
      obtain ⟨vc_result, hbig2, helab_result⟩ := ih2 h_elab2 helab_mrg_env hval_mrg
      exact ⟨vc_result,
             EBig.ebproj (EBig.ebmrg hbig1 hbig2) Core.LookupV.lvzero,
             helab_result⟩
  | mstruct hval_ρ hstep_body ih =>
    cases helab with
    | mstruct _ _ _ ce h_elab_body =>
      obtain ⟨vc, hbig, helab_v⟩ := ih h_elab_body henv henv_val
      exact ⟨vc, hbig, elabExp.mstruct .top _ _ _ helab_v⟩
  | mfunctor_sandboxed hval_ρ =>
    cases helab with
    | mfunctor _ ctxInner _ _ sb _ ce hs1 hs2 h_body =>
      have hctx := hs1 rfl
      rw [hctx] at h_body
      exact ⟨Core.Exp.clos .unit _ ce,
             EBig.ebbox (EBig.ebunit (elab_value henv henv_val))
                        (EBig.ebclos Value.vunit),
             elabExp.mclos .top _ _ _ _ _ _ _ Value.vunit (elabExp.eunit .top) h_body⟩
  | mfunctor_open hval_ρ =>
    cases helab with
    | mfunctor _ ctxInner _ _ sb _ ce hs1 hs2 h_body =>
      have hctx := hs2 rfl
      rw [hctx] at h_body
      exact ⟨Core.Exp.clos ρc _ ce,
             EBig.ebclos (elab_value henv henv_val),
             elabExp.mclos .top _ _ _ _ _ _ _ henv_val henv h_body⟩
  | lrec hval_ρ hstep ih =>
    cases helab with
    | elrec _ A_inner _ ce l h_elab =>
      obtain ⟨vc, hbig, helab_v⟩ := ih h_elab henv henv_val
      exact ⟨Core.Exp.lrec _ vc,
             EBig.ebrec hbig,
             elabExp.elrec .top _ _ _ _ helab_v⟩
  | rproj hval_ρ hstep hsel ih =>
    cases helab with
    | erproj _ A_inner B_inner _ ce l_inner h_elab h_slook =>
      obtain ⟨vc, hbig, helab_v⟩ := ih h_elab henv henv_val
      have hv_val := eval_produces_value henv_val hstep
      obtain ⟨vc', hrlookup_v, helab_v'⟩ :=
        sel_preservation hv_val helab_v hsel h_slook
      exact ⟨vc', EBig.ebsel hbig hrlookup_v, helab_v'⟩
  | mlink h1 bstep1 bstep2 sel1 step2 step3 ih1 ih2 =>
    rename_i _ e1 e2 v1 v2 vl v3 A_src body_src l_name
    cases helab with
    | mlink _ Γ₁ A_inner mt l_inner _ _ ce1 ce2 h_elab1 h_elab2 h_lookup =>
      obtain ⟨vc1, hbig1, helab_v1⟩ := step3 h_elab1 henv henv_val
      obtain ⟨vc2, hbig2, helab_v2⟩ := ih1 h_elab2 henv henv_val
      cases helab_v2 with
      | mclos _ _ _ _ _ _ _ _ hval_v2 h_env2 h_body =>
        rename_i ctx_inner ce1_inner ce2_inner
        have hv1_val := eval_produces_value henv_val bstep1
        obtain ⟨vc_l, hrlookup_v, helab_vl⟩ :=
          sel_preservation hv1_val helab_v1 sel1 h_lookup
        have hvl_val := source_sel_value hv1_val sel1
        have hval_lrec := SCE.Value.vlrec (l := l_name) hvl_val
        have hval_env := SCE.Value.vmrg hval_v2 hval_lrec
        have helab_lrec := elabExp.elrec .top _ _ _ l_name helab_vl
        have helab_lrec_weak :=
          elab_value_weaken helab_lrec hval_lrec (SCE.Typ.and .top ctx_inner)
        have helab_env := elabExp.edmrg .top _ _ _ _ _ _ h_env2 helab_lrec_weak
        obtain ⟨vc3, hbig3, helab_v3⟩ := ih2 h_body helab_env hval_env
        have hv3_val := eval_produces_value hval_env step2
        have helab_v3_weak :=
          elab_value_weaken helab_v3 hv3_val (SCE.Typ.and .top Γ₁)
        have helab_result := elabExp.edmrg .top _ _ _ _ _ _
          helab_v1 helab_v3_weak
        have hρc := elab_value henv henv_val
        exact ⟨.mrg vc1 vc3,
               linkStep_eval hρc hbig1 hbig2
                 (wire_eval_rcd hρc (ebig_produces_value hρc hbig1)
                   (ebig_produces_value hρc hbig2) hrlookup_v)
                 hbig3,
               helab_result⟩
  | mlinkn h1 bstep1 bstep2 hsp bstep3 ih1 ih2 ih3 =>
    cases helab with
    | mlinkn _ Γ₁ D_e B_e _ _ ce1 ce2 h_elab1 h_elab2 hok =>
      obtain ⟨vc1, hbig1, helab_v1⟩ := ih1 h_elab1 henv henv_val
      obtain ⟨vc2, hbig2, helab_v2⟩ := ih2 h_elab2 henv henv_val
      cases helab_v2 with
      | mclos _ ctx_inner _ _ _ _ ce_env ce_body hval_v2 h_env2 h_body =>
        have hv1_val := eval_produces_value henv_val bstep1
        have hρc := elab_value henv henv_val
        obtain ⟨cpkg, hbigw, helab_pkg⟩ :=
          wire_eval hok hsp hv1_val helab_v1
            (Core.Value.vmrg
              (Core.Value.vmrg (Core.Value.vmrg hρc (ebig_produces_value hρc hbig1))
                (ebig_produces_value hρc hbig2))
              (ebig_produces_value hρc hbig1))
            Core.LookupV.lvzero
        have hvpkg := S_Sem.selpkg_value hsp hv1_val
        have hval_env := SCE.Value.vmrg hval_v2 hvpkg
        have helab_env := elabExp.edmrg .top _ _ _ _ _ _ h_env2
          (elab_value_weaken helab_pkg hvpkg _)
        obtain ⟨vc3, hbig3, helab_v3⟩ := ih3 h_body helab_env hval_env
        have hv3_val := eval_produces_value hval_env bstep3
        have helab_result := elabExp.edmrg .top _ _ _ _ _ _
          helab_v1 (elab_value_weaken helab_v3 hv3_val _)
        exact ⟨.mrg vc1 vc3,
               linkStep_eval hρc hbig1 hbig2 hbigw hbig3,
               helab_result⟩
  | inl hval_ρ hstep ih =>
    cases helab with
    | einl _ A_inner B_inner _ ce h_elab =>
      obtain ⟨vc, hbig, helab_v⟩ := ih h_elab henv henv_val
      exact ⟨_, EBig.ebinl hbig, elabExp.einl .top _ _ _ _ helab_v⟩
  | inr hval_ρ hstep ih =>
    cases helab with
    | einr _ A_inner B_inner _ ce h_elab =>
      obtain ⟨vc, hbig, helab_v⟩ := ih h_elab henv henv_val
      exact ⟨_, EBig.ebinr hbig, elabExp.einr .top _ _ _ _ helab_v⟩
  | case_inl hval_ρ hstep1 hstep2 ih1 ih2 =>
    cases helab with
    | ecase _ A_inner B_inner C_inner _ _ _ ce ce1 ce2 h_elab h_elab1 h_elab2 =>
      obtain ⟨vc_inl, hbig1, helab_inl⟩ := ih1 h_elab henv henv_val
      cases helab_inl with
      | einl _ _ _ _ ce_v h_v =>
        have h_inl_val := eval_produces_value henv_val hstep1
        cases h_inl_val with
        | vinl hv1 =>
          have hval_mrg := SCE.Value.vmrg henv_val hv1
          have helab_mrg := elabExp.edmrg .top _ _ _ _ _ _
            henv (elab_value_weaken h_v hv1 _)
          obtain ⟨vc, hbig2, helab_v⟩ := ih2 h_elab1 helab_mrg hval_mrg
          exact ⟨vc, EBig.ebcasel hbig1 hbig2, helab_v⟩
  | case_inr hval_ρ hstep1 hstep2 ih1 ih2 =>
    cases helab with
    | ecase _ A_inner B_inner C_inner _ _ _ ce ce1 ce2 h_elab h_elab1 h_elab2 =>
      obtain ⟨vc_inr, hbig1, helab_inr⟩ := ih1 h_elab henv henv_val
      cases helab_inr with
      | einr _ _ _ _ ce_v h_v =>
        have h_inr_val := eval_produces_value henv_val hstep1
        cases h_inr_val with
        | vinr hv1 =>
          have hval_mrg := SCE.Value.vmrg henv_val hv1
          have helab_mrg := elabExp.edmrg .top _ _ _ _ _ _
            henv (elab_value_weaken h_v hv1 _)
          obtain ⟨vc, hbig2, helab_v⟩ := ih2 h_elab2 helab_mrg hval_mrg
          exact ⟨vc, EBig.ebcaser hbig1 hbig2, helab_v⟩
  | fclos_val henv_src hval =>
    cases helab with
    | efclos _ _ _ _ _ _ _ _ hval' h1 h2 =>
      exact ⟨_, EBig.efclos (elab_value henv henv_val) (elab_value h1 hval),
               elabExp.efclos .top _ _ _ _ _ _ _ hval h1 h2⟩
  | flam hval =>
    cases helab with
    | eflam _ _ _ _ ce h_body =>
      exact ⟨Core.Exp.fclos ρc _ _ ce,
             EBig.ebflam (elab_value henv henv_val),
             elabExp.efclos .top _ _ _ _ _ _ _ henv_val henv h_body⟩
  | app_fclos hval_ρ hstep1 hstep2 hstep_body ih1 ih2 ih3 =>
    cases helab with
    | eapp _ A_param B _ _ ce1 ce2 h_elab1 h_elab2 =>
      obtain ⟨vc_clos, hbig1, helab_clos⟩ := ih1 h_elab1 henv henv_val
      obtain ⟨vc2, hbig2, helab_v2⟩ := ih2 h_elab2 henv henv_val
      cases helab_clos with
      | efclos _ _ _ _ _ _ _ _ hval_v1 h_env_v1 h_body_elab =>
        rename_i ctx_clos ce_env ce_body
        have hv1_val := eval_produces_value henv_val hstep1
        cases hv1_val with
        | vfclos hval_inner =>
          have hv2_val := eval_produces_value henv_val hstep2
          have helab_body_env := elabExp.edmrg .top _ _ _ _ _ _
            (elabExp.edmrg .top _ _ _ _ _ _ h_env_v1
              (elabExp.efclos _ _ _ _ _ _ _ _ hval_inner h_env_v1 h_body_elab))
            (elab_value_weaken helab_v2 hv2_val _)
          obtain ⟨vc_result, hbig3, helab_result⟩ := ih3 h_body_elab helab_body_env
            (SCE.Value.vmrg (SCE.Value.vmrg hval_inner (SCE.Value.vfclos hval_inner)) hv2_val)
          exact ⟨vc_result,
                 EBig.ebfapp hbig1 hbig2 hbig3,
                 helab_result⟩
  | fold hval_ρ hstep ih =>
    cases helab with
    | efold _ T_inner _ ce h_elab =>
      obtain ⟨vc, hbig, helab_v⟩ := ih h_elab henv henv_val
      exact ⟨_, EBig.ebfold hbig, elabExp.efold .top _ _ _ helab_v⟩
  | unfold hval_ρ hstep ih =>
    cases helab with
    | eunfold _ T_inner _ _ ce h_elab heq =>
      subst heq
      obtain ⟨vc_fold, hbig, helab_fold⟩ := ih h_elab henv henv_val
      cases helab_fold with
      | efold _ _ _ ce_v h_v =>
        exact ⟨_, EBig.ebunfold hbig, h_v⟩

theorem whole_program_correctness
    {A : SCE.Typ} {es : SCE.Exp} {ec : Core.Exp} {vs : SCE.Exp}
    (helab : elabExp SCE.Typ.top es A ec)
    (heval : S_Sem.BStep .unit es vs)
    : ∃ vc, EBig .unit ec vc ∧ elabExp SCE.Typ.top vs A vc := by
  exact semantic_preservation helab heval (elabExp.eunit SCE.Typ.top) SCE.Value.vunit
