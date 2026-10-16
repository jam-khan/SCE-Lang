import LeanSce.SCE.Elaboration.Elaboration
import LeanSce.SCE.Semantics.SmallStep
import LeanSce.SCE.Syntax

open SCE S_Sem

-- Value weakening: well-elaborated values can be retyped under any context
theorem elab_value_weaken
    {Γ A : SCE.Typ} {v : SCE.Exp} {ce : Core.Exp}
    (helab : elabExp Γ v A ce)
    (hv : SCE.Value v)
    (Γ' : SCE.Typ) : elabExp Γ' v A ce := by
  induction helab generalizing Γ' with
  | equery => cases hv
  | elit => exact elabExp.elit _ _
  | eunit => exact elabExp.eunit _
  | eapp _ => cases hv
  | eproj _=> cases hv
  | ebox _ => cases hv
  | elam _ => cases hv
  | erproj _ => cases hv
  | letb _ => cases hv
  | openm _ => cases hv
  | mstruct _ _ _ _ h ih =>
    cases hv with
    | vmstruct hv' => exact elabExp.mstruct _ _ _ _ (ih hv' _)
  | mfunctor _ => cases hv
  | mapp _ => cases hv
  | mlink _ => cases hv
  | mlinkn _ => cases hv
  | enmrg _ => cases hv
  | ecase _ => cases hv
  | eflam _ => cases hv
  | efclos _ _ _ _ _ _ _ _ hval ht hb ih1 ih2 =>
    cases hv with
    | vfclos hv' => exact elabExp.efclos _ _ _ _ _ _ _ _ hval ht hb
  | eunfold _ => cases hv
  | efold _ _ _ _ _ ih =>
    cases hv with
    | vfold hv' => exact elabExp.efold _ _ _ _ (ih hv' _)
  | einl _ _ _ _ _ _ ih =>
    cases hv with
    | vinl hv' => exact elabExp.einl _ _ _ _ _ (ih hv' _)
  | einr _ _ _ _ _ _ ih =>
    cases hv with
    | vinr hv' => exact elabExp.einr _ _ _ _ _ (ih hv' _)
  | edmrg _ _ _ _ _ _ _ _ _ ih1 ih2 =>
    cases hv with
    | vmrg hv1 hv2 =>
      exact elabExp.edmrg _ _ _ _ _ _ _ (ih1 hv1 _) (ih2 hv2 _)
  | elrec _ _ _ _ _ _ ih =>
    cases hv with
    | vlrec hv' => exact elabExp.elrec _ _ _ _ _ (ih hv' _)
  | eclos _ _ _ _ _ _ _ _ hval ht hb ih1 ih2 =>
    cases hv with
    | vclos hv' => exact elabExp.eclos _ _ _ _ _ _ _ _ hval ht hb
  | mclos _ _ _ _ _ _ _ _ hval ht hb ih1 ih2 =>
    cases hv with
    | vmclos hv' => exact elabExp.mclos _ _ _ _ _ _ _ _ hval ht hb

/-- A source value retains its type under any ambient context. -/
theorem svalue_weaken
    {Γ₁ A : SCE.Typ} {v : SCE.Exp}
    (htyp : SCE.HasType Γ₁ v A)
    (hv : SCE.Value v)
    (Γ₂ : SCE.Typ) : SCE.HasType Γ₂ v A := by
  obtain ⟨ce, helab⟩ := htyp
  exact ⟨ce, elab_value_weaken helab hv Γ₂⟩

-- SCE LookupV preserves values
theorem sce_lookupv_value {v v' : SCE.Exp} {n : Nat}
    (hlook : S_Sem.LookupV v n v')
    (hv : SCE.Value v) : SCE.Value v' := by
  induction hlook with
  | dmrg_zero => cases hv; assumption
  | dmrg_succ _ ih => cases hv; exact ih (by assumption)
  | nmrg_zero => cases hv
  | nmrg_succ _ ih => cases hv

-- Lookup preservation for elaboration
theorem elab_lookup_pres {Γ B : SCE.Typ} {n : Nat}
    (hlook : SLookup Γ n B) :
    ∀ {v : SCE.Exp} {ce : Core.Exp} {v' : SCE.Exp},
    S_Sem.LookupV v n v'
    → SCE.Value v
    → elabExp SCE.Typ.top v Γ ce
    → ∃ ce', elabExp Γ v' B ce' := by
  induction hlook with
  | zero =>
    intro v ce v' hlv hv helab
    cases hlv with
    | dmrg_zero =>
      cases hv with
      | vmrg hv1 hv2 =>
        cases helab with
        | edmrg _ _ _ _ _ _ _ h1 h2 =>
          exact ⟨_, elab_value_weaken h2 hv2 _⟩
    | nmrg_zero => cases hv
  | succ _ _ _ _ _ ih =>
    intro v ce v' hlv hv helab
    cases hlv with
    | dmrg_succ hlv' =>
      cases hv with
      | vmrg hv1 hv2 =>
        cases helab with
        | edmrg _ _ _ _ _ _ _ h1 h2 =>
          have ⟨ce', hce'⟩ := ih hlv' hv1 (elab_value_weaken h1 hv1 _)
          have hv' := sce_lookupv_value hlv' hv1
          exact ⟨_, elab_value_weaken hce' hv' _⟩
    | nmrg_succ => cases hv

-- SCE Sel preserves values
theorem sce_sel_value {v v' : SCE.Exp} {l : String}
    (hsel : S_Sem.Sel v l v')
    (hv : SCE.Value v) : SCE.Value v' := by
  induction hsel with
  | rcd => cases hv; assumption
  | dmrg_left _ ih => cases hv; exact ih (by assumption)
  | dmrg_right _ ih => cases hv; exact ih (by assumption)
  | nmrg_left _ ih => cases hv
  | nmrg_right _ ih => cases hv
  | mstruct _ ih => cases hv; exact ih (by assumption)

-- If a value elaborates at type A and label l is not in A, then Sel v l v' is impossible
theorem elab_notin_sel_false
    {l : String} {v v' : SCE.Exp}
    (hsel : S_Sem.Sel v l v')
    (hv : SCE.Value v)
    {A : SCE.Typ}
    (hnotin : ¬LabelIn l A)
    {ce : Core.Exp}
    (helab : elabExp SCE.Typ.top v A ce) : False := by
  induction hsel generalizing A ce with
  | rcd =>
    cases hv with
    | vlrec hv' =>
      cases helab with
      | elrec => exact hnotin (LabelIn.rcd _ _)
  | dmrg_left hsel' ih =>
    cases hv with
    | vmrg hv1 hv2 =>
      cases helab with
      | edmrg _ _ _ _ _ _ _ h1 h2 =>
        exact ih hv1 (fun hlin => hnotin (LabelIn.andl _ _ _ hlin)) (elab_value_weaken h1 hv1 _)
  | dmrg_right hsel' ih =>
    cases hv with
    | vmrg hv1 hv2 =>
      cases helab with
      | edmrg _ _ _ _ _ _ _ h1 h2 =>
        exact ih hv2 (fun hlin => hnotin (LabelIn.andr _ _ _ hlin)) (elab_value_weaken h2 hv2 _)
  | nmrg_left _ ih => cases hv
  | nmrg_right _ ih => cases hv
  | mstruct hsel' ih =>
    cases hv with
    | vmstruct hv' =>
      cases helab with
      | mstruct _ _ _ _ h =>
        exact ih hv' (fun hlin => hnotin (LabelIn.sig _ _ hlin)) h

-- Record lookup preservation for elaboration
theorem elab_rlookup_pres {Γ B : SCE.Typ} {l : String}
    (hlook : SRLookup Γ l B) :
    ∀ {v : SCE.Exp} {ce : Core.Exp} {v' : SCE.Exp},
    S_Sem.Sel v l v'
    → SCE.Value v
    → elabExp SCE.Typ.top v Γ ce
    → ∃ ce', elabExp Γ v' B ce' := by
  induction hlook with
  | zero =>
    intro v ce v' hsel hv helab
    cases helab <;> cases hv
    rename_i v₀ ce₀ h1 hv'
    cases hsel with
    | rcd => exact ⟨_, elab_value_weaken h1 hv' _⟩
  | andl _ _ _ _ _ _ ih =>
    intro v ce v' hsel hv helab
    cases helab <;> cases hv
    rename_i v₁ v₂ ce₁ ce₂ h1 h2 hv1 hv2
    cases hsel with
    | dmrg_left hsel' =>
      have ⟨ce', hce'⟩ := ih hsel' hv1 (elab_value_weaken h1 hv1 _)
      exact ⟨_, elab_value_weaken hce' (sce_sel_value hsel' hv1) _⟩
    | dmrg_right hsel' =>
      rename_i hrl hnotin
      exact (elab_notin_sel_false hsel' hv2 hnotin (elab_value_weaken h2 hv2 _)).elim
  | andr _ _ _ _ _ _ ih =>
    intro v ce v' hsel hv helab
    cases helab <;> cases hv
    rename_i v₁ v₂ ce₁ ce₂ h1 h2 hv1 hv2
    cases hsel with
    | dmrg_right hsel' =>
      have ⟨ce', hce'⟩ := ih hsel' hv2 (elab_value_weaken h2 hv2 _)
      exact ⟨_, elab_value_weaken hce' (sce_sel_value hsel' hv2) _⟩
    | dmrg_left hsel' =>
      rename_i hrl hnotin
      exact (elab_notin_sel_false hsel' hv1 hnotin (elab_value_weaken h1 hv1 _)).elim
  | sig _ _ _ _ ih =>
    intro v ce v' hsel hv helab
    cases helab <;> cases hv
    cases hsel with
    | mstruct hsel' =>
      have ⟨ce', hce'⟩ := ih hsel' ‹SCE.Value _› ‹elabExp _ _ _ _›
      exact ⟨_, elab_value_weaken hce' (sce_sel_value hsel' ‹SCE.Value _›) _⟩

-- Lookup progress for elaboration
theorem elab_lookup_prog {A B : SCE.Typ} {n : Nat}
    (hlook : SLookup A n B) :
    ∀ {v : SCE.Exp} {ce : Core.Exp},
    elabExp SCE.Typ.top v A ce
    → SCE.Value v
    → ∃ v', S_Sem.LookupV v n v' := by
  induction hlook with
  | zero =>
    intro v ce helab hv
    cases helab <;> cases hv
    exact ⟨_, LookupV.dmrg_zero⟩
  | succ _ _ _ _ _ ih =>
    intro v ce helab hv
    cases helab <;> cases hv
    rename_i v₁ v₂ ce₁ ce₂ h1 h2 hv1 hv2
    have ⟨v', hlv⟩ := ih (elab_value_weaken h1 hv1 _) hv1
    exact ⟨_, LookupV.dmrg_succ hlv⟩

-- Record lookup progress for elaboration
theorem elab_rlookup_prog {A B : SCE.Typ} {l : String}
    (hlook : SRLookup A l B) :
    ∀ {v : SCE.Exp} {ce : Core.Exp},
    elabExp SCE.Typ.top v A ce
    → SCE.Value v
    → ∃ v', S_Sem.Sel v l v' := by
  induction hlook with
  | zero =>
    intro v ce helab hv
    cases helab <;> cases hv
    · exact ⟨_, Sel.rcd⟩
  | andl _ _ _ _ _ _ ih =>
    intro v ce helab hv
    cases helab <;> cases hv
    rename_i v₁ v₂ ce₁ ce₂ h1 h2 hv1 hv2
    have ⟨v', hsel⟩ := ih (elab_value_weaken h1 hv1 _) hv1
    exact ⟨_, Sel.dmrg_left hsel⟩
  | andr _ _ _ _ _ _ ih =>
    intro v ce helab hv
    cases helab <;> cases hv
    rename_i v₁ v₂ ce₁ ce₂ h1 h2 hv1 hv2
    have ⟨v', hsel⟩ := ih (elab_value_weaken h2 hv2 _) hv2
    exact ⟨_, Sel.dmrg_right hsel⟩
  | sig _ _ _ _ ih =>
    intro v ce helab hv
    cases helab <;> cases hv
    rename_i se h hv'
    have ⟨v', hsel⟩ := ih h hv'
    exact ⟨_, Sel.mstruct hsel⟩

/-- Indexed lookup in a well-typed source value returns a value. -/
theorem slookup_progress
    {A B : SCE.Typ} {n : Nat} {v : SCE.Exp}
    (hlook : SLookup A n B)
    (htyp : SCE.HasType .top v A)
    (hv : SCE.Value v)
    : ∃ v', SCE.Value v' ∧ S_Sem.LookupV v n v' := by
  obtain ⟨ce, helab⟩ := htyp
  obtain ⟨v', hlookup⟩ := elab_lookup_prog hlook helab hv
  exact ⟨v', sce_lookupv_value hlookup hv, hlookup⟩

/-- A field contained in a well-typed source value's type can be selected. -/
theorem sselection_progress
    {A B : SCE.Typ} {l : String} {v : SCE.Exp}
    (hlook : SRLookup A l B)
    (htyp : SCE.HasType .top v A)
    (hv : SCE.Value v)
    : ∃ v', SCE.Value v' ∧ S_Sem.Sel v l v' := by
  obtain ⟨ce, helab⟩ := htyp
  obtain ⟨v', hsel⟩ := elab_rlookup_prog hlook helab hv
  exact ⟨v', sce_sel_value hsel hv, hsel⟩

-- Package extraction progress: every import of D can be selected from a
-- well-elaborated module value
theorem selpkg_prog {Γ₁ D : SCE.Typ} (hok : LinkOk Γ₁ D) :
    ∀ {v : SCE.Exp} {ce : Core.Exp},
    elabExp SCE.Typ.top v Γ₁ ce
    → SCE.Value v
    → ∃ pkg, S_Sem.SelPkg v D pkg := by
  induction hok with
  | one hrl =>
    intro v ce helab hv
    have ⟨vl, hsel⟩ := elab_rlookup_prog hrl helab hv
    exact ⟨_, S_Sem.SelPkg.one hsel⟩
  | more hok' hrl ih =>
    intro v ce helab hv
    have ⟨pkg, hsp⟩ := ih helab hv
    have ⟨vl, hsel⟩ := elab_rlookup_prog hrl helab hv
    exact ⟨_, S_Sem.SelPkg.more hsp hsel⟩

-- Package extraction preservation: the extracted package elaborates at D
theorem selpkg_pres {Γ₁ D : SCE.Typ} (hok : LinkOk Γ₁ D) :
    ∀ {v pkg : SCE.Exp} {ce : Core.Exp},
    S_Sem.SelPkg v D pkg
    → SCE.Value v
    → elabExp SCE.Typ.top v Γ₁ ce
    → ∃ cpkg, elabExp SCE.Typ.top pkg D cpkg := by
  induction hok with
  | one hrl =>
    intro v pkg ce hsp hv helab
    cases hsp with
    | one hsel =>
      have ⟨ce', h⟩ := elab_rlookup_pres hrl hsel hv helab
      have hvl := sce_sel_value hsel hv
      exact ⟨_, elabExp.elrec _ _ _ _ _ (elab_value_weaken h hvl _)⟩
  | more hok' hrl ih =>
    intro v pkg ce hsp hv helab
    cases hsp with
    | more hsp' hsel =>
      have ⟨cpkg, hpkg⟩ := ih hsp' hv helab
      have ⟨ce', h⟩ := elab_rlookup_pres hrl hsel hv helab
      have hvl := sce_sel_value hsel hv
      exact ⟨_, elabExp.edmrg _ _ _ _ _ _ _ hpkg
        (elab_value_weaken
          (elabExp.elrec SCE.Typ.top _ _ _ _ (elab_value_weaken h hvl SCE.Typ.top))
          (SCE.Value.vlrec hvl) _)⟩

-- Generalized preservation: SCE small steps preserve source types
theorem sgpreservation
    {e e' v : SCE.Exp}
    (hstep : SStep v e e') :
    ∀ {Γ A : SCE.Typ},
    SCE.HasType Γ e A
    → SCE.Value v
    → SCE.HasType .top v Γ
    → SCE.HasType Γ e' A := by
  induction hstep with
  | ssquery hval =>
    intro Γ A ⟨ce, helab⟩ hv ⟨ρc, henv⟩
    cases helab
    exact ⟨ρc, elab_value_weaken henv hv _⟩
  | ssappl hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | eapp _ _ _ _ _ _ _ h1 h2 =>
      have ⟨ce', h⟩ := ih ⟨_, h1⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabExp.eapp _ _ _ _ _ _ _ h h2⟩
  | ssboxl hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | ebox _ _ _ _ _ _ _ h1 h2 =>
      have ⟨ce', h⟩ := ih ⟨_, h1⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabExp.ebox _ _ _ _ _ _ _ h h2⟩
  | ssmrgl hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | edmrg _ _ _ _ _ _ _ h1 h2 =>
      have ⟨ce', h⟩ := ih ⟨_, h1⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabExp.edmrg _ _ _ _ _ _ _ h h2⟩
  | ssappr hv hv1 hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | eapp _ _ _ _ _ _ _ h1 h2 =>
      have ⟨ce', h⟩ := ih ⟨_, h2⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabExp.eapp _ _ _ _ _ _ _ h1 h⟩
  | ssboxr hv hv1 hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | ebox _ _ _ _ _ _ _ h1 h2 =>
      have ⟨ce', h⟩ := ih ⟨_, h2⟩ hv1 ⟨_, elab_value_weaken h1 hv1 _⟩
      exact ⟨_, elabExp.ebox _ _ _ _ _ _ _ h1 h⟩
  | ssmrgr hv hv1 hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval henvex
    obtain ⟨ρc, henv⟩ := henvex
    cases helab with
    | edmrg _ _ _ _ _ _ _ h1 h2 =>
      have h1' := elab_value_weaken h1 hv1 (Typ.and Typ.top Γ)
      have henv' : SCE.HasType .top (.mrg _ _) (Typ.and Γ _) :=
        ⟨_, elabExp.edmrg _ _ _ _ _ _ _ (elab_value_weaken henv hval _) h1'⟩
      have ⟨ce', h⟩ := ih ⟨_, h2⟩ (Value.vmrg hval hv1) henv'
      exact ⟨_, elabExp.edmrg _ _ _ _ _ _ _ h1 h⟩
  | ssclos hv =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | elam _ _ _ _ _ h1 =>
      exact ⟨_, elabExp.eclos _ _ _ _ _ _ _ _ hval henv h1⟩
  | ssbeta hv hv1 hv2 =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | eapp _ _ _ _ _ _ _ h1 h2 =>
      cases h1 with
      | eclos _ _ _ _ _ _ _ _ hval' ht hb =>
        exact ⟨_, elabExp.ebox _ _ _ _ _ _ _
          (elabExp.edmrg _ _ _ _ _ _ _
            (elab_value_weaken ht hval' _)
            (elab_value_weaken h2 hv1 _))
          hb⟩
  | ssboxv hv hv1 hv2 =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | ebox _ _ _ _ _ _ _ h1 h2 =>
      exact ⟨_, elab_value_weaken h2 hv2 _⟩
  | ssproj hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | eproj _ _ _ _ _ _ h1 hlook =>
      have ⟨ce', h⟩ := ih ⟨_, h1⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabExp.eproj _ _ _ _ _ _ h hlook⟩
  | ssprojv hv hv1 hlookv =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | eproj _ _ _ _ _ _ h1 hlook =>
      have ⟨ce', hce'⟩ := elab_lookup_pres hlook hlookv hv1 (elab_value_weaken h1 hv1 _)
      have hv' := sce_lookupv_value hlookv hv1
      exact ⟨_, elab_value_weaken hce' hv' _⟩
  | sslrec hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | elrec _ _ _ _ _ h1 =>
      have ⟨ce', h⟩ := ih ⟨_, h1⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabExp.elrec _ _ _ _ _ h⟩
  | ssrproj hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | erproj _ _ _ _ _ _ h1 hlook =>
      have ⟨ce', h⟩ := ih ⟨_, h1⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabExp.erproj _ _ _ _ _ _ h hlook⟩
  | ssrprojv hv hv1 hsel =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | erproj _ _ _ _ _ _ h1 hlook =>
      have ⟨ce', hce'⟩ := elab_rlookup_pres hlook hsel hv1 (elab_value_weaken h1 hv1 _)
      have hv' := sce_sel_value hsel hv1
      exact ⟨_, elab_value_weaken hce' hv' _⟩
  | @ssmstruct v e e' hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | mstruct _ _ _ _ h =>
      have ⟨ce', h'⟩ := ih ⟨_, h⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabExp.mstruct _ _ _ _ h'⟩
  | ssmfunctor_sandboxed hv =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab
    rename_i _ hsb_sand hsb_open h
    have heq := hsb_sand rfl; subst heq
    exact ⟨_, elabExp.mclos _ _ _ _ _ _ _ _ Value.vunit (elabExp.eunit _) h⟩
  | ssmfunctor_open hv =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab
    rename_i _ hsb_sand hsb_open h
    have heq := hsb_open rfl; subst heq
    exact ⟨_, elabExp.mclos _ _ _ _ _ _ _ _ hval henv h⟩
  | ssmappl hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | mapp _ _ _ _ _ _ _ h1 h2 =>
      have ⟨ce', h⟩ := ih ⟨_, h1⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabExp.mapp _ _ _ _ _ _ _ h h2⟩
  | ssmappr hv hv1 hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | mapp _ _ _ _ _ _ _ h1 h2 =>
      have ⟨ce', h⟩ := ih ⟨_, h2⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabExp.mapp _ _ _ _ _ _ _ h1 h⟩
  | ssmbeta hv hv1 hv2 =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | mapp _ _ _ _ _ _ _ h1 h2 =>
      cases h1 with
      | mclos _ _ _ _ _ _ _ _ hval' ht hb =>
        exact ⟨_, elabExp.ebox _ _ _ _ _ _ _
          (elabExp.edmrg _ _ _ _ _ _ _
            (elab_value_weaken ht hval' _)
            (elab_value_weaken h2 hv1 _))
          hb⟩
  | ssnmrgl hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | enmrg _ _ _ _ _ _ _ h1 h2 =>
      have ⟨ce', h⟩ := ih ⟨_, h1⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabExp.enmrg _ _ _ _ _ _ _ h h2⟩
  | ssnmrgr hv hv1 hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | enmrg _ _ _ _ _ _ _ h1 h2 =>
      have ⟨ce', h⟩ := ih ⟨_, h2⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabExp.enmrg _ _ _ _ _ _ _ h1 h⟩
  | ssnmrgv hv hv1 hv2 =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | enmrg _ _ _ _ _ _ _ h1 h2 =>
      exact ⟨_, elabExp.edmrg _ _ _ _ _ _ _
        (elab_value_weaken h1 hv1 _)
        (elab_value_weaken h2 hv2 _)⟩
  | ssletbl hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | letb _ _ _ _ _ _ _ h1 h2 =>
      have ⟨ce', h⟩ := ih ⟨_, h1⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabExp.letb _ _ _ _ _ _ _ h h2⟩
  | ssletbv hv hv1 =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | letb _ _ _ _ _ _ _ h1 h2 =>
      exact ⟨_, elabExp.ebox _ _ _ _ _ _ _
        (elabExp.edmrg _ _ _ _ _ _ _
          (elab_value_weaken henv hval _)
          (elab_value_weaken h1 hv1 _))
        h2⟩
  | ssmlinkl hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | mlink _ _ _ _ _ _ _ _ _ h1 h2 hlook =>
      have ⟨ce', h⟩ := ih ⟨_, h1⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabExp.mlink _ _ _ _ _ _ _ _ _ h h2 hlook⟩
  | ssmlinkr hv hv1 hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | mlink _ _ _ _ _ _ _ _ _ h1 h2 hlook =>
      have ⟨ce', h⟩ := ih ⟨_, h2⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabExp.mlink _ _ _ _ _ _ _ _ _ h1 h hlook⟩
  | ssmlinkbeta hv hv1 hv2 hsel =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | mlink _ _ _ _ _ _ _ _ _ h1 h2 hlook =>
      cases h2 with
      | mclos _ _ _ _ _ _ _ _ hval_v2 henv_v2 hbody =>
        have hvl := sce_sel_value hsel hv1
        have ⟨_, helab_vl⟩ := elab_rlookup_pres hlook hsel hv1 (elab_value_weaken h1 hv1 _)
        exact ⟨_, elabExp.edmrg _ _ _ _ _ _ _
          (elab_value_weaken h1 hv1 _)
          (elabExp.ebox _ _ _ _ _ _ _
            (elabExp.edmrg _ _ _ _ _ _ _
              (elab_value_weaken henv_v2 hval_v2 _)
              (elabExp.elrec _ _ _ _ _ (elab_value_weaken helab_vl hvl _)))
            hbody)⟩
  | ssopenml hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | openm _ _ _ _ _ _ _ _ h1 h2 =>
      have ⟨ce', h⟩ := ih ⟨_, h1⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabExp.openm _ _ _ _ _ _ _ _ h h2⟩
  | ssopenm hv hv' =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | openm _ _ _ _ _ _ _ _ h1 h2 =>
      cases h1 with
      | elrec _ _ _ _ _ h1_inner =>
        exact ⟨_, elabExp.ebox _ _ _ _ _ _ _
          (elabExp.edmrg _ _ _ _ _ _ _
            (elab_value_weaken henv hval _)
            (elab_value_weaken h1_inner hv' _))
          h2⟩
  | ssinl hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | einl _ _ _ _ _ h1 =>
      have ⟨ce', h⟩ := ih ⟨_, h1⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabExp.einl _ _ _ _ _ h⟩
  | ssinr hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | einr _ _ _ _ _ h1 =>
      have ⟨ce', h⟩ := ih ⟨_, h1⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabExp.einr _ _ _ _ _ h⟩
  | sscase hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | ecase _ _ _ _ _ _ _ _ _ _ h h1 h2 =>
      have ⟨ce', h'⟩ := ih ⟨_, h⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabExp.ecase _ _ _ _ _ _ _ _ _ _ h' h1 h2⟩
  | sscasel hv hv1 =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | ecase _ _ _ _ _ _ _ _ _ _ h h1 h2 =>
      cases h with
      | einl _ _ _ _ _ hinner =>
        exact ⟨_, elabExp.ebox _ _ _ _ _ _ _
          (elabExp.edmrg _ _ _ _ _ _ _
            (elab_value_weaken henv hval _)
            (elab_value_weaken hinner hv1 _))
          h1⟩
  | sscaser hv hv1 =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | ecase _ _ _ _ _ _ _ _ _ _ h h1 h2 =>
      cases h with
      | einr _ _ _ _ _ hinner =>
        exact ⟨_, elabExp.ebox _ _ _ _ _ _ _
          (elabExp.edmrg _ _ _ _ _ _ _
            (elab_value_weaken henv hval _)
            (elab_value_weaken hinner hv1 _))
          h2⟩
  | ssfclos hv =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | eflam _ _ _ _ _ h1 =>
      exact ⟨_, elabExp.efclos _ _ _ _ _ _ _ _ hval henv h1⟩
  | ssfbeta hv hv1 hv2 =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | eapp _ _ _ _ _ _ _ h1 h2 =>
      cases h1 with
      | efclos _ _ _ _ _ _ _ _ hval' ht hb =>
        exact ⟨_, elabExp.ebox _ _ _ _ _ _ _
          (elabExp.edmrg _ _ _ _ _ _ _
            (elabExp.edmrg _ _ _ _ _ _ _
              (elab_value_weaken ht hval' _)
              (elabExp.efclos _ _ _ _ _ _ _ _ hval' ht hb))
            (elab_value_weaken h2 hv1 _))
          hb⟩
  | ssfold hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | efold _ _ _ _ h1 =>
      have ⟨ce', h⟩ := ih ⟨_, h1⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabExp.efold _ _ _ _ h⟩
  | ssunfold hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | eunfold _ _ _ _ _ h1 heq =>
      have ⟨ce', h⟩ := ih ⟨_, h1⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabExp.eunfold _ _ _ _ _ h heq⟩
  | ssunfoldv hv hv1 =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | eunfold _ _ _ _ _ h1 heq =>
      subst heq
      cases h1 with
      | efold _ _ _ _ hinner => exact ⟨_, hinner⟩
  | ssmlinknl hv hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | mlinkn _ _ _ _ _ _ _ _ h1 h2 hok =>
      have ⟨ce', h⟩ := ih ⟨_, h1⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabExp.mlinkn _ _ _ _ _ _ _ _ h h2 hok⟩
  | ssmlinknr hv hv1 hstep ih =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | mlinkn _ _ _ _ _ _ _ _ h1 h2 hok =>
      have ⟨ce', h⟩ := ih ⟨_, h2⟩ hval ⟨ρc, henv⟩
      exact ⟨_, elabExp.mlinkn _ _ _ _ _ _ _ _ h1 h hok⟩
  | ssmlinknbeta hv hv1 hv2 hsp =>
    intro Γ A ⟨ce, helab⟩ hval ⟨ρc, henv⟩
    cases helab with
    | mlinkn _ _ _ _ _ _ _ _ h1 h2 hok =>
      cases h2 with
      | mclos _ _ _ _ _ _ _ _ hval_v2 henv_v2 hbody =>
        have ⟨cpkg, hpkg⟩ := selpkg_pres hok hsp hv1 (elab_value_weaken h1 hv1 _)
        have hvpkg := S_Sem.selpkg_value hsp hv1
        exact ⟨_, elabExp.edmrg _ _ _ _ _ _ _
          (elab_value_weaken h1 hv1 _)
          (elabExp.ebox _ _ _ _ _ _ _
            (elabExp.edmrg _ _ _ _ _ _ _
              (elab_value_weaken henv_v2 hval_v2 _)
              (elab_value_weaken hpkg hvpkg _))
            hbody)⟩

-- Whole-program preservation
theorem spreservation {e e' : SCE.Exp} {A : SCE.Typ}
    : SCE.HasType .top e A
    → SStep SCE.Exp.unit e e'
    → SCE.HasType .top e' A := by
  intros htyp hstep
  apply sgpreservation hstep htyp Value.vunit
  exact ⟨_, elabExp.eunit _⟩
