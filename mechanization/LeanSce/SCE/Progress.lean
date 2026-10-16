import LeanSce.SCE.Elaboration.Elaboration
import LeanSce.SCE.Semantics.SmallStep
import LeanSce.SCE.Syntax
import LeanSce.SCE.Preservation

open SCE S_Sem

-- Generalized progress: well-typed source expressions are values or can step
theorem sgprogress
    {Γ A : SCE.Typ} {e : SCE.Exp}
    (htyp : SCE.HasType Γ e A) :
    ∀ {v : SCE.Exp},
    SCE.Value v
    → SCE.HasType .top v Γ
    → SCE.Value e ∨ ∃ e', SStep v e e' := by
  obtain ⟨ce, helab⟩ := htyp
  induction helab with
  | equery =>
    intro v hv _
    right; exact ⟨v, SStep.ssquery hv⟩
  | elit =>
    intro v hv _
    left; exact Value.vint
  | eunit =>
    intro v hv _
    left; exact Value.vunit
  | @eclos _ _ _ _ se1 _ _ _ hval _ _ =>
    intro v hv _; left; exact Value.vclos hval
  | @mclos _ _ _ _ se1 _ _ _ hval _ _ =>
    intro v hv _; left; exact Value.vmclos hval
  | elam => intro v hv _; right; exact ⟨.clos v _ _, SStep.ssclos hv⟩
  | @eapp _ _ _ se1 se2 _ _ h1 h2 ih1 ih2 =>
    intro v hv henv
    have prog1 := ih1 hv henv
    have prog2 := ih2 hv henv
    match prog1 with
    | .inr ⟨e', hstep⟩ => right; exact ⟨.app e' se2, SStep.ssappl hv hstep⟩
    | .inl hve1 =>
      match prog2 with
      | .inr ⟨e', hstep⟩ => right; exact ⟨.app se1 e', SStep.ssappr hv hve1 hstep⟩
      | .inl hve2 =>
        right
        match hve1 with
        | .vclos hvc => match h1 with
          | .eclos _ _ _ _ _ _ _ _ _ _ _ => exact ⟨_, SStep.ssbeta hv hve2 hvc⟩
        | .vfclos hvc => match h1 with
          | .efclos _ _ _ _ _ _ _ _ _ _ _ => exact ⟨_, SStep.ssfbeta hv hve2 hvc⟩
        | .vint => nomatch h1
        | .vunit => nomatch h1
        | .vmrg _ _ => nomatch h1
        | .vmclos _ => nomatch h1
        | .vlrec _ => nomatch h1
        | .vinl _ => nomatch h1
        | .vinr _ => nomatch h1
  | @ebox _ _ _ se1 se2 _ _ h1 h2 ih1 ih2 =>
    intro v hv henv
    have prog1 := ih1 hv henv
    match prog1 with
    | .inr ⟨e', hstep⟩ => right; exact ⟨.box e' se2, SStep.ssboxl hv hstep⟩
    | .inl hve1 =>
      have henv2 : SCE.HasType .top se1 _ := svalue_weaken ⟨_, h1⟩ hve1 _
      have prog2 := ih2 hve1 henv2
      match prog2 with
      | .inr ⟨e', hstep⟩ => right; exact ⟨.box se1 e', SStep.ssboxr hv hve1 hstep⟩
      | .inl hve2 => right; exact ⟨_, SStep.ssboxv hv hve1 hve2⟩
  | @edmrg _ _ _ se1 se2 _ _ h1 h2 ih1 ih2 =>
    intro v hv henv
    obtain ⟨ρc, henvE⟩ := henv
    have prog1 := ih1 hv ⟨ρc, henvE⟩
    match prog1 with
    | .inr ⟨e', hstep⟩ => right; exact ⟨.mrg e' se2, SStep.ssmrgl hv hstep⟩
    | .inl hve1 =>
      have henv' : SCE.HasType .top (.mrg v se1) (Typ.and _ _) :=
        ⟨_, elabExp.edmrg _ _ _ _ _ _ _ (elab_value_weaken henvE hv _) (elab_value_weaken h1 hve1 _)⟩
      have prog2 := ih2 (Value.vmrg hv hve1) henv'
      match prog2 with
      | .inr ⟨e', hstep⟩ => right; exact ⟨.mrg se1 e', SStep.ssmrgr hv hve1 hstep⟩
      | .inl hve2 => left; exact Value.vmrg hve1 hve2
  | @eproj _ _ _ se _ _ h1 hlook ih =>
    intro v hv henv
    have prog1 := ih hv henv
    match prog1 with
    | .inr ⟨e', hstep⟩ => right; exact ⟨.proj e' _, SStep.ssproj hv hstep⟩
    | .inl hve1 =>
      right
      have ⟨v', _, hlv⟩ := slookup_progress hlook (svalue_weaken ⟨_, h1⟩ hve1 _) hve1
      exact ⟨_, SStep.ssprojv hv hve1 hlv⟩
  | @elrec _ _ se _ l _ ih =>
    intro v hv henv
    have prog := ih hv henv
    match prog with
    | .inl hve => left; exact Value.vlrec hve
    | .inr ⟨e', hstep⟩ => right; exact ⟨.lrec l e', SStep.sslrec hv hstep⟩
  | @erproj _ _ _ se _ _ h1 hlook ih =>
    intro v hv henv
    have prog1 := ih hv henv
    match prog1 with
    | .inr ⟨e', hstep⟩ => right; exact ⟨.rproj e' _, SStep.ssrproj hv hstep⟩
    | .inl hve1 =>
      right
      have ⟨v', _, hsel⟩ := sselection_progress hlook (svalue_weaken ⟨_, h1⟩ hve1 _) hve1
      exact ⟨_, SStep.ssrprojv hv hve1 hsel⟩
  | @enmrg _ _ _ se1 se2 _ _ h1 h2 ih1 ih2 =>
    intro v hv henv
    have prog1 := ih1 hv henv
    have prog2 := ih2 hv henv
    match prog1 with
    | .inr ⟨e', hstep⟩ => right; exact ⟨.nmrg e' se2, SStep.ssnmrgl hv hstep⟩
    | .inl hve1 =>
      match prog2 with
      | .inr ⟨e', hstep⟩ => right; exact ⟨.nmrg se1 e', SStep.ssnmrgr hv hve1 hstep⟩
      | .inl hve2 => right; exact ⟨.mrg se1 se2, SStep.ssnmrgv hv hve1 hve2⟩
  | @letb _ _ _ se1 se2 _ _ h1 h2 ih1 ih2 =>
    intro v hv henv
    have prog1 := ih1 hv henv
    match prog1 with
    | .inr ⟨e', hstep⟩ => right; exact ⟨.letb e' se2, SStep.ssletbl hv hstep⟩
    | .inl hve1 => right; exact ⟨.box (.mrg v se1) se2, SStep.ssletbv hv hve1⟩
  | @openm _ _ _ se1 se2 _ _ _ h1 h2 ih1 ih2 =>
    intro v hv henv
    have prog1 := ih1 hv henv
    match prog1 with
    | .inr ⟨e', hstep⟩ => right; exact ⟨.openm e' se2, SStep.ssopenml hv hstep⟩
    | .inl hve1 =>
      right
      match hve1 with
      | .vlrec hv' => exact ⟨.box (.mrg v _) se2, SStep.ssopenm hv hv'⟩
      | .vint => nomatch h1
      | .vunit => nomatch h1
      | .vmrg _ _ => nomatch h1
      | .vclos _ => nomatch h1
      | .vmclos _ => nomatch h1
      | .vinl _ => nomatch h1
      | .vinr _ => nomatch h1
      | .vfclos _ => nomatch h1
  | mstruct _ _ _ _ h ih =>
    intro v hv henv
    match ih hv henv with
    | .inl hve => exact .inl (Value.vmstruct hve)
    | .inr ⟨e', hstep⟩ => exact .inr ⟨.mstruct e', SStep.ssmstruct hv hstep⟩
  | @mfunctor _ ctxInner _ _ sb se _ hsb_sand hsb_open h ih =>
    intro v hv henv
    cases sb with
    | sandboxed => right; exact ⟨_, SStep.ssmfunctor_sandboxed hv⟩
    | open_ => right; exact ⟨_, SStep.ssmfunctor_open hv⟩
  | @mapp _ _ _ se1 se2 _ _ h1 h2 ih1 ih2 =>
    intro v hv henv
    have prog1 := ih1 hv henv
    have prog2 := ih2 hv henv
    match prog1 with
    | .inr ⟨e', hstep⟩ => right; exact ⟨.mapp e' se2, SStep.ssmappl hv hstep⟩
    | .inl hve1 =>
      match prog2 with
      | .inr ⟨e', hstep⟩ => right; exact ⟨.mapp se1 e', SStep.ssmappr hv hve1 hstep⟩
      | .inl hve2 =>
        right
        match hve1 with
        | .vmclos hvc => match h1 with
          | .mclos _ _ _ _ _ _ _ _ _ _ _ => exact ⟨_, SStep.ssmbeta hv hve2 hvc⟩
        | .vint => nomatch h1
        | .vunit => nomatch h1
        | .vmrg _ _ => nomatch h1
        | .vclos _ => nomatch h1
        | .vlrec _ => nomatch h1
        | .vinl _ => nomatch h1
        | .vinr _ => nomatch h1
        | .vfclos _ => nomatch h1
  | @mlink _ _ _ _ l se1 se2 _ _ h1 h2 hlook ih1 ih2 =>
    intro v hv henv
    have prog1 := ih1 hv henv
    have prog2 := ih2 hv henv
    match prog1 with
    | .inr ⟨e', hstep⟩ => right; exact ⟨.mlink e' se2, SStep.ssmlinkl hv hstep⟩
    | .inl hve1 =>
      match prog2 with
      | .inr ⟨e', hstep⟩ => right; exact ⟨.mlink se1 e', SStep.ssmlinkr hv hve1 hstep⟩
      | .inl hve2 =>
        right
        match hve2 with
        | .vmclos hvc =>
          cases h2 with
          | mclos _ _ _ _ _ _ _ _ _ _ _ =>
            have ⟨vl, _, hsel⟩ := sselection_progress hlook (svalue_weaken ⟨_, h1⟩ hve1 _) hve1
            exact ⟨_, SStep.ssmlinkbeta hv hve1 hvc hsel⟩
        | .vint => nomatch h2
        | .vunit => nomatch h2
        | .vmrg _ _ => nomatch h2
        | .vclos _ => nomatch h2
        | .vlrec _ => nomatch h2
        | .vinl _ => nomatch h2
        | .vinr _ => nomatch h2
        | .vfclos _ => nomatch h2
  | @mlinkn _ _ _ _ se1 se2 _ _ h1 h2 hok ih1 ih2 =>
    intro v hv henv
    have prog1 := ih1 hv henv
    have prog2 := ih2 hv henv
    match prog1 with
    | .inr ⟨e', hstep⟩ => right; exact ⟨.mlinkn e' se2, SStep.ssmlinknl hv hstep⟩
    | .inl hve1 =>
      match prog2 with
      | .inr ⟨e', hstep⟩ => right; exact ⟨.mlinkn se1 e', SStep.ssmlinknr hv hve1 hstep⟩
      | .inl hve2 =>
        right
        match hve2 with
        | .vmclos hvc =>
          cases h2 with
          | mclos _ _ _ _ _ _ _ _ _ _ _ =>
            have ⟨pkg, hsp⟩ := selpkg_prog hok (elab_value_weaken h1 hve1 _) hve1
            exact ⟨_, SStep.ssmlinknbeta hv hve1 hvc hsp⟩
        | .vint => nomatch h2
        | .vunit => nomatch h2
        | .vmrg _ _ => nomatch h2
        | .vclos _ => nomatch h2
        | .vlrec _ => nomatch h2
        | .vinl _ => nomatch h2
        | .vinr _ => nomatch h2
        | .vfclos _ => nomatch h2
        | .vfold _ => nomatch h2
  | @einl _ _ _ se _ h ih =>
    intro v hv henv
    have prog := ih hv henv
    match prog with
    | .inl hve => left; exact Value.vinl hve
    | .inr ⟨e', hstep⟩ => right; exact ⟨_, SStep.ssinl hv hstep⟩
  | @einr _ _ _ se _ h ih =>
    intro v hv henv
    have prog := ih hv henv
    match prog with
    | .inl hve => left; exact Value.vinr hve
    | .inr ⟨e', hstep⟩ => right; exact ⟨_, SStep.ssinr hv hstep⟩
  | @ecase _ _ _ _ se se1 se2 _ _ _ h h1 h2 ih ih1 ih2 =>
    intro v hv henv
    right
    have prog := ih hv henv
    match prog with
    | .inr ⟨e', hstep⟩ => exact ⟨_, SStep.sscase hv hstep⟩
    | .inl hve =>
      match hve with
      | .vinl hv1 => exact ⟨_, SStep.sscasel hv hv1⟩
      | .vinr hv1 => exact ⟨_, SStep.sscaser hv hv1⟩
      | .vint => nomatch h
      | .vunit => nomatch h
      | .vclos _ => nomatch h
      | .vmclos _ => nomatch h
      | .vmrg _ _ => nomatch h
      | .vlrec _ => nomatch h
      | .vfclos _ => nomatch h
  | @eflam _ _ _ se _ h ih =>
    intro v hv henv
    right
    exact ⟨_, SStep.ssfclos hv⟩
  | @efclos _ _ _ _ se1 _ _ _ hval _ _ =>
    intro v hv _; left; exact Value.vfclos hval
  | @efold _ _ se _ h ih =>
    intro v hv henv
    have prog := ih hv henv
    match prog with
    | .inl hve => left; exact Value.vfold hve
    | .inr ⟨e', hstep⟩ => right; exact ⟨_, SStep.ssfold hv hstep⟩
  | @eunfold _ _ _ se _ h heq ih =>
    intro v hv henv
    right
    have prog := ih hv henv
    match prog with
    | .inr ⟨e', hstep⟩ => exact ⟨_, SStep.ssunfold hv hstep⟩
    | .inl hve =>
      match hve with
      | .vfold hv1 => exact ⟨_, SStep.ssunfoldv hv hv1⟩
      | .vint => nomatch h
      | .vunit => nomatch h
      | .vclos _ => nomatch h
      | .vmclos _ => nomatch h
      | .vmrg _ _ => nomatch h
      | .vlrec _ => nomatch h
      | .vinl _ => nomatch h
      | .vinr _ => nomatch h
      | .vfclos _ => nomatch h

-- Whole-program progress
theorem sprogress {e : SCE.Exp} {A : SCE.Typ}
    : SCE.HasType .top e A
    → SCE.Value e ∨ ∃ e', SStep SCE.Exp.unit e e' := by
  intro htyp
  exact sgprogress htyp Value.vunit ⟨_, elabExp.eunit _⟩
