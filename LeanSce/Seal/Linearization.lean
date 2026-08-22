import LeanSce.Seal.Correctness

-- Bind-once (linearized) linking for λE^≤.
--
-- The seal-based combinator of Elaboration.lean re-evaluates the module expression
-- (twice for mlink, 1+n times for mlinkn).  In the pure calculus that is invisible —
-- proved by the sepcomp theorems — but under effects it is observable, which is why the
-- implementation ships bind-once combinators (SCE/Linearization.lean).  Core's bind-once
-- spelling is UNTYPEABLE in λE^≤: binding the module value puts Γ₁ into the context, and
-- the body's merge then needs Disj Γ₁ (Γ & Γ₁), which fails.  The fix is Eᵢ's own
-- fresh-label trick (their Fig. 5): bind the module wrapped as {x = m}, so the bound copy
-- has type {x : Γ₁}, disjoint from everything not mentioning the fresh label x.  The
-- freshness premises are the price of evaluate-once under a sealing discipline.
--
-- Note: the non-capturing merge needs no linearized variant at all in λE^≤ — the
-- seal-based `e₁ # ((? : Γ) ▷ e₂)` already evaluates each operand exactly once.
--
-- Coherence with the seal-based spelling is stated at the EVal level (both spellings
-- compute values related to the same source value).  Core's syntactic-equality coherence
-- is FALSE here: the two spellings apply different cast histories, and casting at a
-- top-like arrow collapses closures to generators asymmetrically.
namespace Seal

variable {Δ : SCE.BrandStore}


-- ── Freshness gives disjointness ─────────────────────────────────────────────────────

theorem cost_rcd_lin : {T : Seal.Typ} → {x : String} → {S : Seal.Typ}
    → Cost T (.rcd x S) → Seal.Lin x T
  | _, _, _, .crcd _ => Seal.Lin.rcd
  | _, _, _, .candl h => Seal.Lin.andl (cost_rcd_lin h)
  | _, _, _, .candr h => Seal.Lin.andr (cost_rcd_lin h)

theorem disj_rcd_notin {T : Seal.Typ} {x : String} {S : Seal.Typ}
    (h : ¬ Seal.Lin x T) : Seal.Disj T (.rcd x S) :=
  fun hc => h (cost_rcd_lin hc)

theorem cost_and_split : {A B C : Seal.Typ} → Cost (.and A B) C → Cost A C ∨ Cost B C
  | _, _, _, .candl h => Or.inl h
  | _, _, _, .candr h => Or.inr h
  | _, _, _, .crandl h => (cost_and_split h).imp .crandl .crandl
  | _, _, _, .crandr h => (cost_and_split h).imp .crandr .crandr

theorem disj_and_l {A B C : Seal.Typ} (h₁ : Seal.Disj A C) (h₂ : Seal.Disj B C)
    : Seal.Disj (.and A B) C :=
  fun hc => (cost_and_split hc).elim h₁ h₂

-- ── The bind-once combinator ─────────────────────────────────────────────────────────

-- linkedSealLin Γ' Γ₁' B' x l ce₁ ce₂ =
--   (λ{x:Γ₁'} → Γ₁'&B'.  ?.0.x  #  ((? : Γ'&{x:Γ₁'}) ▷ ((? : Γ') ▷ ce₂) (l = ?.0.x.l)))
--     {x = ce₁}
-- The module expression ce₁ is evaluated once; both uses read the bound value ?.0.x.
def linkedSealLin (Γ' Γ₁' B' : Seal.Typ) (x l : String) (ce₁ ce₂ : Seal.Exp) : Seal.Exp :=
  .app
    (.lam (.rcd x Γ₁') (.and Γ₁' B')
      (.mrg (.rproj (.proj .query 0) x)
        (.box (.anno .query (.and Γ' (.rcd x Γ₁')))
          (.app (.box (.anno .query Γ') ce₂)
            (.lrec l (.rproj (.rproj (.proj .query 0) x) l))))))
    (.lrec x ce₁)

-- Well-typedness of the composition term, from the units' typings alone.
theorem linkedSealLin_typed {Γ Γ₁ A B : SCE.Typ} {x l : String} {ce₁ ce₂ : Seal.Exp}
    (ht₁ : Seal.HasType (sealStore Δ) (sealTyp Γ) ce₁ (sealTyp Γ₁))
    (ht₂ : Seal.HasType (sealStore Δ) (sealTyp Γ) ce₂
      (.arr (.rcd l (sealTyp A)) (sealTyp B)))
    (hlookup : SCE.SRLookup Γ₁ l A)
    (hd₁ : Seal.Disj (sealTyp Γ₁) (sealTyp Γ))
    (hd₂ : Seal.Disj (sealTyp Γ₁) (sealTyp B))
    (hfrΓ : ¬ Seal.Lin x (sealTyp Γ))
    (hfrΓ₁ : ¬ Seal.Lin x (sealTyp Γ₁))
    : Seal.HasType (sealStore Δ) (sealTyp Γ)
        (linkedSealLin (sealTyp Γ) (sealTyp Γ₁) (sealTyp B) x l ce₁ ce₂)
        (.and (sealTyp Γ₁) (sealTyp B)) := by
  refine HasType.tapp (HasType.tlam (disj_rcd_notin hfrΓ) ?_) (HasType.trcd ht₁)
  -- body, under Γ' & {x : Γ₁'}
  refine HasType.tmrg
    (HasType.trproj (HasType.tproj HasType.tquery Lookup.zero) RLookup.zero)
    ?_ ?_ hd₂
  · -- the functor application, under (Γ' & {x:Γ₁'}) & Γ₁', sealed back to Γ' & {x:Γ₁'}
    refine HasType.tbox (HasType.tanno HasType.tquery (Sub.sandl (sub_refl _))) ?_
    refine HasType.tapp
      (HasType.tbox (HasType.tanno HasType.tquery (Sub.sandl (sub_refl _))) ht₂) ?_
    exact HasType.trcd (HasType.trproj
      (HasType.trproj (HasType.tproj HasType.tquery Lookup.zero) RLookup.zero)
      (srlookup_seal hlookup))
  · -- left branch disjoint from the extended context: Γ₁' ∗ (Γ' & {x:Γ₁'})
    exact disj_symm (disj_and_l (disj_symm hd₁) (disj_symm (disj_rcd_notin hfrΓ₁)))

-- ── Separate compilation for the bind-once spelling ──────────────────────────────────
-- The module expression evaluates exactly once; every later use reads the bound value.
-- All sub-runs are provided by seal_semantic_preservation; the rest is cast bookkeeping:
-- each restriction of a bound-extended environment collapses, via cast_merge_eq and cast
-- transitivity/determinism, to self-casts of the parts, which EVal absorbs.
theorem seal_separate_compilation_lin
    {Γ Γ₁ A B : SCE.Typ} {x l : String} {es₁ es₂ : SCE.Exp} {ce₁ ce₂ : Seal.Exp}
    {ρs vs : SCE.Exp} {ρc : Seal.Exp}
    (helab₁ : elabSeal Δ Γ es₁ Γ₁ ce₁)
    (helab₂ : elabSeal Δ Γ es₂ (.sig (.TyArrM (.rcd l A) (.TyIntf B))) ce₂)
    (hlookup : SCE.SRLookup Γ₁ l A)
    (hd₁ : Seal.Disj (sealTyp Γ₁) (sealTyp Γ))
    (hd₂ : Seal.Disj (sealTyp Γ₁) (sealTyp B))
    (hfrΓ : ¬ Seal.Lin x (sealTyp Γ))
    (hfrΓ₁ : ¬ Seal.Lin x (sealTyp Γ₁))
    (heval : S_Sem.BStep ρs (.mlink es₁ es₂) vs)
    (henv_val : SCE.Value ρs) (henv : EVal Δ Γ ρs ρc)
    : ∃ vc, MStep ρc (linkedSealLin (sealTyp Γ) (sealTyp Γ₁) (sealTyp B) x l ce₁ ce₂) vc
      ∧ EVal Δ (.and Γ₁ B) vs vc := by
  cases heval with
  | mlink _ h1 h2 hsel h3 =>
    -- the module runs ONCE, under the ambient environment
    obtain ⟨vc₁, hr₁, hEV₁⟩ := seal_semantic_preservation h1 helab₁ henv_val henv
    obtain ⟨vc₁', c₁', hEV₁'⟩ := eval_cast_ex hEV₁
    have hρv := eval_value henv
    have hv₁c := eval_value hEV₁
    have hv₁c' := eval_value hEV₁'
    have hE₁v : Value (.mrg ρc (.lrec x vc₁')) := Value.vmrg hρv (Value.vrcd hv₁c')
    have htE₁ : HasType (sealStore Δ) .top (.mrg ρc (.lrec x vc₁'))
        (.and (sealTyp Γ) (.rcd x (sealTyp Γ₁))) :=
      HasType.tmergev hρv (Value.vrcd hv₁c') (eval_typed henv)
        (HasType.trcd (eval_typed hEV₁')) (disj_rcd_notin hfrΓ)
        (disjoint_consistent hρv (Value.vrcd hv₁c') (eval_typed henv)
          (HasType.trcd (eval_typed hEV₁')) (disj_rcd_notin hfrΓ))
    -- self-cast of the beta environment E₁ at C₀, and its componentwise shape
    obtain ⟨E₁', cE₁⟩ := cast_progress hE₁v htE₁ (sub_refl _)
    cases cE₁ with
    | cmrgl hord _ => nomatch hord
    | cmrgr hord _ => nomatch hord
    | cand cz₁ cz₂ =>
      rename_i z₁ z₂
      obtain ⟨ρc'', cρ, hρ''⟩ := eval_cast_ex henv
      obtain ⟨vc₁'', c₁'', hEV₁''⟩ := eval_cast_ex hEV₁'
      have heqz₁ : z₁ = ρc'' := cast_merge_eq_l hE₁v htE₁ cz₁ cρ
      have heqz₂ : z₂ = .lrec x vc₁'' :=
        cast_merge_eq_r hE₁v htE₁ cz₂ (Cast.crcd c₁'')
      rw [heqz₁] at cz₁
      rw [heqz₂] at cz₂
      have cE₁' : Cast (.mrg ρc (.lrec x vc₁'))
          (.and (sealTyp Γ) (.rcd x (sealTyp Γ₁))) (.mrg ρc'' (.lrec x vc₁'')) :=
        Cast.cand cz₁ cz₂
      have hE₁'v : Value (.mrg ρc'' (.lrec x vc₁'')) := cast_value hE₁v cE₁'
      have htE₁' := cast_preservation cE₁' hE₁v htE₁
      -- restricting E₁' back to Γ' gives the self-cast of the ambient part
      obtain ⟨z, cz⟩ := cast_progress hE₁'v htE₁' (Sub.sandl (sub_refl _))
      have heqz : z = ρc'' :=
        cast_determinism (cast_trans cE₁' cz) hE₁v htE₁ cz₁
      rw [heqz] at cz
      -- the functor runs under the restriction
      obtain ⟨f, hrf, hEVf⟩ := seal_semantic_preservation h2 helab₂ henv_val hρ''
      have hv₁''c := eval_value hEV₁''
      have hmod_v := eval_produces_value henv_val h1
      have himp_v := S_Sem.sel_value hsel hmod_v
      -- typing of the merge-extended environment E₂ for the outer seal
      have hDC : Seal.Disj (.and (sealTyp Γ) (.rcd x (sealTyp Γ₁))) (sealTyp Γ₁) :=
        disj_and_l (disj_symm hd₁) (disj_symm (disj_rcd_notin hfrΓ₁))
      have htE₂ : HasType (sealStore Δ) .top (.mrg (.mrg ρc (.lrec x vc₁')) vc₁')
          (.and (.and (sealTyp Γ) (.rcd x (sealTyp Γ₁))) (sealTyp Γ₁)) :=
        HasType.tmergev hE₁v hv₁c' htE₁ (eval_typed hEV₁') hDC
          (disjoint_consistent hE₁v hv₁c' htE₁ (eval_typed hEV₁') hDC)
      obtain ⟨EE, cEE⟩ := cast_progress (Value.vmrg hE₁v hv₁c') htE₂
        (Sub.sandl (sub_refl _))
      have heqEE : EE = .mrg ρc'' (.lrec x vc₁'') :=
        cast_merge_eq_l (Value.vmrg hE₁v hv₁c') htE₂ cEE cE₁'
      rw [heqEE] at cEE
      -- the bound-value projection chain, under E₁' — no re-evaluation of ce₁
      have hproj₂ : MStep (.mrg ρc'' (.lrec x vc₁''))
          (.rproj (.proj .query 0) x) vc₁'' :=
        mstep_trans (mstep_rproj hE₁'v
            (mstep_trans (mstep_proj hE₁'v (mstep_one (Step.squery hE₁'v)))
              (mstep_one (Step.sprojv hE₁'v hE₁'v LookupV.lvzero))))
          (mstep_one (Step.srprojv hE₁'v (Value.vrcd hv₁''c) RLookupV.rvlzero))
      -- ... and the same chain under E₁ for the merge's left branch
      have hleft : MStep (.mrg ρc (.lrec x vc₁')) (.rproj (.proj .query 0) x) vc₁' :=
        mstep_trans (mstep_rproj hE₁v
            (mstep_trans (mstep_proj hE₁v (mstep_one (Step.squery hE₁v)))
              (mstep_one (Step.sprojv hE₁v hE₁v LookupV.lvzero))))
          (mstep_one (Step.srprojv hE₁v (Value.vrcd hv₁c') RLookupV.rvlzero))
      cases hEVf with
      | mclos hρ₂ hEVenv₂ hbody₂ hd₂' =>
        obtain ⟨wc, hwc, hEVw⟩ := eval_sel hlookup hEV₁'' hsel
        have hYrun : MStep (.mrg ρc'' (.lrec x vc₁''))
            (.lrec l (.rproj (.rproj (.proj .query 0) x) l)) (.lrec l wc) :=
          mstep_lrec hE₁'v
            (mstep_trans (mstep_rproj hE₁'v hproj₂)
              (mstep_one (Step.srprojv hE₁'v hv₁''c hwc)))
        obtain ⟨argc, hcarg, hEVarg⟩ := eval_cast_ex (EVal.rcd hEVw)
        obtain ⟨bc, hrb, hEVb⟩ := seal_semantic_preservation h3 hbody₂
          (SCE.Value.vmrg hρ₂ (SCE.Value.vlrec himp_v)) (EVal.mrg hEVenv₂ hEVarg hd₂')
        obtain ⟨rc, hcr, hEVr⟩ := eval_cast_ex hEVb
        obtain ⟨fin, cfin, hEVfin⟩ := eval_cast_ex (EVal.mrg hEV₁' hEVr hd₂)
        refine ⟨fin, ?_, hEVfin⟩
        refine mstep_trans (mstep_appl hρv (mstep_one (Step.sclos hρv))) ?_
        refine mstep_trans (mstep_appr hρv (Value.vclos hρv) (mstep_lrec hρv hr₁)) ?_
        refine beta_mstep hρv hρv (Value.vrcd hv₁c) (Cast.crcd c₁') ?_
          (Value.vmrg hv₁c' (eval_value hEVr)) cfin
        -- the lambda body: LEFT ⇓ vc₁' once, then the sealed functor application
        refine mstep_trans (mstep_mrgl hE₁v hleft) ?_
        refine mstep_mrgr hE₁v hv₁c' ?_
        refine sealbox_mstep hE₁v hv₁c' cEE ?_ (eval_value hEVr)
        refine mstep_trans (mstep_appl hE₁'v
          (sealbox_mstep (cast_value hρv cρ) (Value.vrcd hv₁''c) cz hrf
            (Value.vclos (eval_value hEVenv₂)))) ?_
        refine mstep_trans (mstep_appr hE₁'v (Value.vclos (eval_value hEVenv₂)) hYrun) ?_
        exact beta_mstep hE₁'v (eval_value hEVenv₂) (Value.vrcd (eval_value hEVw)) hcarg
          hrb (eval_value hEVb) hcr
      | gen htl hv hw =>
        simp only [sealTyp, sealModTyp] at htl
        cases htl with
        | tlarr hB' =>
          cases hw with
          | emclos hval₂ hw₁ hw₂ hdw =>
            obtain ⟨wc, hwc, hEVw⟩ := eval_sel hlookup hEV₁'' hsel
            have hYrun : MStep (.mrg ρc'' (.lrec x vc₁''))
                (.lrec l (.rproj (.rproj (.proj .query 0) x) l)) (.lrec l wc) :=
              mstep_lrec hE₁'v
                (mstep_trans (mstep_rproj hE₁'v hproj₂)
                  (mstep_one (Step.srprojv hE₁'v hv₁''c hwc)))
            obtain ⟨argc, hcarg, _⟩ := eval_cast_ex (EVal.rcd hEVw)
            obtain ⟨g', hcg⟩ := cast_progress (genVal_value _) (genVal_typed (Δ := sealStore Δ) hB' .top)
              (sub_refl _)
            have hg' := (toplike_gen_cast hB' hcg).1
            obtain ⟨wa, hwa⟩ := eval_elab (EVal.rcd hEVw)
            obtain ⟨bc', _, hEVb'⟩ := seal_semantic_preservation h3 hw₂
              (SCE.Value.vmrg hval₂ (SCE.Value.vlrec himp_v))
              (EVal.mrg (elab_eval hw₁ hval₂) (elab_eval hwa (SCE.Value.vlrec himp_v)) hdw)
            obtain ⟨wv, hwv⟩ := eval_elab hEVb'
            have hEVg := EVal.gen hB'
              (eval_produces_value (SCE.Value.vmrg hval₂ (SCE.Value.vlrec himp_v)) h3) hwv
            rw [← hg'] at hEVg
            obtain ⟨fin, cfin, hEVfin⟩ := eval_cast_ex (EVal.mrg hEV₁' hEVg hd₂)
            refine ⟨fin, ?_, hEVfin⟩
            refine mstep_trans (mstep_appl hρv (mstep_one (Step.sclos hρv))) ?_
            refine mstep_trans (mstep_appr hρv (Value.vclos hρv) (mstep_lrec hρv hr₁)) ?_
            refine beta_mstep hρv hρv (Value.vrcd hv₁c) (Cast.crcd c₁') ?_
              (Value.vmrg hv₁c' (cast_value (genVal_value _) hcg)) cfin
            refine mstep_trans (mstep_mrgl hE₁v hleft) ?_
            refine mstep_mrgr hE₁v hv₁c' ?_
            refine sealbox_mstep hE₁v hv₁c' cEE ?_ (cast_value (genVal_value _) hcg)
            refine mstep_trans (mstep_appl hE₁'v
              (sealbox_mstep (cast_value hρv cρ) (Value.vrcd hv₁''c) cz hrf
                (genVal_value _))) ?_
            refine mstep_trans (mstep_appr hE₁'v (genVal_value _) hYrun) ?_
            exact beta_mstep hE₁'v Value.vunit (Value.vrcd (eval_value hEVw)) hcarg
              MStep.refl (genVal_value _) hcg

theorem seal_separate_compilation_lin_closed
    {Γ₁ A B : SCE.Typ} {x l : String} {es₁ es₂ : SCE.Exp} {ce₁ ce₂ : Seal.Exp}
    {vs : SCE.Exp}
    (helab₁ : elabSeal Δ .top es₁ Γ₁ ce₁)
    (helab₂ : elabSeal Δ .top es₂ (.sig (.TyArrM (.rcd l A) (.TyIntf B))) ce₂)
    (hlookup : SCE.SRLookup Γ₁ l A)
    (hd₂ : Seal.Disj (sealTyp Γ₁) (sealTyp B))
    (hfrΓ₁ : ¬ Seal.Lin x (sealTyp Γ₁))
    (heval : S_Sem.BStep .unit (.mlink es₁ es₂) vs)
    : ∃ vc, MStep .unit (linkedSealLin .top (sealTyp Γ₁) (sealTyp B) x l ce₁ ce₂) vc
      ∧ EVal Δ (.and Γ₁ B) vs vc :=
  seal_separate_compilation_lin helab₁ helab₂ hlookup disj_top_r hd₂
    (fun h => nomatch h) hfrΓ₁ heval SCE.Value.vunit EVal.unit

-- ── Coherence of the two link spellings ──────────────────────────────────────────────
-- Both the seal-based (evaluate-twice) and the bind-once spellings compute values
-- related to the SAME source value.  This is the λE^≤ analogue of Core's
-- linearization_coherent — but stated at the EVal level: Core's syntactic-equality
-- coherence is false here, because the two spellings apply different cast histories and
-- top-like closures collapse to generators asymmetrically between them.
theorem linearization_coherent_seal
    {Γ Γ₁ A B : SCE.Typ} {x l : String} {es₁ es₂ : SCE.Exp} {ce₁ ce₂ : Seal.Exp}
    {ρs vs : SCE.Exp} {ρc : Seal.Exp}
    (helab₁ : elabSeal Δ Γ es₁ Γ₁ ce₁)
    (helab₂ : elabSeal Δ Γ es₂ (.sig (.TyArrM (.rcd l A) (.TyIntf B))) ce₂)
    (hlookup : SCE.SRLookup Γ₁ l A)
    (hd₁ : Seal.Disj (sealTyp Γ₁) (sealTyp Γ))
    (hd₂ : Seal.Disj (sealTyp Γ₁) (sealTyp B))
    (hfrΓ : ¬ Seal.Lin x (sealTyp Γ))
    (hfrΓ₁ : ¬ Seal.Lin x (sealTyp Γ₁))
    (heval : S_Sem.BStep ρs (.mlink es₁ es₂) vs)
    (henv_val : SCE.Value ρs) (henv : EVal Δ Γ ρs ρc)
    : ∃ vc vc',
        MStep ρc (.mrg ce₁ (.box (.anno .query (sealTyp Γ))
          (.app ce₂ (.lrec l (.rproj ce₁ l))))) vc
      ∧ MStep ρc (linkedSealLin (sealTyp Γ) (sealTyp Γ₁) (sealTyp B) x l ce₁ ce₂) vc'
      ∧ EVal Δ (.and Γ₁ B) vs vc
      ∧ EVal Δ (.and Γ₁ B) vs vc' := by
  obtain ⟨vc, hr, hEV⟩ :=
    seal_separate_compilation helab₁ helab₂ hlookup hd₁ hd₂ heval henv_val henv
  obtain ⟨vc', hr', hEV'⟩ :=
    seal_separate_compilation_lin helab₁ helab₂ hlookup hd₁ hd₂ hfrΓ hfrΓ₁ heval
      henv_val henv
  exact ⟨vc, vc', hr, hr', hEV, hEV'⟩

end Seal
