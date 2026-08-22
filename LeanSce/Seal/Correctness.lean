import LeanSce.Seal.Elaboration
import LeanSce.Seal.Sealing
import LeanSce.Seal.Abstraction
import LeanSce.SCE.Semantics
import LeanSce.SCE.Preservation
import LeanSce.SCE.Theories

-- Semantic correctness of the SCE → λE^≤ elaboration: source evaluation is simulated by
-- the elaborated evaluation, with values related by EVal — "elaboration up to top-like
-- collapse".  A syntactic simulation (target value = elaboration of source value, as in
-- SCE/Theories.lean for the Core target) is FALSE here: λE^≤'s beta casts the argument
-- and reseals the result, and casting a closure at a top-like arrow type collapses it to
-- the canonical generator.  EVal mirrors value elaboration but stores EVal-related (not
-- raw-elaborated) closure environments and admits the generator at any top-like type;
-- the key lemma is that casting at a value's own type preserves the relation.
namespace Seal

variable {Δ : SCE.BrandStore}

-- ── The simulation relation on values ────────────────────────────────────────────────

inductive EVal (Δ : SCE.BrandStore) : SCE.Typ → SCE.Exp → Seal.Exp → Prop where
  | lit {n : Nat}
    : EVal Δ .int (.lit n) (.lit n)
  | unit
    : EVal Δ .top .unit .unit
  | mrg {A B : SCE.Typ} {v₁ v₂ : SCE.Exp} {w₁ w₂ : Seal.Exp}
    : EVal Δ A v₁ w₁
    → EVal Δ B v₂ w₂
    → Seal.Disj (sealTyp A) (sealTyp B)
    → EVal Δ (.and A B) (.mrg v₁ v₂) (.mrg w₁ w₂)
  | rcd {A : SCE.Typ} {l : String} {v : SCE.Exp} {w : Seal.Exp}
    : EVal Δ A v w
    → EVal Δ (.rcd l A) (.lrec l v) (.lrec l w)
  | clos {ctx' A B : SCE.Typ} {ρs se₂ : SCE.Exp} {ρc ce₂ : Seal.Exp}
    : SCE.Value ρs
    → EVal Δ ctx' ρs ρc
    → elabSeal Δ (.and ctx' A) se₂ B ce₂
    → Seal.Disj (sealTyp ctx') (sealTyp A)
    → EVal Δ (.arr A B) (.clos ρs A se₂) (.clos ρc (sealTyp A) (sealTyp B) ce₂)
  | mclos {ctx' A B : SCE.Typ} {ρs se₂ : SCE.Exp} {ρc ce₂ : Seal.Exp}
    : SCE.Value ρs
    → EVal Δ ctx' ρs ρc
    → elabSeal Δ (.and ctx' A) se₂ B ce₂
    → Seal.Disj (sealTyp ctx') (sealTyp A)
    → EVal Δ (.sig (.TyArrM A (.TyIntf B))) (.mclos ρs A se₂)
        (.clos ρc (sealTyp A) (sealTyp B) ce₂)
  | gen {A : SCE.Typ} {vs : SCE.Exp} {w : Seal.Exp}
    : TopLike (sealTyp A)
    → SCE.Value vs
    → elabSeal Δ .top vs A w
    → EVal Δ A vs (genVal (sealTyp A))
  -- branded values (mirror of ewrap; the payloads are related at the representation
  -- type the store records)
  | wrap {R : SCE.Typ} {n : Nat} {v : SCE.Exp} {w : Seal.Exp}
    : Δ n = some R
    → EVal Δ R v w
    → EVal Δ (.brand n) (.wrap n v) (.wrap n w)
  -- unions: related under the same tag, the other component sealed pointwise
  | inl {A B : SCE.Typ} {v : SCE.Exp} {w : Seal.Exp}
    : EVal Δ A v w
    → EVal Δ (.or A B) (.inl B v) (.inl (sealTyp B) w)
  | inr {A B : SCE.Typ} {v : SCE.Exp} {w : Seal.Exp}
    : EVal Δ B v w
    → EVal Δ (.or A B) (.inr A v) (.inr (sealTyp A) w)
  -- fixpoint closures: both codomains of the target fclos are the sealed source codomain
  -- (elaboration introduces them equal, and the simulation only ever self-casts)
  | fclos {ctx' A B : SCE.Typ} {ρs se₂ : SCE.Exp} {ρc ce₂ : Seal.Exp}
    : SCE.Value ρs
    → EVal Δ ctx' ρs ρc
    → elabSeal Δ (.and (.and ctx' (.arr A B)) A) se₂ B ce₂
    → Seal.Disj (sealTyp ctx') (.arr (sealTyp A) (sealTyp B))
    → Seal.Disj (.and (sealTyp ctx') (.arr (sealTyp A) (sealTyp B))) (sealTyp A)
    → EVal Δ (.arr A B) (.fclos ρs A B se₂)
        (.fclos ρc (sealTyp A) (sealTyp B) (sealTyp B) ce₂)
  -- iso-recursive folds: payloads related at the unfolding
  | fold {T : SCE.Typ} {v : SCE.Exp} {w : Seal.Exp}
    : EVal Δ (SCE.substTyp 0 (.mu T) T) v w
    → EVal Δ (.mu T) (.fold T v) (.fold (sealTyp T) w)

theorem eval_value_src {A : SCE.Typ} {vs : SCE.Exp} {vc : Seal.Exp} (h : EVal Δ A vs vc)
    : SCE.Value vs := by
  induction h with
  | lit => exact SCE.Value.vint
  | unit => exact SCE.Value.vunit
  | mrg _ _ _ ih₁ ih₂ => exact SCE.Value.vmrg ih₁ ih₂
  | rcd _ ih => exact SCE.Value.vlrec ih
  | clos hρ _ _ _ _ => exact SCE.Value.vclos hρ
  | mclos hρ _ _ _ _ => exact SCE.Value.vmclos hρ
  | gen _ hv _ => exact hv
  | wrap _ _ ih => exact SCE.Value.vwrap ih
  | inl _ ih => exact SCE.Value.vinl ih
  | inr _ ih => exact SCE.Value.vinr ih
  | fclos hρ _ _ _ _ _ => exact SCE.Value.vfclos hρ
  | fold _ ih => exact SCE.Value.vfold ih

theorem eval_value {A : SCE.Typ} {vs : SCE.Exp} {vc : Seal.Exp} (h : EVal Δ A vs vc)
    : Seal.Value vc := by
  induction h with
  | lit => exact Value.vint
  | unit => exact Value.vunit
  | mrg _ _ _ ih₁ ih₂ => exact Value.vmrg ih₁ ih₂
  | rcd _ ih => exact Value.vrcd ih
  | clos _ _ _ _ ih => exact Value.vclos ih
  | mclos _ _ _ _ ih => exact Value.vclos ih
  | gen _ _ _ => exact genVal_value _
  | wrap _ _ ih => exact Value.vwrap ih
  | inl _ ih => exact Value.vinl ih
  | inr _ ih => exact Value.vinr ih
  | fclos _ _ _ _ _ ih => exact Value.vfclos ih
  | fold _ ih => exact Value.vfold ih

-- Every related source value still elaborates (at the empty context).
theorem eval_elab {A : SCE.Typ} {vs : SCE.Exp} {vc : Seal.Exp} (h : EVal Δ A vs vc)
    : ∃ w, elabSeal Δ .top vs A w := by
  induction h with
  | lit => exact ⟨_, elabSeal.elit .top _⟩
  | unit => exact ⟨_, elabSeal.eunit .top⟩
  | mrg h₁ h₂ hd ih₁ ih₂ =>
    obtain ⟨w₁, hw₁⟩ := ih₁
    obtain ⟨w₂, hw₂⟩ := ih₂
    exact ⟨_, elabSeal.evmrg (eval_value_src h₁) (eval_value_src h₂) hw₁ hw₂ hd⟩
  | rcd _ ih =>
    obtain ⟨w, hw⟩ := ih
    exact ⟨_, elabSeal.elrec hw⟩
  | clos hρ _ hbody hd ih =>
    obtain ⟨w, hw⟩ := ih
    exact ⟨_, elabSeal.eclos hρ hw hbody hd⟩
  | mclos hρ _ hbody hd ih =>
    obtain ⟨w, hw⟩ := ih
    exact ⟨_, elabSeal.emclos hρ hw hbody hd⟩
  | gen _ _ hw => exact ⟨_, hw⟩
  | wrap hΔ h ih =>
    obtain ⟨w, hw⟩ := ih
    exact ⟨_, elabSeal.ewrap hΔ (eval_value_src h) hw⟩
  | inl _ ih =>
    obtain ⟨w, hw⟩ := ih
    exact ⟨_, elabSeal.einl hw⟩
  | inr _ ih =>
    obtain ⟨w, hw⟩ := ih
    exact ⟨_, elabSeal.einr hw⟩
  | fclos hρ _ hbody hd₁ hd₂ ih =>
    obtain ⟨w, hw⟩ := ih
    exact ⟨_, elabSeal.efclos hρ hw hbody hd₁ hd₂⟩
  | fold _ ih =>
    obtain ⟨w, hw⟩ := ih
    exact ⟨_, elabSeal.efold hw⟩

-- Related target values inhabit the sealed type.
theorem eval_typed {A : SCE.Typ} {vs : SCE.Exp} {vc : Seal.Exp} (h : EVal Δ A vs vc)
    : Seal.HasType (sealStore Δ) .top vc (sealTyp A) := by
  induction h with
  | lit => exact HasType.tint
  | unit => exact HasType.tunit
  | mrg h₁ h₂ hd ih₁ ih₂ =>
    exact HasType.tmergev (eval_value h₁) (eval_value h₂) ih₁ ih₂ hd
      (disjoint_consistent (eval_value h₁) (eval_value h₂) ih₁ ih₂ hd)
  | rcd _ ih => exact HasType.trcd ih
  | clos _ h hbody hd ih =>
    exact HasType.tclos (eval_value h) ih hd (seal_type_preservation hbody)
      (sub_refl _) (sub_refl _)
  | mclos _ h hbody hd ih =>
    exact HasType.tclos (eval_value h) ih hd (seal_type_preservation hbody)
      (sub_refl _) (sub_refl _)
  | gen htl _ _ => exact genVal_typed htl .top
  | wrap hΔ h ih => exact HasType.twrap (sealStore_some hΔ) (eval_value h) ih
  | inl _ ih => exact HasType.tinl ih
  | inr _ ih => exact HasType.tinr ih
  | fclos _ h hbody hd₁ hd₂ ih =>
    exact HasType.tfclos (eval_value h) ih hd₁ hd₂ (seal_type_preservation hbody)
      (sub_refl _) (sub_refl _) (sub_refl _)
  | fold h ih =>
    rw [sealTyp_substTyp] at ih
    exact HasType.tfold ih

-- Raw value elaborations embed into the relation.
theorem elab_eval {Γ A : SCE.Typ} {vs : SCE.Exp} {vc : Seal.Exp}
    (h : elabSeal Δ Γ vs A vc) (hv : SCE.Value vs) : EVal Δ A vs vc := by
  induction h with
  | equery => nomatch hv
  | elit _ _ => exact EVal.lit
  | eunit _ => exact EVal.unit
  | eapp _ _ _ _ => nomatch hv
  | eproj _ _ _ => nomatch hv
  | ebox _ _ _ _ => nomatch hv
  | edmrg _ _ _ hd₂ ih₁ ih₂ =>
    cases hv with
    | vmrg hv₁ hv₂ => exact EVal.mrg (ih₁ hv₁) (ih₂ hv₂) hd₂
  | evmrg hv₁ hv₂ _ _ hd ih₁ ih₂ => exact EVal.mrg (ih₁ hv₁) (ih₂ hv₂) hd
  | enmrg _ _ _ _ _ _ => nomatch hv
  | elam _ _ _ => nomatch hv
  | erproj _ _ _ => nomatch hv
  | eclos hval h₁ h₂ hd ih₁ _ =>
    exact EVal.clos hval (ih₁ hval) h₂ hd
  | elrec _ ih =>
    cases hv with
    | vlrec hv' => exact EVal.rcd (ih hv')
  | eletb _ _ _ _ _ => nomatch hv
  | eopenm _ _ _ _ _ => nomatch hv
  | emstruct _ _ _ _ => nomatch hv
  | emfunctor _ _ _ _ _ => nomatch hv
  | emclos hval h₁ h₂ hd ih₁ _ =>
    exact EVal.mclos hval (ih₁ hval) h₂ hd
  | emapp _ _ _ _ => nomatch hv
  | emlink _ _ _ _ _ _ _ => nomatch hv
  | emlinkn _ _ _ _ _ _ _ => nomatch hv
  | ewrap hΔ hv' _ ih => exact EVal.wrap hΔ (ih hv')
  | emseal _ _ _ _ _ => nomatch hv
  | emunseal _ _ _ _ _ _ => nomatch hv
  | einl _ ih =>
    cases hv with
    | vinl hv' => exact EVal.inl (ih hv')
  | einr _ ih =>
    cases hv with
    | vinr hv' => exact EVal.inr (ih hv')
  | ecase _ _ _ _ _ _ _ _ => nomatch hv
  | eflam _ _ _ _ => nomatch hv
  | efclos hval h₁ h₂ hd₁ hd₂ ih₁ _ =>
    exact EVal.fclos hval (ih₁ hval) h₂ hd₁ hd₂
  | efold _ ih =>
    cases hv with
    | vfold hv' => exact EVal.fold (ih hv')
  | eunfold _ _ _ => nomatch hv

-- ── Generator lookups and top-like propagation ───────────────────────────────────────

theorem lookup_toplike {T : Seal.Typ} {n : Nat} {T' : Seal.Typ} (hl : Seal.Lookup T n T')
    (htl : TopLike T) : TopLike T' := by
  induction hl with
  | zero => cases htl with | tland _ h₂ => exact h₂
  | succ _ ih => cases htl with | tland h₁ _ => exact ih h₁

theorem rlookup_toplike {T : Seal.Typ} {l : String} {T' : Seal.Typ}
    (hl : Seal.RLookup T l T') (htl : TopLike T) : TopLike T' := by
  induction hl with
  | zero => cases htl with | tlrcd h => exact h
  | landl _ _ ih => cases htl with | tland h₁ _ => exact ih h₁
  | landr _ _ ih => cases htl with | tland _ h₂ => exact ih h₂

theorem genVal_lookupv {T : Seal.Typ} {n : Nat} {T' : Seal.Typ} (hl : Seal.Lookup T n T')
    : Seal.LookupV (genVal T) n (genVal T') := by
  induction hl with
  | zero => exact LookupV.lvzero
  | succ _ ih => exact LookupV.lvsucc ih

theorem genVal_rlookupv {T : Seal.Typ} {l : String} {T' : Seal.Typ}
    (hl : Seal.RLookup T l T') : Seal.RLookupV (genVal T) l (genVal T') := by
  induction hl with
  | zero => exact RLookupV.rvlzero
  | landl _ _ ih => exact RLookupV.vlandl ih
  | landr _ _ ih => exact RLookupV.vlandr ih

-- ── Casting at a value's own type preserves the relation ─────────────────────────────

theorem eval_cast_self {A : SCE.Typ} {vs : SCE.Exp} {vc vc' : Seal.Exp}
    (h : EVal Δ A vs vc) (hc : Cast vc (sealTyp A) vc') : EVal Δ A vs vc' := by
  induction h generalizing vc' with
  | lit =>
    cases hc
    exact EVal.lit
  | unit =>
    cases hc with
    | ctop => exact EVal.unit
  | mrg h₁ h₂ hd ih₁ ih₂ =>
    cases hc with
    | cmrgl hord _ => nomatch hord
    | cmrgr hord _ => nomatch hord
    | cand c₁ c₂ =>
      obtain ⟨x₁, hx₁⟩ := cast_progress (eval_value h₁) (eval_typed h₁) (sub_refl _)
      obtain ⟨x₂, hx₂⟩ := cast_progress (eval_value h₂) (eval_typed h₂) (sub_refl _)
      rw [cast_merge_eq_l (Value.vmrg (eval_value h₁) (eval_value h₂))
            (eval_typed (EVal.mrg h₁ h₂ hd)) c₁ hx₁,
          cast_merge_eq_r (Value.vmrg (eval_value h₁) (eval_value h₂))
            (eval_typed (EVal.mrg h₁ h₂ hd)) c₂ hx₂]
      exact EVal.mrg (ih₁ hx₁) (ih₂ hx₂) hd
  | rcd h ih =>
    cases hc with
    | crcd d => exact EVal.rcd (ih d)
  | clos hρ hEV hbody hd ih =>
    cases hc with
    | carrow _ _ _ => exact EVal.clos hρ hEV hbody hd
    | carrowtl htl _ _ =>
      obtain ⟨w, hw⟩ := eval_elab (EVal.clos hρ hEV hbody hd)
      exact EVal.gen (TopLike.tlarr htl) (SCE.Value.vclos hρ) hw
  | mclos hρ hEV hbody hd ih =>
    cases hc with
    | carrow _ _ _ => exact EVal.mclos hρ hEV hbody hd
    | carrowtl htl _ _ =>
      obtain ⟨w, hw⟩ := eval_elab (EVal.mclos hρ hEV hbody hd)
      exact EVal.gen (TopLike.tlarr htl) (SCE.Value.vmclos hρ) hw
  | gen htl hv hw =>
    rw [(toplike_gen_cast htl hc).1]
    exact EVal.gen htl hv hw
  | wrap hΔ h _ =>
    cases hc with
    | cwrap => exact EVal.wrap hΔ h
  | inl h ih =>
    cases hc with
    | cinl d => exact EVal.inl (ih d)
  | inr h ih =>
    cases hc with
    | cinr d => exact EVal.inr (ih d)
  | fclos hρ hEV hbody hd₁ hd₂ ih =>
    cases hc with
    | cfarrow _ _ _ => exact EVal.fclos hρ hEV hbody hd₁ hd₂
    | cfarrowtl htl _ _ =>
      obtain ⟨w, hw⟩ := eval_elab (EVal.fclos hρ hEV hbody hd₁ hd₂)
      exact EVal.gen (TopLike.tlarr htl) (SCE.Value.vfclos hρ) hw
  | fold h ih =>
    cases hc with
    | cfold => exact EVal.fold h

-- Package: cast at own type exists and stays related.
theorem eval_cast_ex {A : SCE.Typ} {vs : SCE.Exp} {vc : Seal.Exp} (h : EVal Δ A vs vc)
    : ∃ vc', Cast vc (sealTyp A) vc' ∧ EVal Δ A vs vc' := by
  obtain ⟨vc', hc⟩ := cast_progress (eval_value h) (eval_typed h) (sub_refl _)
  exact ⟨vc', hc, eval_cast_self h hc⟩

-- ── Lookup and selection transport along EVal ────────────────────────────────────────

theorem eval_lookup {A B : SCE.Typ} {n : Nat} (hl : SCE.SLookup A n B)
    : ∀ {vs v' : SCE.Exp} {vc : Seal.Exp}, EVal Δ A vs vc → S_Sem.LookupV vs n v'
    → ∃ wc, Seal.LookupV vc n wc ∧ EVal Δ B v' wc := by
  induction hl with
  | zero A₀ B₀ =>
    intro vs v' vc hEV hlv
    cases hEV with
    | mrg _ h₂ _ =>
      cases hlv with
      | dmrg_zero => exact ⟨_, LookupV.lvzero, h₂⟩
    | gen htl hv hw =>
      obtain ⟨w', hw'⟩ := elabSeal_lookup_pres (SCE.SLookup.zero A₀ B₀) hw hv hlv
      exact ⟨_, genVal_lookupv (slookup_seal (SCE.SLookup.zero A₀ B₀)),
        EVal.gen (lookup_toplike (slookup_seal (SCE.SLookup.zero A₀ B₀)) htl)
          (S_Sem.lookupv_value hlv hv) hw'⟩
  | succ A₀ B₀ n₀ C₀ hpre ih =>
    intro vs v' vc hEV hlv
    cases hEV with
    | mrg h₁ _ _ =>
      cases hlv with
      | dmrg_succ hlv' =>
        obtain ⟨wc, hwc, hEV'⟩ := ih h₁ hlv'
        exact ⟨wc, LookupV.lvsucc hwc, hEV'⟩
    | gen htl hv hw =>
      obtain ⟨w', hw'⟩ :=
        elabSeal_lookup_pres (SCE.SLookup.succ A₀ B₀ n₀ C₀ hpre) hw hv hlv
      exact ⟨_, genVal_lookupv (slookup_seal (SCE.SLookup.succ A₀ B₀ n₀ C₀ hpre)),
        EVal.gen (lookup_toplike (slookup_seal (SCE.SLookup.succ A₀ B₀ n₀ C₀ hpre)) htl)
          (S_Sem.lookupv_value hlv hv) hw'⟩

theorem eval_sel {B : SCE.Typ} {l : String} {A : SCE.Typ} (hl : SCE.SRLookup B l A)
    : ∀ {vs v' : SCE.Exp} {vc : Seal.Exp}, EVal Δ B vs vc → S_Sem.Sel vs l v'
    → ∃ wc, Seal.RLookupV vc l wc ∧ EVal Δ A v' wc := by
  induction hl with
  | zero label T =>
    intro vs v' vc hEV hsel
    cases hEV with
    | rcd h =>
      cases hsel with
      | rcd => exact ⟨_, RLookupV.rvlzero, h⟩
    | gen htl hv hw =>
      obtain ⟨w', hw'⟩ := elabSeal_sel_pres (SCE.SRLookup.zero label T) hw hv hsel
      exact ⟨_, genVal_rlookupv (srlookup_seal (SCE.SRLookup.zero label T)),
        EVal.gen (rlookup_toplike (srlookup_seal (SCE.SRLookup.zero label T)) htl)
          (S_Sem.sel_value hsel hv) hw'⟩
  | andl A' B' label T hl' hnl ih =>
    intro vs v' vc hEV hsel
    cases hEV with
    | mrg h₁ h₂ _ =>
      cases hsel with
      | dmrg_left hsel' =>
        obtain ⟨wc, hwc, hEV'⟩ := ih h₁ hsel'
        exact ⟨wc, RLookupV.vlandl hwc, hEV'⟩
      | dmrg_right hsel' =>
        obtain ⟨w₂, hw₂⟩ := eval_elab h₂
        exact (elabSeal_sel_absent hsel' hw₂ (eval_value_src h₂) hnl).elim
    | gen htl hv hw =>
      obtain ⟨w', hw'⟩ :=
        elabSeal_sel_pres (SCE.SRLookup.andl A' B' label T hl' hnl) hw hv hsel
      exact ⟨_, genVal_rlookupv (srlookup_seal (SCE.SRLookup.andl A' B' label T hl' hnl)),
        EVal.gen
          (rlookup_toplike (srlookup_seal (SCE.SRLookup.andl A' B' label T hl' hnl)) htl)
          (S_Sem.sel_value hsel hv) hw'⟩
  | andr A' B' label T hl' hnl ih =>
    intro vs v' vc hEV hsel
    cases hEV with
    | mrg h₁ h₂ _ =>
      cases hsel with
      | dmrg_right hsel' =>
        obtain ⟨wc, hwc, hEV'⟩ := ih h₂ hsel'
        exact ⟨wc, RLookupV.vlandr hwc, hEV'⟩
      | dmrg_left hsel' =>
        obtain ⟨w₁, hw₁⟩ := eval_elab h₁
        exact (elabSeal_sel_absent hsel' hw₁ (eval_value_src h₁) hnl).elim
    | gen htl hv hw =>
      obtain ⟨w', hw'⟩ :=
        elabSeal_sel_pres (SCE.SRLookup.andr A' B' label T hl' hnl) hw hv hsel
      exact ⟨_, genVal_rlookupv (srlookup_seal (SCE.SRLookup.andr A' B' label T hl' hnl)),
        EVal.gen
          (rlookup_toplike (srlookup_seal (SCE.SRLookup.andr A' B' label T hl' hnl)) htl)
          (S_Sem.sel_value hsel hv) hw'⟩
  | sig label T A' _ _ =>
    intro vs v' vc hEV hsel
    cases hEV with
    | gen _ hv hw => exact (value_elab_sig_intf hw hv).elim

-- ── Run assembly ─────────────────────────────────────────────────────────────────────

-- The full beta run of λE^≤: cast the argument, run the body under the extended closure
-- environment, reseal the result at the annotation codomain.
theorem beta_mstep {ρ env arg arg' body bres sres : Seal.Exp} {A B : Seal.Typ}
    (hρ : Value ρ) (henv : Value env) (harg : Value arg)
    (hc : Cast arg A arg') (hrun : MStep (.mrg env arg') body bres)
    (hbv : Value bres) (hcr : Cast bres B sres)
    : MStep ρ (.app (.clos env A B body) arg) sres := by
  have hvm : Value (.mrg env arg') := Value.vmrg henv (cast_value harg hc)
  refine MStep.step (Step.sbeta hρ henv harg hc) ?_
  refine mstep_trans (mstep_boxr hρ hvm (mstep_anno hvm hrun)) ?_
  refine MStep.step (Step.sboxr hρ hvm (Step.sannov hvm hbv hcr)) ?_
  exact MStep.step (Step.sboxv hρ hvm (cast_value hbv hcr)) MStep.refl

-- The fixpoint beta run: cast the argument, run the body under the environment extended
-- with the self-copy (external codomain reset to internal) and the cast argument, reseal
-- the result at the external codomain.
theorem fbeta_mstep {ρ env arg arg' body bres sres : Seal.Exp} {A B Bx : Seal.Typ}
    (hρ : Value ρ) (henv : Value env) (harg : Value arg)
    (hc : Cast arg A arg')
    (hrun : MStep (.mrg (.mrg env (.fclos env A B B body)) arg') body bres)
    (hbv : Value bres) (hcr : Cast bres Bx sres)
    : MStep ρ (.app (.fclos env A B Bx body) arg) sres := by
  have hvm : Value (.mrg (.mrg env (.fclos env A B B body)) arg') :=
    Value.vmrg (Value.vmrg henv (Value.vfclos henv)) (cast_value harg hc)
  refine MStep.step (Step.sfbeta hρ henv harg hc) ?_
  refine mstep_trans (mstep_boxr hρ hvm (mstep_anno hvm hrun)) ?_
  refine MStep.step (Step.sboxr hρ hvm (Step.sannov hvm hbv hcr)) ?_
  exact MStep.step (Step.sboxv hρ hvm (cast_value hbv hcr)) MStep.refl

-- The seal-based non-capturing evaluation: under the extended environment, (? : Γ)
-- restores the restriction and the body runs under it.
theorem sealbox_mstep {ρ v₁ ρ' body bres : Seal.Exp} {Γ : Seal.Typ}
    (hρ : Value ρ) (hv₁ : Value v₁) (hc : Cast (.mrg ρ v₁) Γ ρ')
    (hrun : MStep ρ' body bres) (hbv : Value bres)
    : MStep (.mrg ρ v₁) (.box (.anno .query Γ) body) bres := by
  have hvm : Value (.mrg ρ v₁) := Value.vmrg hρ hv₁
  have hρ' : Value ρ' := cast_value hvm hc
  refine MStep.step (Step.sboxl hvm (Step.sanno hvm (Step.squery hvm))) ?_
  refine MStep.step (Step.sboxl hvm (Step.sannov hvm hvm hc)) ?_
  refine mstep_trans (mstep_boxr hvm hρ' hrun) ?_
  exact MStep.step (Step.sboxv hvm hρ' hbv) MStep.refl

-- Restricting an EVal-extended environment back to the ambient context stays related:
-- the cast of the whole merge at Γ equals the self-cast of the ambient part
-- (cast_merge_eq_l), which EVal absorbs.  This is where A ∗ Γ pays off semantically.
theorem eval_env_restrict {Γ A : SCE.Typ} {ρs v₁s : SCE.Exp} {ρc v₁c : Seal.Exp}
    (hρ : EVal Δ Γ ρs ρc) (h₁ : EVal Δ A v₁s v₁c) (hd : Seal.Disj (sealTyp A) (sealTyp Γ))
    : ∃ ρ', Cast (.mrg ρc v₁c) (sealTyp Γ) ρ' ∧ EVal Δ Γ ρs ρ' := by
  have hty : HasType (sealStore Δ) .top (.mrg ρc v₁c) (.and (sealTyp Γ) (sealTyp A)) :=
    HasType.tmergev (eval_value hρ) (eval_value h₁) (eval_typed hρ) (eval_typed h₁)
      (disj_symm hd)
      (disjoint_consistent (eval_value hρ) (eval_value h₁) (eval_typed hρ) (eval_typed h₁)
        (disj_symm hd))
  obtain ⟨ρ', hc⟩ := cast_progress (Value.vmrg (eval_value hρ) (eval_value h₁)) hty
    (Sub.sandl (sub_refl _))
  obtain ⟨ρ'', hc''⟩ := cast_progress (eval_value hρ) (eval_typed hρ) (sub_refl _)
  have heq : ρ' = ρ'' :=
    cast_merge_eq_l (Value.vmrg (eval_value hρ) (eval_value h₁)) hty hc hc''
  refine ⟨ρ', hc, ?_⟩
  rw [heq]
  exact eval_cast_self hρ hc''

-- Source values evaluate to themselves.
theorem bstep_value_id {ρ v v' : SCE.Exp} (h : S_Sem.BStep ρ v v') (hv : SCE.Value v)
    : v' = v := by
  induction h with
  | query _ => nomatch hv
  | lit _ => rfl
  | unit _ => rfl
  | clos_val _ _ => rfl
  | mclos_val _ _ => rfl
  | proj _ _ _ _ => nomatch hv
  | lam _ => nomatch hv
  | box _ _ _ _ _ => nomatch hv
  | app_clos _ _ _ _ _ _ _ => nomatch hv
  | app_mclos _ _ _ _ _ _ _ => nomatch hv
  | dmrg _ _ _ ih₁ ih₂ =>
    cases hv with
    | vmrg hv₁ hv₂ => rw [ih₁ hv₁, ih₂ hv₂]
  | nmrg _ _ _ _ _ => nomatch hv
  | lrec _ _ ih =>
    cases hv with
    | vlrec hv' => rw [ih hv']
  | rproj _ _ _ _ => nomatch hv
  | letb _ _ _ _ _ => nomatch hv
  | openm _ _ _ _ _ => nomatch hv
  | mstruct_sandboxed _ _ _ => nomatch hv
  | mstruct_open _ _ _ => nomatch hv
  | mfunctor_sandboxed _ => nomatch hv
  | mfunctor_open _ => nomatch hv
  | mlink _ _ _ _ _ _ _ _ => nomatch hv
  | inl _ _ ih =>
    cases hv with
    | vinl hv' => rw [ih hv']
  | inr _ _ ih =>
    cases hv with
    | vinr hv' => rw [ih hv']
  | case_inl _ _ _ _ _ => nomatch hv
  | case_inr _ _ _ _ _ => nomatch hv
  | fclos_val _ _ => rfl
  | flam _ => nomatch hv
  | app_fclos _ _ _ _ _ _ _ => nomatch hv
  | fold _ _ ih =>
    cases hv with
    | vfold hv' => rw [ih hv']
  | unfold _ _ _ => nomatch hv
  | mlinkn _ _ _ _ _ _ _ _ => nomatch hv
  | wrap _ _ ih =>
    cases hv with
    | vwrap hv' => rw [ih hv']
  | mseal _ _ _ _ => nomatch hv
  | munseal _ _ _ _ => nomatch hv

-- The import package of an n-ary link: given a way to re-run the module expression under
-- any related environment (the caller's induction hypothesis), the wireArgSeal term runs
-- to a package EVal-related to the source package.
theorem wire_mstep {Γ Γ₁ : SCE.Typ} {ce₁ : Seal.Exp} {ρs v₁s : SCE.Exp} {D : SCE.Typ}
    (hw : WireOk (sealTyp Γ) Γ₁ D)
    (K : ∀ {ρc : Seal.Exp}, EVal Δ Γ ρs ρc → ∃ vc, MStep ρc ce₁ vc ∧ EVal Δ Γ₁ v₁s vc)
    : ∀ {pkgs : SCE.Exp} {ρc : Seal.Exp}, S_Sem.SelPkg v₁s D pkgs → EVal Δ Γ ρs ρc
    → ∃ pc, MStep ρc (wireArgSeal (sealTyp Γ) ce₁ D) pc ∧ EVal Δ D pkgs pc := by
  induction hw with
  | @one l A hl =>
    intro pkgs ρc hsp hρ
    cases hsp with
    | one hsel =>
      obtain ⟨vc, hrun, hEV⟩ := K hρ
      obtain ⟨wc, hwc, hEVw⟩ := eval_sel hl hEV hsel
      refine ⟨.lrec l wc, ?_, EVal.rcd hEVw⟩
      exact mstep_trans (mstep_lrec (eval_value hρ) (mstep_rproj (eval_value hρ) hrun))
        (mstep_one (Step.slrec (eval_value hρ)
          (Step.srprojv (eval_value hρ) (eval_value hEV) hwc)))
  | @more D' l A hw' hl hd₁ hd₂ ih =>
    intro pkgs ρc hsp hρ
    cases hsp with
    | more hsp' hsel =>
      obtain ⟨pc', hrunp, hEVp⟩ := ih hsp' hρ
      obtain ⟨ρ', hcast, hρ'⟩ := eval_env_restrict hρ hEVp hd₁
      obtain ⟨vc, hrun, hEV⟩ := K hρ'
      obtain ⟨wc, hwc, hEVw⟩ := eval_sel hl hEV hsel
      have hρ'v : Value ρ' :=
        cast_value (Value.vmrg (eval_value hρ) (eval_value hEVp)) hcast
      have hinner : MStep ρ' (.lrec l (.rproj ce₁ l)) (.lrec l wc) :=
        mstep_trans (mstep_lrec hρ'v (mstep_rproj hρ'v hrun))
          (mstep_one (Step.slrec hρ'v (Step.srprojv hρ'v (eval_value hEV) hwc)))
      refine ⟨.mrg pc' (.lrec l wc), ?_, EVal.mrg hEVp (EVal.rcd hEVw) hd₂⟩
      refine mstep_trans (mstep_mrgl (eval_value hρ) hrunp) ?_
      exact mstep_mrgr (eval_value hρ) (eval_value hEVp)
        (sealbox_mstep (eval_value hρ) (eval_value hEVp) hcast hinner
          (Value.vrcd (eval_value hEVw)))

-- ── The sealing coercions simulate each other ────────────────────────────────────────

-- Source `SSealV` is simulated by target `SealV` on EVal-related values, structurally on
-- the signature.  At arrows both sides build proxy closures; the two proxies are related
-- by EVal.clos directly (the proxy body elaborates rule-for-rule, and the proxy
-- environment is EVal-related because the underlying closures are), so no induction is
-- needed there.  Generator-shaped target values (EVal.gen) are re-split along the
-- signature; TopLike never holds at a brand, so wrappers are never generators.
theorem eval_sealv {n : Nat} {R S : SCE.Typ} {v w : SCE.Exp}
    (hs : S_Sem.SSealV n R S v w)
    : ∀ {vc : Seal.Exp}, Δ n = some R → NoRes (sealTyp R) → WfSig n (sealTyp R) (sealTyp S)
    → EVal Δ (SCE.substBrand n R S) v vc
    → ∃ wc, SealV n (sealTyp R) (sealTyp S) vc wc ∧ EVal Δ S w wc := by
  induction hs with
  | brand_eq =>
    intro vc hΔ _ _ h
    simp only [SCE.substBrand, if_true] at h
    exact ⟨_, SealV.brand_eq, EVal.wrap hΔ h⟩
  | brand_ne hne =>
    intro vc _ _ _ h
    simp only [SCE.substBrand, hne, if_false] at h
    exact ⟨_, SealV.brand_ne hne, h⟩
  | int =>
    intro vc _ _ _ h
    cases h with
    | lit => exact ⟨_, SealV.int, EVal.lit⟩
    | gen htl _ _ => nomatch htl
  | top =>
    intro vc _ _ _ _
    exact ⟨_, SealV.top, EVal.unit⟩
  | @and A B v₁ v₂ w₁ w₂ _ _ ih₁ ih₂ =>
    intro vc hΔ hnr hwf h
    cases hwf with
    | and hwf₁ hwf₂ hd _ =>
      simp only [SCE.substBrand] at h
      cases h with
      | mrg h₁ h₂ _ =>
        obtain ⟨wc₁, hs₁, he₁⟩ := ih₁ hΔ hnr hwf₁ h₁
        obtain ⟨wc₂, hs₂, he₂⟩ := ih₂ hΔ hnr hwf₂ h₂
        exact ⟨_, SealV.and hs₁ hs₂, EVal.mrg he₁ he₂ hd⟩
      | gen htl hv hw =>
        cases htl with
        | tland htl₁ htl₂ =>
          cases hv with
          | vmrg hv₁ hv₂ =>
            have hg : ∃ w₁' w₂', elabSeal Δ .top v₁ (SCE.substBrand n R A) w₁'
                ∧ elabSeal Δ .top v₂ (SCE.substBrand n R B) w₂' := by
              cases hw with
              | edmrg h₁ h₂ _ _ => exact ⟨_, _, h₁, elabSeal_weaken h₂ hv₂ .top⟩
              | evmrg _ _ h₁ h₂ _ => exact ⟨_, _, h₁, h₂⟩
            obtain ⟨w₁', w₂', hw₁, hw₂⟩ := hg
            obtain ⟨wc₁, hs₁, he₁⟩ := ih₁ hΔ hnr hwf₁ (EVal.gen htl₁ hv₁ hw₁)
            obtain ⟨wc₂, hs₂, he₂⟩ := ih₂ hΔ hnr hwf₂ (EVal.gen htl₂ hv₂ hw₂)
            exact ⟨_, SealV.and hs₁ hs₂, EVal.mrg he₁ he₂ hd⟩
  | rcd _ ih =>
    intro vc hΔ hnr hwf h
    cases hwf with
    | rcd _ hwf' =>
      simp only [SCE.substBrand] at h
      cases h with
      | rcd h' =>
        obtain ⟨wc, hs', he⟩ := ih hΔ hnr hwf' h'
        exact ⟨_, SealV.rcd hs', EVal.rcd he⟩
      | gen htl hv hw =>
        cases htl with
        | tlrcd htl' =>
          cases hv with
          | vlrec hv' =>
            cases hw with
            | elrec hw' =>
              obtain ⟨wc, hs', he⟩ := ih hΔ hnr hwf' (EVal.gen htl' hv' hw')
              exact ⟨_, SealV.rcd hs', EVal.rcd he⟩
  | @arr A B c =>
    intro vc hΔ hnr hwf h
    cases hwf with
    | arr hwfA hwfB =>
      simp only [SCE.substBrand] at h
      refine ⟨_, SealV.arr, ?_⟩
      refine EVal.clos (SCE.Value.vmrg SCE.Value.vunit (SCE.Value.vlrec (eval_value_src h)))
        (EVal.mrg EVal.unit (EVal.rcd h) disj_top) ?_ (disj_proxyEnv (wfsig_nores hwfA))
      exact elabSeal.emseal hΔ hnr hwfB
        (elabSeal.eapp
          (elabSeal.erproj
            (elabSeal.eproj elabSeal.equery (SCE.SLookup.succ _ _ _ _ (SCE.SLookup.zero _ _)))
            (SCE.SRLookup.zero _ _))
          (elabSeal.emunseal hΔ hnr hwfA (elabSeal.eproj elabSeal.equery (SCE.SLookup.zero _ _))
            rfl))
  | @sig A B c =>
    intro vc hΔ hnr hwf h
    simp only [SCE.substBrand, SCE.substBrandModTyp] at h
    cases hwf with
    | arr hwfA hwfB =>
      refine ⟨_, SealV.arr, ?_⟩
      refine EVal.mclos (SCE.Value.vmrg SCE.Value.vunit (SCE.Value.vlrec (eval_value_src h)))
        (EVal.mrg EVal.unit (EVal.rcd h) disj_top) ?_ (disj_proxyEnv (wfsig_nores hwfA))
      exact elabSeal.emseal hΔ hnr hwfB
        (elabSeal.emapp
          (elabSeal.erproj
            (elabSeal.eproj elabSeal.equery (SCE.SLookup.succ _ _ _ _ (SCE.SLookup.zero _ _)))
            (SCE.SRLookup.zero _ _))
          (elabSeal.emunseal hΔ hnr hwfA (elabSeal.eproj elabSeal.equery (SCE.SLookup.zero _ _))
            rfl))
  | @inl A B v w _ ih =>
    intro vc hΔ hnr hwf h
    cases hwf with
    | or hwfA hwfB =>
      simp only [SCE.substBrand] at h
      cases h with
      | inl h' =>
        obtain ⟨wc, hs', he⟩ := ih hΔ hnr hwfA h'
        refine ⟨_, ?_, EVal.inl he⟩
        rw [sealTyp_substBrand n R B]
        exact SealV.inl hs'
      | gen htl _ _ => nomatch htl
  | @inr A B v w _ ih =>
    intro vc hΔ hnr hwf h
    cases hwf with
    | or hwfA hwfB =>
      simp only [SCE.substBrand] at h
      cases h with
      | inr h' =>
        obtain ⟨wc, hs', he⟩ := ih hΔ hnr hwfB h'
        refine ⟨_, ?_, EVal.inr he⟩
        rw [sealTyp_substBrand n R A]
        exact SealV.inr hs'
      | gen htl _ _ => nomatch htl
  | var =>
    intro vc _ _ _ h
    cases h with
    | gen htl _ _ => nomatch htl
  | @mu T v =>
    intro vc hΔ hnr hwf h
    cases hwf with
    | mu hnin _ =>
      rw [sce_substBrand_notin hnin] at h
      exact ⟨_, SealV.mu, h⟩

-- The converse: source `SUnsealV` is simulated by target `UnsealV`.
theorem eval_unsealv {n : Nat} {R S : SCE.Typ} {v w : SCE.Exp}
    (hs : S_Sem.SUnsealV n R S v w)
    : ∀ {vc : Seal.Exp}, Δ n = some R → NoRes (sealTyp R) → WfSig n (sealTyp R) (sealTyp S)
    → EVal Δ S v vc
    → ∃ wc, UnsealV n (sealTyp R) (sealTyp S) vc wc ∧ EVal Δ (SCE.substBrand n R S) w wc := by
  induction hs with
  | brand_eq =>
    intro vc hΔ _ _ h
    cases h with
    | wrap hΔ' h' =>
      rw [hΔ] at hΔ'
      cases hΔ'
      refine ⟨_, UnsealV.brand_eq, ?_⟩
      simp only [SCE.substBrand, if_true]
      exact h'
    | gen htl _ _ => nomatch htl
  | brand_ne hne =>
    intro vc _ _ _ h
    refine ⟨_, UnsealV.brand_ne hne, ?_⟩
    simp only [SCE.substBrand, hne, if_false]
    exact h
  | int =>
    intro vc _ _ _ h
    cases h with
    | lit => exact ⟨_, UnsealV.int, EVal.lit⟩
    | gen htl _ _ => nomatch htl
  | top =>
    intro vc _ _ _ _
    exact ⟨_, UnsealV.top, EVal.unit⟩
  | @and A B v₁ v₂ w₁ w₂ _ _ ih₁ ih₂ =>
    intro vc hΔ hnr hwf h
    cases hwf with
    | and hwf₁ hwf₂ _ hd =>
      rw [← sealTyp_substBrand, ← sealTyp_substBrand] at hd
      cases h with
      | mrg h₁ h₂ _ =>
        obtain ⟨wc₁, hs₁, he₁⟩ := ih₁ hΔ hnr hwf₁ h₁
        obtain ⟨wc₂, hs₂, he₂⟩ := ih₂ hΔ hnr hwf₂ h₂
        refine ⟨_, UnsealV.and hs₁ hs₂, ?_⟩
        simp only [SCE.substBrand]
        exact EVal.mrg he₁ he₂ hd
      | gen htl hv hw =>
        cases htl with
        | tland htl₁ htl₂ =>
          cases hv with
          | vmrg hv₁ hv₂ =>
            have hg : ∃ w₁' w₂', elabSeal Δ .top v₁ A w₁' ∧ elabSeal Δ .top v₂ B w₂' := by
              cases hw with
              | edmrg h₁ h₂ _ _ => exact ⟨_, _, h₁, elabSeal_weaken h₂ hv₂ .top⟩
              | evmrg _ _ h₁ h₂ _ => exact ⟨_, _, h₁, h₂⟩
            obtain ⟨w₁', w₂', hw₁, hw₂⟩ := hg
            obtain ⟨wc₁, hs₁, he₁⟩ := ih₁ hΔ hnr hwf₁ (EVal.gen htl₁ hv₁ hw₁)
            obtain ⟨wc₂, hs₂, he₂⟩ := ih₂ hΔ hnr hwf₂ (EVal.gen htl₂ hv₂ hw₂)
            refine ⟨_, UnsealV.and hs₁ hs₂, ?_⟩
            simp only [SCE.substBrand]
            exact EVal.mrg he₁ he₂ hd
  | rcd _ ih =>
    intro vc hΔ hnr hwf h
    cases hwf with
    | rcd _ hwf' =>
      cases h with
      | rcd h' =>
        obtain ⟨wc, hs', he⟩ := ih hΔ hnr hwf' h'
        refine ⟨_, UnsealV.rcd hs', ?_⟩
        simp only [SCE.substBrand]
        exact EVal.rcd he
      | gen htl hv hw =>
        cases htl with
        | tlrcd htl' =>
          cases hv with
          | vlrec hv' =>
            cases hw with
            | elrec hw' =>
              obtain ⟨wc, hs', he⟩ := ih hΔ hnr hwf' (EVal.gen htl' hv' hw')
              refine ⟨_, UnsealV.rcd hs', ?_⟩
              simp only [SCE.substBrand]
              exact EVal.rcd he
  | @arr A B c =>
    intro vc hΔ hnr hwf h
    cases hwf with
    | arr hwfA hwfB =>
      refine ⟨_, UnsealV.arr, ?_⟩
      rw [← sealTyp_substBrand n R A, ← sealTyp_substBrand n R B]
      simp only [SCE.substBrand]
      refine EVal.clos (SCE.Value.vmrg SCE.Value.vunit (SCE.Value.vlrec (eval_value_src h)))
        (EVal.mrg EVal.unit (EVal.rcd h) disj_top) ?_ ?_
      · exact elabSeal.emunseal hΔ hnr hwfB
          (elabSeal.eapp
            (elabSeal.erproj
              (elabSeal.eproj elabSeal.equery (SCE.SLookup.succ _ _ _ _ (SCE.SLookup.zero _ _)))
              (SCE.SRLookup.zero _ _))
            (elabSeal.emseal hΔ hnr hwfA (elabSeal.eproj elabSeal.equery (SCE.SLookup.zero _ _))))
          rfl
      · rw [sealTyp_substBrand]
        exact disj_proxyEnv (nores_subst hnr (wfsig_nores hwfA))
  | @sig A B c =>
    intro vc hΔ hnr hwf h
    cases hwf with
    | arr hwfA hwfB =>
      refine ⟨_, UnsealV.arr, ?_⟩
      simp only [sealTyp, sealModTyp]
      rw [← sealTyp_substBrand n R A, ← sealTyp_substBrand n R B]
      simp only [SCE.substBrand, SCE.substBrandModTyp]
      refine EVal.mclos (SCE.Value.vmrg SCE.Value.vunit (SCE.Value.vlrec (eval_value_src h)))
        (EVal.mrg EVal.unit (EVal.rcd h) disj_top) ?_ ?_
      · exact elabSeal.emunseal hΔ hnr hwfB
          (elabSeal.emapp
            (elabSeal.erproj
              (elabSeal.eproj elabSeal.equery (SCE.SLookup.succ _ _ _ _ (SCE.SLookup.zero _ _)))
              (SCE.SRLookup.zero _ _))
            (elabSeal.emseal hΔ hnr hwfA (elabSeal.eproj elabSeal.equery (SCE.SLookup.zero _ _))))
          rfl
      · rw [sealTyp_substBrand]
        exact disj_proxyEnv (nores_subst hnr (wfsig_nores hwfA))
  | @inl A B v w _ ih =>
    intro vc hΔ hnr hwf h
    cases hwf with
    | or hwfA hwfB =>
      cases h with
      | inl h' =>
        obtain ⟨wc, hs', he⟩ := ih hΔ hnr hwfA h'
        refine ⟨_, UnsealV.inl hs', ?_⟩
        simp only [SCE.substBrand]
        rw [← sealTyp_substBrand n R B]
        exact EVal.inl he
      | gen htl _ _ => nomatch htl
  | @inr A B v w _ ih =>
    intro vc hΔ hnr hwf h
    cases hwf with
    | or hwfA hwfB =>
      cases h with
      | inr h' =>
        obtain ⟨wc, hs', he⟩ := ih hΔ hnr hwfB h'
        refine ⟨_, UnsealV.inr hs', ?_⟩
        simp only [SCE.substBrand]
        rw [← sealTyp_substBrand n R A]
        exact EVal.inr he
      | gen htl _ _ => nomatch htl
  | var =>
    intro vc _ _ _ h
    cases h with
    | gen htl _ _ => nomatch htl
  | @mu T v =>
    intro vc hΔ hnr hwf h
    cases hwf with
    | mu hnin _ =>
      rw [sce_substBrand_notin hnin]
      exact ⟨_, UnsealV.mu, h⟩

-- ── Semantic preservation ────────────────────────────────────────────────────────────

-- Source evaluation is simulated by the elaborated λE^≤ evaluation, with results related
-- by EVal.  (The Core-target analogue concludes with a syntactic elaboration of the
-- source value; here the reseals force the relation instead.)
theorem seal_semantic_preservation {ρs es vs : SCE.Exp} (heval : S_Sem.BStep ρs es vs)
    : ∀ {Γ A : SCE.Typ} {ce ρc : Seal.Exp},
      elabSeal Δ Γ es A ce → SCE.Value ρs → EVal Δ Γ ρs ρc
    → ∃ vc, MStep ρc ce vc ∧ EVal Δ A vs vc := by
  induction heval with
  | query _ =>
    intro Γ A ce ρc helab henv_val henv
    cases helab
    exact ⟨ρc, mstep_one (Step.squery (eval_value henv)), henv⟩
  | lit _ =>
    intro Γ A ce ρc helab henv_val henv
    cases helab
    exact ⟨_, MStep.refl, EVal.lit⟩
  | unit _ =>
    intro Γ A ce ρc helab henv_val henv
    cases helab
    exact ⟨_, MStep.refl, EVal.unit⟩
  | clos_val _ hval =>
    intro Γ A ce ρc helab henv_val henv
    cases helab with
    | eclos hval' h₁ h₂ hd =>
      exact ⟨_, MStep.refl, EVal.clos hval' (elab_eval h₁ hval') h₂ hd⟩
  | mclos_val _ hval =>
    intro Γ A ce ρc helab henv_val henv
    cases helab with
    | emclos hval' h₁ h₂ hd =>
      exact ⟨_, MStep.refl, EVal.mclos hval' (elab_eval h₁ hval') h₂ hd⟩
  | proj _ h1 hlv ih =>
    intro Γ A ce ρc helab henv_val henv
    cases helab with
    | eproj h hsl =>
      obtain ⟨vc, hrun, hEV⟩ := ih h henv_val henv
      obtain ⟨wc, hwc, hEV'⟩ := eval_lookup hsl hEV hlv
      exact ⟨wc, mstep_trans (mstep_proj (eval_value henv) hrun)
        (mstep_one (Step.sprojv (eval_value henv) (eval_value hEV) hwc)), hEV'⟩
  | lam _ =>
    intro Γ A ce ρc helab henv_val henv
    cases helab with
    | elam hbody hd =>
      exact ⟨_, mstep_one (Step.sclos (eval_value henv)),
        EVal.clos henv_val henv hbody hd⟩
  | box _ h1 h2 ih1 ih2 =>
    intro Γ A ce ρc helab henv_val henv
    cases helab with
    | ebox ha hb =>
      obtain ⟨g, hrg, hEVg⟩ := ih1 ha henv_val henv
      obtain ⟨w, hrw, hEVw⟩ := ih2 hb (eval_produces_value henv_val h1) hEVg
      exact ⟨w, mstep_trans (mstep_boxl (eval_value henv) hrg)
        (mstep_trans (mstep_boxr (eval_value henv) (eval_value hEVg) hrw)
          (mstep_one (Step.sboxv (eval_value henv) (eval_value hEVg) (eval_value hEVw)))),
        hEVw⟩
  | app_clos _ h1 h2 h3 ih1 ih2 ih3 =>
    intro Γ A ce ρc helab henv_val henv
    cases helab with
    | eapp ha hb =>
      obtain ⟨fc, hrf, hEVf⟩ := ih1 ha henv_val henv
      obtain ⟨ac, hra, hEVa⟩ := ih2 hb henv_val henv
      have harg_v := eval_produces_value henv_val h2
      cases hEVf with
      | clos hρ₁ hEVenv hbody hd =>
        obtain ⟨ac', hca, hEVa'⟩ := eval_cast_ex hEVa
        obtain ⟨bc, hrb, hEVb⟩ := ih3 hbody (SCE.Value.vmrg hρ₁ harg_v)
          (EVal.mrg hEVenv hEVa' hd)
        obtain ⟨rc, hcr, hEVr⟩ := eval_cast_ex hEVb
        exact ⟨rc, mstep_trans (mstep_appl (eval_value henv) hrf)
          (mstep_trans (mstep_appr (eval_value henv) (Value.vclos (eval_value hEVenv)) hra)
            (beta_mstep (eval_value henv) (eval_value hEVenv) (eval_value hEVa) hca hrb
              (eval_value hEVb) hcr)), hEVr⟩
      | gen htl hv hw =>
        simp only [sealTyp] at htl
        cases htl with
        | tlarr hB' =>
          obtain ⟨ac', hca, _⟩ := eval_cast_ex hEVa
          obtain ⟨g', hcg⟩ := cast_progress (genVal_value _) (genVal_typed (Δ := sealStore Δ) hB' .top)
            (sub_refl _)
          have hg' := (toplike_gen_cast hB' hcg).1
          -- the source result still elaborates: rerun the body IH on the raw elaboration
          cases hw with
          | eclos hval₁ hw₁ hw₂ hdw =>
            obtain ⟨wa, hwa⟩ := eval_elab hEVa
            obtain ⟨bc', _, hEVb'⟩ := ih3 hw₂ (SCE.Value.vmrg hval₁ harg_v)
              (EVal.mrg (elab_eval hw₁ hval₁) (elab_eval hwa harg_v) hdw)
            obtain ⟨wv, hwv⟩ := eval_elab hEVb'
            refine ⟨g', mstep_trans (mstep_appl (eval_value henv) hrf)
              (mstep_trans (mstep_appr (eval_value henv) (genVal_value _) hra)
                (beta_mstep (eval_value henv) Value.vunit (eval_value hEVa) hca
                  MStep.refl (genVal_value _) hcg)), ?_⟩
            rw [hg']
            exact EVal.gen hB' (eval_produces_value (SCE.Value.vmrg hval₁ harg_v) h3) hwv
  | app_mclos _ h1 h2 h3 ih1 ih2 ih3 =>
    intro Γ A ce ρc helab henv_val henv
    cases helab with
    | emapp ha hb =>
      obtain ⟨fc, hrf, hEVf⟩ := ih1 ha henv_val henv
      obtain ⟨ac, hra, hEVa⟩ := ih2 hb henv_val henv
      have harg_v := eval_produces_value henv_val h2
      cases hEVf with
      | mclos hρ₁ hEVenv hbody hd =>
        obtain ⟨ac', hca, hEVa'⟩ := eval_cast_ex hEVa
        obtain ⟨bc, hrb, hEVb⟩ := ih3 hbody (SCE.Value.vmrg hρ₁ harg_v)
          (EVal.mrg hEVenv hEVa' hd)
        obtain ⟨rc, hcr, hEVr⟩ := eval_cast_ex hEVb
        exact ⟨rc, mstep_trans (mstep_appl (eval_value henv) hrf)
          (mstep_trans (mstep_appr (eval_value henv) (Value.vclos (eval_value hEVenv)) hra)
            (beta_mstep (eval_value henv) (eval_value hEVenv) (eval_value hEVa) hca hrb
              (eval_value hEVb) hcr)), hEVr⟩
      | gen htl hv hw =>
        simp only [sealTyp, sealModTyp] at htl
        cases htl with
        | tlarr hB' =>
          obtain ⟨ac', hca, _⟩ := eval_cast_ex hEVa
          obtain ⟨g', hcg⟩ := cast_progress (genVal_value _) (genVal_typed (Δ := sealStore Δ) hB' .top)
            (sub_refl _)
          have hg' := (toplike_gen_cast hB' hcg).1
          cases hw with
          | emclos hval₁ hw₁ hw₂ hdw =>
            obtain ⟨wa, hwa⟩ := eval_elab hEVa
            obtain ⟨bc', _, hEVb'⟩ := ih3 hw₂ (SCE.Value.vmrg hval₁ harg_v)
              (EVal.mrg (elab_eval hw₁ hval₁) (elab_eval hwa harg_v) hdw)
            obtain ⟨wv, hwv⟩ := eval_elab hEVb'
            refine ⟨g', mstep_trans (mstep_appl (eval_value henv) hrf)
              (mstep_trans (mstep_appr (eval_value henv) (genVal_value _) hra)
                (beta_mstep (eval_value henv) Value.vunit (eval_value hEVa) hca
                  MStep.refl (genVal_value _) hcg)), ?_⟩
            rw [hg']
            exact EVal.gen hB' (eval_produces_value (SCE.Value.vmrg hval₁ harg_v) h3) hwv
  | dmrg _ h1 h2 ih1 ih2 =>
    intro Γ A ce ρc helab henv_val henv
    cases helab with
    | edmrg ha hb hd1 hd2 =>
      obtain ⟨a, hra, hEVa⟩ := ih1 ha henv_val henv
      obtain ⟨b, hrb, hEVb⟩ := ih2 hb
        (SCE.Value.vmrg henv_val (eval_produces_value henv_val h1))
        (EVal.mrg henv hEVa (disj_symm hd1))
      exact ⟨.mrg a b, mstep_trans (mstep_mrgl (eval_value henv) hra)
        (mstep_mrgr (eval_value henv) (eval_value hEVa) hrb),
        EVal.mrg hEVa hEVb hd2⟩
    | evmrg hv1 hv2 hw1 hw2 hd =>
      have he1 := bstep_value_id h1 hv1
      have he2 := bstep_value_id h2 hv2
      subst he1
      subst he2
      exact ⟨_, MStep.refl, elab_eval (elabSeal.evmrg (ctx := .top) hv1 hv2 hw1 hw2 hd)
        (SCE.Value.vmrg hv1 hv2)⟩
  | nmrg _ h1 h2 ih1 ih2 =>
    intro Γ A ce ρc helab henv_val henv
    cases helab with
    | enmrg ha hb hd1 hd2 =>
      obtain ⟨a, hra, hEVa⟩ := ih1 ha henv_val henv
      obtain ⟨ρ', hcast, hρ'⟩ := eval_env_restrict henv hEVa hd1
      obtain ⟨b, hrb, hEVb⟩ := ih2 hb henv_val hρ'
      exact ⟨.mrg a b, mstep_trans (mstep_mrgl (eval_value henv) hra)
        (mstep_mrgr (eval_value henv) (eval_value hEVa)
          (sealbox_mstep (eval_value henv) (eval_value hEVa) hcast hrb (eval_value hEVb))),
        EVal.mrg hEVa hEVb hd2⟩
  | lrec _ h1 ih =>
    intro Γ A ce ρc helab henv_val henv
    cases helab with
    | elrec h =>
      obtain ⟨w, hrw, hEVw⟩ := ih h henv_val henv
      exact ⟨_, mstep_lrec (eval_value henv) hrw, EVal.rcd hEVw⟩
  | rproj _ h1 hsel ih =>
    intro Γ A ce ρc helab henv_val henv
    cases helab with
    | erproj h hsl =>
      obtain ⟨vc, hrun, hEV⟩ := ih h henv_val henv
      obtain ⟨wc, hwc, hEV'⟩ := eval_sel hsl hEV hsel
      exact ⟨wc, mstep_trans (mstep_rproj (eval_value henv) hrun)
        (mstep_one (Step.srprojv (eval_value henv) (eval_value hEV) hwc)), hEV'⟩
  | letb _ h1 h2 ih1 ih2 =>
    intro Γ A ce ρc helab henv_val henv
    cases helab with
    | eletb ha hb hd =>
      obtain ⟨a, hra, hEVa⟩ := ih1 ha henv_val henv
      obtain ⟨a', hca, hEVa'⟩ := eval_cast_ex hEVa
      obtain ⟨b, hrb, hEVb⟩ := ih2 hb
        (SCE.Value.vmrg henv_val (eval_produces_value henv_val h1))
        (EVal.mrg henv hEVa' hd)
      obtain ⟨r, hcr, hEVr⟩ := eval_cast_ex hEVb
      exact ⟨r, mstep_trans (mstep_appl (eval_value henv)
          (mstep_one (Step.sclos (eval_value henv))))
        (mstep_trans (mstep_appr (eval_value henv) (Value.vclos (eval_value henv)) hra)
          (beta_mstep (eval_value henv) (eval_value henv) (eval_value hEVa) hca hrb
            (eval_value hEVb) hcr)), hEVr⟩
  | openm _ h1 h2 ih1 ih2 =>
    intro Γ A ce ρc helab henv_val henv
    cases helab with
    | eopenm ha hb hd =>
      obtain ⟨m, hrm, hEVm⟩ := ih1 ha henv_val henv
      have himp_v := S_Sem.sel_value S_Sem.Sel.rcd (eval_produces_value henv_val h1)
      cases hEVm with
      | rcd hEVw =>
        obtain ⟨a', hca, hEVa'⟩ := eval_cast_ex hEVw
        obtain ⟨b, hrb, hEVb⟩ := ih2 hb (SCE.Value.vmrg henv_val himp_v)
          (EVal.mrg henv hEVa' hd)
        obtain ⟨r, hcr, hEVr⟩ := eval_cast_ex hEVb
        refine ⟨r, ?_, hEVr⟩
        refine mstep_trans (mstep_appl (eval_value henv)
          (mstep_one (Step.sclos (eval_value henv)))) ?_
        refine mstep_trans (mstep_appr (eval_value henv) (Value.vclos (eval_value henv))
          (mstep_trans (mstep_rproj (eval_value henv) hrm)
            (mstep_one (Step.srprojv (eval_value henv)
              (Value.vrcd (eval_value hEVw)) RLookupV.rvlzero)))) ?_
        exact beta_mstep (eval_value henv) (eval_value henv) (eval_value hEVw) hca hrb
          (eval_value hEVb) hcr
      | gen htl hv hw =>
        simp only [sealTyp] at htl
        cases htl with
        | tlrcd hA' =>
          cases hw with
          | elrec hw' =>
          cases hv with
          | vlrec hv' =>
          have hEVw := EVal.gen hA' hv' hw'
          obtain ⟨a', hca, hEVa'⟩ := eval_cast_ex hEVw
          obtain ⟨b, hrb, hEVb⟩ := ih2 hb (SCE.Value.vmrg henv_val himp_v)
            (EVal.mrg henv hEVa' hd)
          obtain ⟨r, hcr, hEVr⟩ := eval_cast_ex hEVb
          refine ⟨r, ?_, hEVr⟩
          refine mstep_trans (mstep_appl (eval_value henv)
            (mstep_one (Step.sclos (eval_value henv)))) ?_
          refine mstep_trans (mstep_appr (eval_value henv) (Value.vclos (eval_value henv))
            (mstep_trans (mstep_rproj (eval_value henv) hrm)
              (mstep_one (Step.srprojv (eval_value henv) (genVal_value _)
                (genVal_rlookupv RLookup.zero))))) ?_
          exact beta_mstep (eval_value henv) (eval_value henv) (genVal_value _) hca hrb
            (eval_value hEVb) hcr
  | mstruct_sandboxed _ h1 ih =>
    intro Γ A ce ρc helab henv_val henv
    cases helab with
    | emstruct hsb _ hbody =>
      rw [hsb rfl] at hbody
      obtain ⟨w, hrw, hEVw⟩ := ih hbody SCE.Value.vunit EVal.unit
      exact ⟨w, mstep_trans (mstep_boxr (eval_value henv) Value.vunit hrw)
        (mstep_one (Step.sboxv (eval_value henv) Value.vunit (eval_value hEVw))), hEVw⟩
  | mstruct_open _ h1 ih =>
    intro Γ A ce ρc helab henv_val henv
    cases helab with
    | emstruct _ hop hbody =>
      rw [hop rfl] at hbody
      obtain ⟨w, hrw, hEVw⟩ := ih hbody henv_val henv
      exact ⟨w, mstep_trans (mstep_boxl (eval_value henv)
          (mstep_one (Step.squery (eval_value henv))))
        (mstep_trans (mstep_boxr (eval_value henv) (eval_value henv) hrw)
          (mstep_one (Step.sboxv (eval_value henv) (eval_value henv) (eval_value hEVw)))),
        hEVw⟩
  | mfunctor_sandboxed _ =>
    intro Γ A ce ρc helab henv_val henv
    cases helab with
    | emfunctor hsb _ _ hbody =>
      rw [hsb rfl] at hbody
      refine ⟨_, mstep_trans (mstep_boxr (eval_value henv) Value.vunit
          (mstep_one (Step.sclos Value.vunit)))
        (mstep_one (Step.sboxv (eval_value henv) Value.vunit
          (Value.vclos Value.vunit))), ?_⟩
      exact EVal.mclos SCE.Value.vunit EVal.unit hbody disj_top
  | mfunctor_open _ =>
    intro Γ A ce ρc helab henv_val henv
    cases helab with
    | emfunctor _ hop hdop hbody =>
      rw [hop rfl] at hbody
      exact ⟨_, mstep_one (Step.sclos (eval_value henv)),
        EVal.mclos henv_val henv hbody (hdop rfl)⟩
  | mlink _ h1 h2 hsel h3 ih1 ih2 ih3 =>
    intro Γ A ce ρc helab henv_val henv
    cases helab with
    | emlink ha hb hslook hd1 hd2 =>
      obtain ⟨m, hrm, hEVm⟩ := ih1 ha henv_val henv
      obtain ⟨ρ', hcast, hρ'⟩ := eval_env_restrict henv hEVm hd1
      have hρ'v : Value ρ' :=
        cast_value (Value.vmrg (eval_value henv) (eval_value hEVm)) hcast
      obtain ⟨f, hrf, hEVf⟩ := ih2 hb henv_val hρ'
      obtain ⟨m', hrm', hEVm'⟩ := ih1 ha henv_val hρ'
      have hmod_v := eval_produces_value henv_val h1
      have himp_v := S_Sem.sel_value hsel hmod_v
      cases hEVf with
      | mclos hρ₂ hEVenv₂ hbody₂ hd₂' =>
        obtain ⟨wc, hwc, hEVw⟩ := eval_sel hslook hEVm' hsel
        obtain ⟨argc, hcarg, hEVarg⟩ := eval_cast_ex (EVal.rcd hEVw)
        obtain ⟨bc, hrb, hEVb⟩ := ih3 hbody₂
          (SCE.Value.vmrg hρ₂ (SCE.Value.vlrec himp_v)) (EVal.mrg hEVenv₂ hEVarg hd₂')
        obtain ⟨rc, hcr, hEVr⟩ := eval_cast_ex hEVb
        exact ⟨.mrg m rc, mstep_trans (mstep_mrgl (eval_value henv) hrm)
          (mstep_mrgr (eval_value henv) (eval_value hEVm)
            (sealbox_mstep (eval_value henv) (eval_value hEVm) hcast
              (mstep_trans (mstep_appl hρ'v hrf)
                (mstep_trans (mstep_appr hρ'v (Value.vclos (eval_value hEVenv₂))
                  (mstep_trans (mstep_lrec hρ'v (mstep_rproj hρ'v hrm'))
                    (mstep_one (Step.slrec hρ'v
                      (Step.srprojv hρ'v (eval_value hEVm') hwc)))))
                  (beta_mstep hρ'v (eval_value hEVenv₂) (Value.vrcd (eval_value hEVw))
                    hcarg hrb (eval_value hEVb) hcr)))
              (eval_value hEVr))),
          EVal.mrg hEVm hEVr hd2⟩
      | gen htl hv hw =>
        simp only [sealTyp, sealModTyp] at htl
        cases htl with
        | tlarr hB' =>
          cases hw with
          | emclos hval₂ hw₁ hw₂ hdw =>
            obtain ⟨wc, hwc, hEVw⟩ := eval_sel hslook hEVm' hsel
            obtain ⟨argc, hcarg, _⟩ := eval_cast_ex (EVal.rcd hEVw)
            obtain ⟨g', hcg⟩ := cast_progress (genVal_value _) (genVal_typed (Δ := sealStore Δ) hB' .top)
              (sub_refl _)
            have hg' := (toplike_gen_cast hB' hcg).1
            obtain ⟨wa, hwa⟩ := eval_elab (EVal.rcd hEVw)
            obtain ⟨bc', _, hEVb'⟩ := ih3 hw₂
              (SCE.Value.vmrg hval₂ (SCE.Value.vlrec himp_v))
              (EVal.mrg (elab_eval hw₁ hval₂) (elab_eval hwa (SCE.Value.vlrec himp_v)) hdw)
            obtain ⟨wv, hwv⟩ := eval_elab hEVb'
            refine ⟨.mrg m g', mstep_trans (mstep_mrgl (eval_value henv) hrm)
              (mstep_mrgr (eval_value henv) (eval_value hEVm)
                (sealbox_mstep (eval_value henv) (eval_value hEVm) hcast
                  (mstep_trans (mstep_appl hρ'v hrf)
                    (mstep_trans (mstep_appr hρ'v (genVal_value _)
                      (mstep_trans (mstep_lrec hρ'v (mstep_rproj hρ'v hrm'))
                        (mstep_one (Step.slrec hρ'v
                          (Step.srprojv hρ'v (eval_value hEVm') hwc)))))
                      (beta_mstep hρ'v Value.vunit (Value.vrcd (eval_value hEVw))
                        hcarg MStep.refl (genVal_value _) hcg)))
                  (cast_value (genVal_value _) hcg))), ?_⟩
            refine EVal.mrg hEVm ?_ hd2
            rw [hg']
            exact EVal.gen hB'
              (eval_produces_value (SCE.Value.vmrg hval₂ (SCE.Value.vlrec himp_v)) h3) hwv
  | mlinkn _ h1 h2 hsp h3 ih1 ih2 ih3 =>
    intro Γ A ce ρc helab henv_val henv
    cases helab with
    | emlinkn ha hb hwire hd1 hd2 =>
      obtain ⟨m, hrm, hEVm⟩ := ih1 ha henv_val henv
      obtain ⟨ρ', hcast, hρ'⟩ := eval_env_restrict henv hEVm hd1
      have hρ'v : Value ρ' :=
        cast_value (Value.vmrg (eval_value henv) (eval_value hEVm)) hcast
      obtain ⟨f, hrf, hEVf⟩ := ih2 hb henv_val hρ'
      have hmod_v := eval_produces_value henv_val h1
      have hpkg_v := S_Sem.selpkg_value hsp hmod_v
      cases hEVf with
      | mclos hρ₂ hEVenv₂ hbody₂ hd₂' =>
        obtain ⟨pc, hrp, hEVp⟩ := wire_mstep hwire
          (fun hρx => ih1 ha henv_val hρx) hsp hρ'
        obtain ⟨argc, hcarg, hEVarg⟩ := eval_cast_ex hEVp
        obtain ⟨bc, hrb, hEVb⟩ := ih3 hbody₂ (SCE.Value.vmrg hρ₂ hpkg_v)
          (EVal.mrg hEVenv₂ hEVarg hd₂')
        obtain ⟨rc, hcr, hEVr⟩ := eval_cast_ex hEVb
        have hinner :=
          mstep_trans (mstep_appl hρ'v hrf)
            (mstep_trans (mstep_appr hρ'v (Value.vclos (eval_value hEVenv₂)) hrp)
              (beta_mstep hρ'v (eval_value hEVenv₂) (eval_value hEVp) hcarg
                hrb (eval_value hEVb) hcr))
        exact ⟨.mrg m rc, mstep_trans (mstep_mrgl (eval_value henv) hrm)
          (mstep_mrgr (eval_value henv) (eval_value hEVm)
            (sealbox_mstep (eval_value henv) (eval_value hEVm) hcast hinner
              (eval_value hEVr))),
          EVal.mrg hEVm hEVr hd2⟩
      | gen htl hv hw =>
        simp only [sealTyp, sealModTyp] at htl
        cases htl with
        | tlarr hB' =>
          cases hw with
          | emclos hval₂ hw₁ hw₂ hdw =>
            obtain ⟨pc, hrp, hEVp⟩ := wire_mstep hwire
              (fun hρx => ih1 ha henv_val hρx) hsp hρ'
            obtain ⟨argc, hcarg, _⟩ := eval_cast_ex hEVp
            obtain ⟨g', hcg⟩ := cast_progress (genVal_value _) (genVal_typed (Δ := sealStore Δ) hB' .top)
              (sub_refl _)
            have hg' := (toplike_gen_cast hB' hcg).1
            obtain ⟨wa, hwa⟩ := eval_elab hEVp
            obtain ⟨bc', _, hEVb'⟩ := ih3 hw₂ (SCE.Value.vmrg hval₂ hpkg_v)
              (EVal.mrg (elab_eval hw₁ hval₂) (elab_eval hwa hpkg_v) hdw)
            obtain ⟨wv, hwv⟩ := eval_elab hEVb'
            have hinner :=
              mstep_trans (mstep_appl hρ'v hrf)
                (mstep_trans (mstep_appr hρ'v (genVal_value _) hrp)
                  (beta_mstep hρ'v Value.vunit (eval_value hEVp) hcarg
                    MStep.refl (genVal_value _) hcg))
            refine ⟨.mrg m g', mstep_trans (mstep_mrgl (eval_value henv) hrm)
              (mstep_mrgr (eval_value henv) (eval_value hEVm)
                (sealbox_mstep (eval_value henv) (eval_value hEVm) hcast hinner
                  (cast_value (genVal_value _) hcg))), ?_⟩
            refine EVal.mrg hEVm ?_ hd2
            rw [hg']
            exact EVal.gen hB' (eval_produces_value (SCE.Value.vmrg hval₂ hpkg_v) h3) hwv
  | inl _ h ih =>
    intro Γ A ce ρc helab henv_val henv
    cases helab with
    | einl ha =>
      obtain ⟨vc, hrun, hEV⟩ := ih ha henv_val henv
      exact ⟨_, mstep_inl (eval_value henv) hrun, EVal.inl hEV⟩
  | inr _ h ih =>
    intro Γ A ce ρc helab henv_val henv
    cases helab with
    | einr ha =>
      obtain ⟨vc, hrun, hEV⟩ := ih ha henv_val henv
      exact ⟨_, mstep_inr (eval_value henv) hrun, EVal.inr hEV⟩
  | case_inl _ h1 h2 ih1 ih2 =>
    intro Γ A ce ρc helab henv_val henv
    cases helab with
    | ecase ha hb₁ hb₂ hd₁ hd₂ =>
      obtain ⟨sc, hrs, hEVs⟩ := ih1 ha henv_val henv
      cases hEVs with
      | inl hEVp =>
        obtain ⟨bc, hrb, hEVb⟩ := ih2 hb₁
          (SCE.Value.vmrg henv_val (eval_value_src hEVp)) (EVal.mrg henv hEVp hd₁)
        have hvm : Value (.mrg ρc _) := Value.vmrg (eval_value henv) (eval_value hEVp)
        exact ⟨bc,
          mstep_trans (mstep_case (eval_value henv) hrs)
            (MStep.step (Step.scasel (eval_value henv) (eval_value hEVp))
              (mstep_trans (mstep_boxr (eval_value henv) hvm hrb)
                (mstep_one (Step.sboxv (eval_value henv) hvm (eval_value hEVb))))),
          hEVb⟩
      | gen htl _ _ => simp only [sealTyp] at htl; nomatch htl
  | case_inr _ h1 h2 ih1 ih2 =>
    intro Γ A ce ρc helab henv_val henv
    cases helab with
    | ecase ha hb₁ hb₂ hd₁ hd₂ =>
      obtain ⟨sc, hrs, hEVs⟩ := ih1 ha henv_val henv
      cases hEVs with
      | inr hEVp =>
        obtain ⟨bc, hrb, hEVb⟩ := ih2 hb₂
          (SCE.Value.vmrg henv_val (eval_value_src hEVp)) (EVal.mrg henv hEVp hd₂)
        have hvm : Value (.mrg ρc _) := Value.vmrg (eval_value henv) (eval_value hEVp)
        exact ⟨bc,
          mstep_trans (mstep_case (eval_value henv) hrs)
            (MStep.step (Step.scaser (eval_value henv) (eval_value hEVp))
              (mstep_trans (mstep_boxr (eval_value henv) hvm hrb)
                (mstep_one (Step.sboxv (eval_value henv) hvm (eval_value hEVb))))),
          hEVb⟩
      | gen htl _ _ => simp only [sealTyp] at htl; nomatch htl
  | fclos_val _ hval =>
    intro Γ A ce ρc helab henv_val henv
    cases helab with
    | efclos hval' h₁ h₂ hd₁ hd₂ =>
      exact ⟨_, MStep.refl, EVal.fclos hval' (elab_eval h₁ hval') h₂ hd₁ hd₂⟩
  | flam _ =>
    intro Γ A ce ρc helab henv_val henv
    cases helab with
    | eflam hbody hd₁ hd₂ =>
      exact ⟨_, mstep_one (Step.sflam (eval_value henv)),
        EVal.fclos henv_val henv hbody hd₁ hd₂⟩
  | app_fclos _ h1 h2 h3 ih1 ih2 ih3 =>
    intro Γ A ce ρc helab henv_val henv
    cases helab with
    | eapp ha hb =>
      obtain ⟨fc, hrf, hEVf⟩ := ih1 ha henv_val henv
      obtain ⟨ac, hra, hEVa⟩ := ih2 hb henv_val henv
      have harg_v := eval_produces_value henv_val h2
      cases hEVf with
      | fclos hρ₁ hEVenv hbody hd₁ hd₂ =>
        obtain ⟨ac', hca, hEVa'⟩ := eval_cast_ex hEVa
        obtain ⟨bc, hrb, hEVb⟩ := ih3 hbody
          (SCE.Value.vmrg (SCE.Value.vmrg hρ₁ (SCE.Value.vfclos hρ₁)) harg_v)
          (EVal.mrg (EVal.mrg hEVenv (EVal.fclos hρ₁ hEVenv hbody hd₁ hd₂) hd₁) hEVa' hd₂)
        obtain ⟨rc, hcr, hEVr⟩ := eval_cast_ex hEVb
        exact ⟨rc, mstep_trans (mstep_appl (eval_value henv) hrf)
          (mstep_trans
            (mstep_appr (eval_value henv) (Value.vfclos (eval_value hEVenv)) hra)
            (fbeta_mstep (eval_value henv) (eval_value hEVenv) (eval_value hEVa) hca hrb
              (eval_value hEVb) hcr)), hEVr⟩
      | gen htl hv hw =>
        simp only [sealTyp] at htl
        cases htl with
        | tlarr hB' =>
          obtain ⟨ac', hca, _⟩ := eval_cast_ex hEVa
          obtain ⟨g', hcg⟩ := cast_progress (genVal_value _)
            (genVal_typed (Δ := sealStore Δ) hB' .top) (sub_refl _)
          have hg' := (toplike_gen_cast hB' hcg).1
          cases hw with
          | efclos hval₁ hw₁ hw₂ hdw₁ hdw₂ =>
            obtain ⟨wa, hwa⟩ := eval_elab hEVa
            obtain ⟨bc', _, hEVb'⟩ := ih3 hw₂
              (SCE.Value.vmrg (SCE.Value.vmrg hval₁ (SCE.Value.vfclos hval₁)) harg_v)
              (EVal.mrg
                (EVal.mrg (elab_eval hw₁ hval₁)
                  (elab_eval (elabSeal.efclos (ctx := .top) hval₁ hw₁ hw₂ hdw₁ hdw₂)
                    (SCE.Value.vfclos hval₁)) hdw₁)
                (elab_eval hwa harg_v) hdw₂)
            obtain ⟨wv, hwv⟩ := eval_elab hEVb'
            refine ⟨g', mstep_trans (mstep_appl (eval_value henv) hrf)
              (mstep_trans (mstep_appr (eval_value henv) (genVal_value _) hra)
                (beta_mstep (eval_value henv) Value.vunit (eval_value hEVa) hca
                  MStep.refl (genVal_value _) hcg)), ?_⟩
            rw [hg']
            exact EVal.gen hB'
              (eval_produces_value
                (SCE.Value.vmrg (SCE.Value.vmrg hval₁ (SCE.Value.vfclos hval₁)) harg_v) h3)
              hwv
  | fold _ h ih =>
    intro Γ A ce ρc helab henv_val henv
    cases helab with
    | efold ha =>
      obtain ⟨vc, hrun, hEV⟩ := ih ha henv_val henv
      exact ⟨_, mstep_fold (eval_value henv) hrun, EVal.fold hEV⟩
  | unfold _ h ih =>
    intro Γ A ce ρc helab henv_val henv
    cases helab with
    | eunfold ha heq =>
      subst heq
      obtain ⟨vc, hrun, hEV⟩ := ih ha henv_val henv
      cases hEV with
      | fold hEVp =>
        exact ⟨_, mstep_trans (mstep_unfold (eval_value henv) hrun)
          (mstep_one (Step.sunfoldv (eval_value henv) (eval_value hEVp))), hEVp⟩
      | gen htl _ _ => simp only [sealTyp] at htl; nomatch htl
  -- Sealing forms: branded values are values (evaluate to themselves); the coercions
  -- run the operand and then simulate the source coercion by the target one.
  | wrap _ h _ =>
    intro Γ A ce ρc helab _ henv
    cases helab with
    | ewrap hΔ hv hw =>
      rw [bstep_value_id h hv]
      exact ⟨_, MStep.refl, EVal.wrap hΔ (elab_eval hw hv)⟩
  | mseal _ _ hs ih =>
    intro Γ A ce ρc helab henv_val henv
    cases helab with
    | emseal hΔ hnr hwf he =>
      obtain ⟨vc, hrun, hEV⟩ := ih he henv_val henv
      obtain ⟨wc, hs', hEV'⟩ := eval_sealv hs hΔ hnr hwf hEV
      refine ⟨wc, ?_, hEV'⟩
      exact mstep_trans (mstep_seal (eval_value henv) hrun)
        (mstep_one (Step.ssealv (eval_value henv) (eval_value hEV) hs'))
  | munseal _ _ hs ih =>
    intro Γ A ce ρc helab henv_val henv
    cases helab with
    | emunseal hΔ hnr hwf he heq =>
      subst heq
      obtain ⟨vc, hrun, hEV⟩ := ih he henv_val henv
      obtain ⟨wc, hs', hEV'⟩ := eval_unsealv hs hΔ hnr hwf hEV
      refine ⟨wc, ?_, hEV'⟩
      exact mstep_trans (mstep_unseal (eval_value henv) hrun)
        (mstep_one (Step.sunsealv (eval_value henv) (eval_value hEV) hs'))

-- ── Corollaries ──────────────────────────────────────────────────────────────────────

-- Whole-program correctness for closed programs.
theorem seal_whole_program_correctness {es vs : SCE.Exp} {A : SCE.Typ} {ce : Seal.Exp}
    (helab : elabSeal Δ .top es A ce) (heval : S_Sem.BStep .unit es vs)
    : ∃ vc, MStep .unit ce vc ∧ EVal Δ A vs vc :=
  seal_semantic_preservation heval helab SCE.Value.vunit EVal.unit

-- Separate compilation, single-import link: elaborate the module and the functor
-- separately; if the source link evaluates, the composed λE^≤ term (a merge of sealed
-- boxes — no bind-once combinator) evaluates to a related value.
theorem seal_separate_compilation
    {Γ Γ₁ A B : SCE.Typ} {l : String} {es₁ es₂ : SCE.Exp} {ce₁ ce₂ : Seal.Exp}
    {ρs vs : SCE.Exp} {ρc : Seal.Exp}
    (helab₁ : elabSeal Δ Γ es₁ Γ₁ ce₁)
    (helab₂ : elabSeal Δ Γ es₂ (.sig (.TyArrM (.rcd l A) (.TyIntf B))) ce₂)
    (hlookup : SCE.SRLookup Γ₁ l A)
    (hd₁ : Seal.Disj (sealTyp Γ₁) (sealTyp Γ))
    (hd₂ : Seal.Disj (sealTyp Γ₁) (sealTyp B))
    (heval : S_Sem.BStep ρs (.mlink es₁ es₂) vs)
    (henv_val : SCE.Value ρs) (henv : EVal Δ Γ ρs ρc)
    : ∃ vc, MStep ρc
        (.mrg ce₁ (.box (.anno .query (sealTyp Γ))
          (.app ce₂ (.lrec l (.rproj ce₁ l))))) vc
      ∧ EVal Δ (.and Γ₁ B) vs vc :=
  seal_semantic_preservation heval
    (elabSeal.emlink helab₁ helab₂ hlookup hd₁ hd₂) henv_val henv

theorem seal_separate_compilation_closed
    {Γ₁ A B : SCE.Typ} {l : String} {es₁ es₂ : SCE.Exp} {ce₁ ce₂ : Seal.Exp}
    {vs : SCE.Exp}
    (helab₁ : elabSeal Δ .top es₁ Γ₁ ce₁)
    (helab₂ : elabSeal Δ .top es₂ (.sig (.TyArrM (.rcd l A) (.TyIntf B))) ce₂)
    (hlookup : SCE.SRLookup Γ₁ l A)
    (hd₂ : Seal.Disj (sealTyp Γ₁) (sealTyp B))
    (heval : S_Sem.BStep .unit (.mlink es₁ es₂) vs)
    : ∃ vc, MStep .unit
        (.mrg ce₁ (.box (.anno .query .top) (.app ce₂ (.lrec l (.rproj ce₁ l))))) vc
      ∧ EVal Δ (.and Γ₁ B) vs vc :=
  seal_separate_compilation helab₁ helab₂ hlookup disj_top_r hd₂ heval
    SCE.Value.vunit EVal.unit

-- Separate compilation, n-ary link.
theorem seal_separate_compilation_n
    {Γ Γ₁ D B : SCE.Typ} {es₁ es₂ : SCE.Exp} {ce₁ ce₂ : Seal.Exp}
    {ρs vs : SCE.Exp} {ρc : Seal.Exp}
    (helab₁ : elabSeal Δ Γ es₁ Γ₁ ce₁)
    (helab₂ : elabSeal Δ Γ es₂ (.sig (.TyArrM D (.TyIntf B))) ce₂)
    (hwire : WireOk (sealTyp Γ) Γ₁ D)
    (hd₁ : Seal.Disj (sealTyp Γ₁) (sealTyp Γ))
    (hd₂ : Seal.Disj (sealTyp Γ₁) (sealTyp B))
    (heval : S_Sem.BStep ρs (.mlinkn es₁ es₂) vs)
    (henv_val : SCE.Value ρs) (henv : EVal Δ Γ ρs ρc)
    : ∃ vc, MStep ρc
        (.mrg ce₁ (.box (.anno .query (sealTyp Γ))
          (.app ce₂ (wireArgSeal (sealTyp Γ) ce₁ D)))) vc
      ∧ EVal Δ (.and Γ₁ B) vs vc :=
  seal_semantic_preservation heval
    (elabSeal.emlinkn helab₁ helab₂ hwire hd₁ hd₂) henv_val henv

theorem seal_separate_compilation_n_closed
    {Γ₁ D B : SCE.Typ} {es₁ es₂ : SCE.Exp} {ce₁ ce₂ : Seal.Exp} {vs : SCE.Exp}
    (helab₁ : elabSeal Δ .top es₁ Γ₁ ce₁)
    (helab₂ : elabSeal Δ .top es₂ (.sig (.TyArrM D (.TyIntf B))) ce₂)
    (hwire : WireOk .top Γ₁ D)
    (hd₂ : Seal.Disj (sealTyp Γ₁) (sealTyp B))
    (heval : S_Sem.BStep .unit (.mlinkn es₁ es₂) vs)
    : ∃ vc, MStep .unit
        (.mrg ce₁ (.box (.anno .query .top) (.app ce₂ (wireArgSeal .top ce₁ D)))) vc
      ∧ EVal Δ (.and Γ₁ B) vs vc :=
  seal_separate_compilation_n helab₁ helab₂ hwire disj_top_r hd₂ heval
    SCE.Value.vunit EVal.unit

-- Evaluation of elaborated programs is deterministic on the λE^≤ side: two terminating
-- runs of a well-typed term agree (the analogue of SCE's bigstep_deterministic, via
-- gdeterminism + gpreservation).
theorem mstep_value_determinism {Δ' : Seal.BrandStore} {venv e v₁ : Seal.Exp}
    (h₁ : MStep venv e v₁)
    : ∀ {Γ A : Seal.Typ}, Seal.HasType Δ' Γ e A → Seal.HasType Δ' .top venv Γ → Value v₁
    → ∀ {v₂ : Seal.Exp}, MStep venv e v₂ → Value v₂ → v₁ = v₂ := by
  induction h₁ with
  | refl =>
    intro Γ A ht henv hv₁ v₂ h₂ hv₂
    exact mstep_value_eq hv₁ h₂
  | step hs h' ih =>
    intro Γ A ht henv hv₁ v₂ h₂ hv₂
    cases h₂ with
    | refl => exact (value_not_step hv₂ hs).elim
    | step hs₂ h₂' =>
      have heq := gdeterminism hs ht henv hs₂
      rw [← heq] at h₂'
      exact ih (gpreservation hs ht henv) henv hv₁ h₂' hv₂

-- ── Sealed compilation units ─────────────────────────────────────────────────────────

-- Sealed separate compilation: the provider unit is a *sealed* module `mseal n R Γ₁ es₁`
-- (implementation es₁ at the representation view Γ₁[n:=R] of its interface Γ₁), the
-- client a functor over the abstract interface, compiled in a store Δc that need not
-- know the representation (`StoreLe Δc Δ`).  Both are elaborated separately; the target
-- links the sealed provider exactly as `seal_separate_compilation` links a plain one.
theorem seal_separate_compilation_sealed {Δc : SCE.BrandStore}
    {Γ Γ₁ R A B : SCE.Typ} {n : Nat} {l : String} {es₁ es₂ : SCE.Exp} {ce₁ ce₂ : Seal.Exp}
    {ρs vs : SCE.Exp} {ρc : Seal.Exp}
    (hΔ : Δ n = some R) (hnr : NoRes (sealTyp R)) (hwf : WfSig n (sealTyp R) (sealTyp Γ₁))
    (helab₁ : elabSeal Δ Γ es₁ (SCE.substBrand n R Γ₁) ce₁)
    (hle : SCE.StoreLe Δc Δ)
    (helab₂ : elabSeal Δc Γ es₂ (.sig (.TyArrM (.rcd l A) (.TyIntf B))) ce₂)
    (hlookup : SCE.SRLookup Γ₁ l A)
    (hd₁ : Seal.Disj (sealTyp Γ₁) (sealTyp Γ))
    (hd₂ : Seal.Disj (sealTyp Γ₁) (sealTyp B))
    (heval : S_Sem.BStep ρs (.mlink (.mseal n R Γ₁ es₁) es₂) vs)
    (henv_val : SCE.Value ρs) (henv : EVal Δ Γ ρs ρc)
    : ∃ vc, MStep ρc
        (.mrg (.seal n (sealTyp R) (sealTyp Γ₁) ce₁)
          (.box (.anno .query (sealTyp Γ))
            (.app ce₂ (.lrec l (.rproj (.seal n (sealTyp R) (sealTyp Γ₁) ce₁) l))))) vc
      ∧ EVal Δ (.and Γ₁ B) vs vc :=
  seal_semantic_preservation heval
    (elabSeal.emlink (elabSeal.emseal hΔ hnr hwf helab₁)
      (elabSeal_weaken_store hle helab₂) hlookup hd₁ hd₂) henv_val henv

-- Related values at Int are the same literal on both sides.
theorem eval_int {vs : SCE.Exp} {vc : Seal.Exp} (h : EVal Δ .int vs vc)
    : ∃ i, vs = .lit i ∧ vc = .lit i := by
  cases h with
  | lit => exact ⟨_, rfl, rfl⟩
  | gen htl _ _ => nomatch htl

-- ── Elaborated code is in the normalizing fragment ───────────────────────────────────
-- The elaboration has no rules for the source fixpoint forms (flam/fclos), so every term
-- it emits is Finitary.  This discharges the fragment hypothesis of the relational layer
-- for clients that come from elaboration.  [When elabSeal grows fixpoint rules, this
-- lemma becomes conditional on a source-side fragment predicate.]

theorem wireArgSeal_finitary {ctx : Seal.Typ} {ce₁ : Seal.Exp} (hce : Finitary ce₁)
    : (D : SCE.Typ) → Finitary (wireArgSeal ctx ce₁ D)
  | .int => Finitary.unit
  | .top => Finitary.unit
  | .arr _ _ => Finitary.unit
  | .rcd _ _ => Finitary.lrec (Finitary.rproj hce)
  | .sig _ => Finitary.unit
  | .var _ => Finitary.unit
  | .mu _ => Finitary.unit
  | .brand _ => Finitary.unit
  | .or _ _ => Finitary.unit
  | .and D₁ D₂ => by
    cases D₂ with
    | rcd l A =>
      exact Finitary.mrg (wireArgSeal_finitary hce D₁)
        (Finitary.box (Finitary.anno Finitary.query) (Finitary.lrec (Finitary.rproj hce)))
    | int => exact Finitary.unit
    | top => exact Finitary.unit
    | arr _ _ => exact Finitary.unit
    | and _ _ => exact Finitary.unit
    | or _ _ => exact Finitary.unit
    | sig _ => exact Finitary.unit
    | var _ => exact Finitary.unit
    | mu _ => exact Finitary.unit
    | brand _ => exact Finitary.unit

theorem elabSeal_finitary {Γ : SCE.Typ} {e : SCE.Exp} {A : SCE.Typ} {ce : Seal.Exp}
    (h : elabSeal Δ Γ e A ce) (hsf : SCE.SFinitary e) : Finitary ce := by
  induction h with
  | equery => exact Finitary.query
  | elit _ _ => exact Finitary.lit
  | eunit _ => exact Finitary.unit
  | eapp _ _ ih₁ ih₂ => exact Finitary.app (ih₁ hsf.1) (ih₂ hsf.2)
  | eproj _ _ ih => exact Finitary.proj (ih hsf)
  | ebox _ _ ih₁ ih₂ => exact Finitary.box (ih₁ hsf.1) (ih₂ hsf.2)
  | edmrg _ _ _ _ ih₁ ih₂ => exact Finitary.mrg (ih₁ hsf.1) (ih₂ hsf.2)
  | evmrg _ _ _ _ _ ih₁ ih₂ => exact Finitary.mrg (ih₁ hsf.1) (ih₂ hsf.2)
  | enmrg _ _ _ _ ih₁ ih₂ =>
    exact Finitary.mrg (ih₁ hsf.1) (Finitary.box (Finitary.anno Finitary.query) (ih₂ hsf.2))
  | elam _ _ ih => exact Finitary.lam (ih hsf)
  | erproj _ _ ih => exact Finitary.rproj (ih hsf)
  | eclos _ _ _ _ ih₁ ih₂ => exact Finitary.clos (ih₁ hsf.1) (ih₂ hsf.2)
  | elrec _ ih => exact Finitary.lrec (ih hsf)
  | eletb _ _ _ ih₁ ih₂ => exact Finitary.app (Finitary.lam (ih₂ hsf.2)) (ih₁ hsf.1)
  | eopenm _ _ _ ih₁ ih₂ =>
    exact Finitary.app (Finitary.lam (ih₂ hsf.2)) (Finitary.rproj (ih₁ hsf.1))
  | @emstruct _ _ _ sb _ _ _ _ _ ih =>
    cases sb with
    | sandboxed => exact Finitary.box Finitary.unit (ih hsf)
    | open_ => exact Finitary.box Finitary.query (ih hsf)
  | @emfunctor _ _ _ _ sb _ _ _ _ _ _ ih =>
    cases sb with
    | sandboxed => exact Finitary.box Finitary.unit (Finitary.lam (ih hsf))
    | open_ => exact Finitary.lam (ih hsf)
  | emclos _ _ _ _ ih₁ ih₂ => exact Finitary.clos (ih₁ hsf.1) (ih₂ hsf.2)
  | emapp _ _ ih₁ ih₂ => exact Finitary.app (ih₁ hsf.1) (ih₂ hsf.2)
  | emlink _ _ _ _ _ ih₁ ih₂ =>
    exact Finitary.mrg (ih₁ hsf.1) (Finitary.box (Finitary.anno Finitary.query)
      (Finitary.app (ih₂ hsf.2) (Finitary.lrec (Finitary.rproj (ih₁ hsf.1)))))
  | emlinkn _ _ _ _ _ ih₁ ih₂ =>
    exact Finitary.mrg (ih₁ hsf.1) (Finitary.box (Finitary.anno Finitary.query)
      (Finitary.app (ih₂ hsf.2) (wireArgSeal_finitary (ih₁ hsf.1) _)))
  | ewrap _ _ _ ih => exact Finitary.wrap (ih hsf)
  | emseal _ _ _ _ ih => exact Finitary.seal (ih hsf)
  | emunseal _ _ _ _ _ ih => exact Finitary.unseal (ih hsf)
  | einl _ ih => exact Finitary.inl (ih hsf)
  | einr _ ih => exact Finitary.inr (ih hsf)
  | ecase _ _ _ _ _ ih ih₁ ih₂ =>
    exact Finitary.case (ih hsf.1) (ih₁ hsf.2.1) (ih₂ hsf.2.2)
  | eflam _ _ _ _ => exact hsf.elim
  | efclos _ _ _ _ _ _ _ => exact hsf.elim
  | efold _ _ => exact hsf.elim
  | eunfold _ _ _ => exact hsf.elim

-- Source-level representation independence.  Two source providers p₁, p₂ of a signature
-- S with abstract type α_n, over representations R₁, R₂, whose elaborations are related
-- as implementations (LRg at the open brand, cf. Abstraction.lean); a source client c
-- typed against S with every brand opaque (store noBrands), observing at Int.  Then the
-- two sealed source programs `box (mseal n Rᵢ S pᵢ) c` compute the same literal — by
-- semantic preservation, target-level representation independence, and determinism.
theorem source_representation_independence
    {Δ₁ Δ₂ : SCE.BrandStore} {η : Nat → Exp → Exp → Prop} {n : Nat} {R₁ R₂ : SCE.Typ}
    (hb : OpenBrand (sealStore Δ₁) (sealStore Δ₂) η n (sealTyp R₁) (sealTyp R₂))
    (hΔ₁ : Δ₁ n = some R₁) (hΔ₂ : Δ₂ n = some R₂)
    {S : SCE.Typ} (hwf₁ : WfSig n (sealTyp R₁) (sealTyp S)) (hwf₂ : WfSig n (sealTyp R₂) (sealTyp S))
    {p₁ p₂ : SCE.Exp} {pc₁ pc₂ : Seal.Exp}
    (hp₁ : elabSeal Δ₁ .top p₁ (SCE.substBrand n R₁ S) pc₁)
    (hp₂ : elabSeal Δ₂ .top p₂ (SCE.substBrand n R₂ S) pc₂)
    (hrel : LRg (sealStore Δ₁) (sealStore Δ₂) η (some (n, sealTyp R₁, sealTyp R₂))
      (sealTyp S) pc₁ pc₂)
    {c : SCE.Exp} {cc : Seal.Exp} (hc : elabSeal SCE.noBrands S c .int cc)
    (hsf : SCE.SFinitary c)
    {v₁ v₂ : SCE.Exp}
    (hev₁ : S_Sem.BStep .unit (.box (.mseal n R₁ S p₁) c) v₁)
    (hev₂ : S_Sem.BStep .unit (.box (.mseal n R₂ S p₂) c) v₂)
    : ∃ i, v₁ = .lit i ∧ v₂ = .lit i := by
  -- the client types with every brand opaque
  have hcl : HasType noBrands (sealTyp S) cc .int := seal_type_preservation hc
  obtain ⟨i, r₁, r₂⟩ :=
    representation_independence hb hwf₁ hwf₂ hrel hcl (elabSeal_finitary hc hsf)
  -- the two sealed programs elaborate and are simulated
  have helab₁ : elabSeal Δ₁ .top (.box (.mseal n R₁ S p₁) c) .int
      (.box (.seal n (sealTyp R₁) (sealTyp S) pc₁) cc) :=
    elabSeal.ebox (elabSeal.emseal hΔ₁ hb.nores₁ hwf₁ hp₁)
      (elabSeal_weaken_store (SCE.storele_noBrands Δ₁) hc)
  have helab₂ : elabSeal Δ₂ .top (.box (.mseal n R₂ S p₂) c) .int
      (.box (.seal n (sealTyp R₂) (sealTyp S) pc₂) cc) :=
    elabSeal.ebox (elabSeal.emseal hΔ₂ hb.nores₂ hwf₂ hp₂)
      (elabSeal_weaken_store (SCE.storele_noBrands Δ₂) hc)
  obtain ⟨vc₁, run₁, hEV₁⟩ :=
    seal_semantic_preservation hev₁ helab₁ SCE.Value.vunit EVal.unit
  obtain ⟨vc₂, run₂, hEV₂⟩ :=
    seal_semantic_preservation hev₂ helab₂ SCE.Value.vunit EVal.unit
  -- determinism pins the simulated results to the RI literal
  have heq₁ : vc₁ = .lit i :=
    mstep_value_determinism run₁ (seal_type_preservation helab₁) HasType.tunit
      (eval_value hEV₁) r₁ Value.vint
  have heq₂ : vc₂ = .lit i :=
    mstep_value_determinism run₂ (seal_type_preservation helab₂) HasType.tunit
      (eval_value hEV₂) r₂ Value.vint
  obtain ⟨i₁, hv₁, hc₁⟩ := eval_int hEV₁
  obtain ⟨i₂, hv₂, hc₂⟩ := eval_int hEV₂
  rw [heq₁] at hc₁
  rw [heq₂] at hc₂
  cases hc₁
  cases hc₂
  exact ⟨i, hv₁, hv₂⟩

end Seal
