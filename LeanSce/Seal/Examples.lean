import LeanSce.Seal.Sealing
import LeanSce.Seal.Elaboration
import LeanSce.Seal.Abstraction
import LeanSce.Seal.Correctness

-- Smoke tests: sealing is not inert — the cast actually discards components, beta
-- actually casts the argument and reseals the result, and providers that differ outside
-- the seal agree exactly after sealing.
namespace Seal

variable {Δ : BrandStore}

-- Sealing discards: {x = 1} # {y = 2} sealed at {x : Int} is exactly {x = 1}.
example : Cast (.mrg (.lrec "x" (.lit 1)) (.lrec "y" (.lit 2))) (.rcd "x" .int)
    (.lrec "x" (.lit 1)) :=
  Cast.cmrgl Ordinary.orcd (Cast.crcd Cast.cint)

-- ... and the seal fires in the operational semantics (contrast λE, where annotations
-- do not even exist as expressions).
example : Step .unit
    (.anno (.mrg (.lrec "x" (.lit 1)) (.lrec "y" (.lit 2))) (.rcd "x" .int))
    (.lrec "x" (.lit 1)) :=
  Step.sannov Value.vunit (Value.vmrg (Value.vrcd Value.vint) (Value.vrcd Value.vint))
    (Cast.cmrgl Ordinary.orcd (Cast.crcd Cast.cint))

-- The typing side of the same seal: the merge has the full inferred type
-- {x : Int} & {y : Int}; the annotation compiles the client against {x : Int} only.
example : HasType Δ .top
    (.anno (.mrg (.lrec "x" (.lit 1)) (.lrec "y" (.lit 2))) (.rcd "x" .int))
    (.rcd "x" .int) :=
  HasType.tanno
    (HasType.tmrg (HasType.trcd HasType.tint) (HasType.trcd HasType.tint)
      disj_top_r (disj_rcd_ne (by decide)))
    (Sub.sandl (sub_refl _))

-- Beta casts the argument at the annotation input and reseals the result at the
-- annotation codomain (the two casting premises new in λE^≤'s Step-beta).
example : Step .unit
    (.app (.clos .unit .int .int (.proj .query 0)) (.lit 7))
    (.box (.mrg .unit (.lit 7)) (.anno (.proj .query 0) .int)) :=
  Step.sbeta Value.vunit Value.vunit Value.vint Cast.cint

-- Two providers that differ outside the seal — {x = 1} # {y = 2} vs {x = 1} # {z = 3} —
-- both seal to {x = 1}, hence are related at the seal, hence (by `sealing`)
-- indistinguishable to any client typed against {x : Int}.
example : LR noBrands noBrands (fun _ _ _ => False) (.rcd "x" .int)
    (.lrec "x" (.lit 1)) (.lrec "x" (.lit 1)) :=
  ⟨_, _, rfl, rfl, 1, rfl, rfl⟩

-- A client of the seal: select x from the sealed environment.
example : HasType Δ (.rcd "x" .int) (.rproj .query "x") .int :=
  HasType.trproj HasType.tquery RLookup.zero

-- SCE's non-capturing merge elaborates into λE^≤ via sealing — the (? : Γ) restriction
-- replaces Core's λ-self-application combinator (which λE^≤'s Disj Γ Γ premise forbids).
example : elabSeal SCE.noBrands .top (.nmrg (.lrec "x" (.lit 1)) (.lrec "y" (.lit 2)))
    (.and (.rcd "x" .int) (.rcd "y" .int))
    (.mrg (.lrec "x" (.lit 1))
      (.box (.anno .query .top) (.lrec "y" (.lit 2)))) :=
  elabSeal.enmrg (elabSeal.elrec (elabSeal.elit .top 1))
    (elabSeal.elrec (elabSeal.elit .top 2))
    disj_top_r (disj_rcd_ne (by decide))

-- ... and the elaborated code is well-typed λE^≤ by the preservation theorem (in the
-- brand-free store — this unit seals nothing).
example : Seal.HasType noBrands .top
    (.mrg (.lrec "x" (.lit 1)) (.box (.anno .query .top) (.lrec "y" (.lit 2))))
    (.and (.rcd "x" .int) (.rcd "y" .int)) :=
  sealStore_noBrands ▸ seal_type_preservation
    (elabSeal.enmrg (Δ := SCE.noBrands) (elabSeal.elrec (elabSeal.elit .top 1))
      (elabSeal.elrec (elabSeal.elit .top 2))
      disj_top_r (disj_rcd_ne (by decide)))


-- ── Representation independence, concretely ──────────────────────────────────────────
-- Signature  S = {mk : Int → α} & {get : α → Int}  with abstract α = brand 0.
-- Implementation 1 represents α as Int (mk = get = identity);
-- implementation 2 represents α as {v : Int} (mk boxes, get unboxes).
-- Related through η 0 i {v = i}; the theorem says no client typed against S can tell the
-- sealed units apart.

section RIExample

def α : Typ := .brand 0
def SigMk : Typ := .rcd "mk" (.arr .int α)
def SigGet : Typ := .rcd "get" (.arr α .int)
def Sig : Typ := .and SigMk SigGet

def R₂ : Typ := .rcd "v" .int

def idClos : Exp := .clos .unit .int .int (.proj .query 0)
def boxClos : Exp := .clos .unit .int R₂ (.lrec "v" (.proj .query 0))
def unboxClos : Exp := .clos .unit R₂ .int (.rproj (.proj .query 0) "v")

def impl₁ : Exp := .mrg (.lrec "mk" idClos) (.lrec "get" idClos)
def impl₂ : Exp := .mrg (.lrec "mk" boxClos) (.lrec "get" unboxClos)

def store₁ : BrandStore := fun n => if n = 0 then some .int else none
def store₂ : BrandStore := fun n => if n = 0 then some R₂ else none

def ηex : Nat → Exp → Exp → Prop := fun _ w₁ w₂ => ∃ i, w₁ = .lit i ∧ w₂ = .lrec "v" (.lit i)

theorem lin_rcd_ne {l l' : String} (hne : l ≠ l') {A : Typ} : ¬ Lin l (.rcd l' A) := by
  intro h; cases h; exact hne rfl

theorem openbrand_ex : OpenBrand store₁ store₂ ηex 0 .int R₂ where
  st₁ := rfl
  st₂ := rfl
  nores₁ := NoRes.int
  nores₂ := NoRes.rcd (by decide) NoRes.int
  nobvar₁ := fun h => nomatch h
  nobvar₂ := fun h => by cases h with | rcd h' => nomatch h'
  ntl₁ := fun h => nomatch h
  ntl₂ := fun h => by cases h with | tlrcd h' => nomatch h'
  cast_closed := by
    intro w₁ w₂ ⟨i, e₁, e₂⟩ w₁' w₂' c₁ c₂
    subst e₁; subst e₂
    cases c₁ with
    | cint =>
      cases c₂ with
      | crcd c => cases c with | cint => exact ⟨i, rfl, rfl⟩

theorem wfsig_ex₁ : WfSig 0 .int Sig :=
  WfSig.and (WfSig.rcd (by decide) (WfSig.arr WfSig.int WfSig.brand))
    (WfSig.rcd (by decide) (WfSig.arr WfSig.brand WfSig.int))
    (disj_rcd_ne (by decide)) (disj_rcd_ne (by decide))

theorem wfsig_ex₂ : WfSig 0 R₂ Sig :=
  WfSig.and (WfSig.rcd (by decide) (WfSig.arr WfSig.int WfSig.brand))
    (WfSig.rcd (by decide) (WfSig.arr WfSig.brand WfSig.int))
    (disj_rcd_ne (by decide)) (disj_rcd_ne (by decide))

-- The identity closure applied to a literal returns the literal.
theorem idClos_run {ρ : Exp} (hρ : Value ρ) (i : Nat)
    : MStep ρ (.app idClos (.lit i)) (.lit i) := by
  have henv : Value (.mrg .unit (.lit i)) := Value.vmrg Value.vunit Value.vint
  refine MStep.step (Step.sbeta hρ Value.vunit Value.vint Cast.cint) ?_
  refine MStep.step (Step.sboxr hρ henv (Step.sanno henv (Step.sproj henv (Step.squery henv)))) ?_
  refine MStep.step (Step.sboxr hρ henv (Step.sanno henv (Step.sprojv henv henv LookupV.lvzero))) ?_
  refine MStep.step (Step.sboxr hρ henv (Step.sannov henv Value.vint Cast.cint)) ?_
  exact mstep_one (Step.sboxv hρ henv Value.vint)

theorem boxClos_run {ρ : Exp} (hρ : Value ρ) (i : Nat)
    : MStep ρ (.app boxClos (.lit i)) (.lrec "v" (.lit i)) := by
  have henv : Value (.mrg .unit (.lit i)) := Value.vmrg Value.vunit Value.vint
  refine MStep.step (Step.sbeta hρ Value.vunit Value.vint Cast.cint) ?_
  refine MStep.step (Step.sboxr hρ henv (Step.sanno henv (Step.slrec henv
    (Step.sproj henv (Step.squery henv))))) ?_
  refine MStep.step (Step.sboxr hρ henv (Step.sanno henv (Step.slrec henv
    (Step.sprojv henv henv LookupV.lvzero)))) ?_
  refine MStep.step (Step.sboxr hρ henv (Step.sannov henv (Value.vrcd Value.vint)
    (Cast.crcd Cast.cint))) ?_
  exact mstep_one (Step.sboxv hρ henv (Value.vrcd Value.vint))

theorem unboxClos_run {ρ : Exp} (hρ : Value ρ) (i : Nat)
    : MStep ρ (.app unboxClos (.lrec "v" (.lit i))) (.lit i) := by
  have hv : Value (.lrec "v" (.lit i)) := Value.vrcd Value.vint
  have henv : Value (.mrg .unit (.lrec "v" (.lit i))) := Value.vmrg Value.vunit hv
  refine MStep.step (Step.sbeta hρ Value.vunit hv (Cast.crcd Cast.cint)) ?_
  refine MStep.step (Step.sboxr hρ henv (Step.sanno henv (Step.srproj henv
    (Step.sproj henv (Step.squery henv))))) ?_
  refine MStep.step (Step.sboxr hρ henv (Step.sanno henv (Step.srproj henv
    (Step.sprojv henv henv LookupV.lvzero)))) ?_
  refine MStep.step (Step.sboxr hρ henv (Step.sanno henv
    (Step.srprojv henv hv RLookupV.rvlzero))) ?_
  refine MStep.step (Step.sboxr hρ henv (Step.sannov henv Value.vint Cast.cint)) ?_
  exact mstep_one (Step.sboxv hρ henv Value.vint)

theorem idClos_typed {Δ : BrandStore} : HasType Δ .top idClos (.arr .int .int) :=
  HasType.tclos Value.vunit HasType.tunit disj_top
    (HasType.tproj HasType.tquery Lookup.zero) (sub_refl _) (sub_refl _)

theorem boxClos_typed {Δ : BrandStore} : HasType Δ .top boxClos (.arr .int R₂) :=
  HasType.tclos Value.vunit HasType.tunit disj_top
    (HasType.trcd (HasType.tproj HasType.tquery Lookup.zero)) (sub_refl _) (sub_refl _)

theorem unboxClos_typed {Δ : BrandStore} : HasType Δ .top unboxClos (.arr R₂ .int) :=
  HasType.tclos Value.vunit HasType.tunit disj_top
    (HasType.trproj (HasType.tproj HasType.tquery Lookup.zero) RLookup.zero)
    (sub_refl _) (sub_refl _)

-- The two implementations are related through η at the abstract type (in any pair of
-- stores: the relation at an open brand only consults η).
theorem impl_related {Δ₁ Δ₂ : BrandStore}
    : LRg Δ₁ Δ₂ ηex (some (0, .int, R₂)) Sig impl₁ impl₂ := by
  refine ⟨?_, ?_, _, _, _, _, rfl, rfl, ?_, ?_⟩
  · -- typing of impl₁ at Sig[α := Int]
    exact HasType.tmrg (HasType.trcd idClos_typed)
      (HasType.trcd (value_weaken idClos_typed (Value.vclos Value.vunit)))
      disj_top_r (disj_rcd_ne (by decide))
  · exact HasType.tmrg (HasType.trcd boxClos_typed)
      (HasType.trcd (value_weaken unboxClos_typed (Value.vclos Value.vunit)))
      disj_top_r (disj_rcd_ne (by decide))
  · -- mk : Int → α
    refine ⟨_, _, rfl, rfl, Value.vclos Value.vunit, Value.vclos Value.vunit,
      idClos_typed, boxClos_typed, ?_⟩
    intro u₁ u₂ hu ρ₁ ρ₂ hρ₁ hρ₂
    obtain ⟨i, e₁, e₂⟩ := hu
    subst e₁; subst e₂
    refine ⟨_, _, idClos_run hρ₁ i, boxClos_run hρ₂ i, ?_⟩
    simp only [LRg, α, if_true]
    exact ⟨Value.vint, Value.vrcd Value.vint, HasType.tint, HasType.trcd HasType.tint, i, rfl, rfl⟩
  · -- get : α → Int
    refine ⟨_, _, rfl, rfl, Value.vclos Value.vunit, Value.vclos Value.vunit,
      idClos_typed, unboxClos_typed, ?_⟩
    intro u₁ u₂ hu ρ₁ ρ₂ hρ₁ hρ₂
    simp only [LRg, α, if_true] at hu
    obtain ⟨_, _, _, _, i, e₁, e₂⟩ := hu
    subst e₁; subst e₂
    exact ⟨_, _, idClos_run hρ₁ i, unboxClos_run hρ₂ i, i, rfl, rfl⟩

-- A client of the seal: get (mk 5).  Typed with α opaque (noBrands).
def client : Exp := .app (.rproj .query "get") (.app (.rproj .query "mk") (.lit 5))

theorem client_typed : HasType noBrands Sig client .int :=
  HasType.tapp
    (HasType.trproj HasType.tquery (RLookup.landr RLookup.zero (lin_rcd_ne (by decide))))
    (HasType.tapp
      (HasType.trproj HasType.tquery (RLookup.landl RLookup.zero (lin_rcd_ne (by decide))))
      HasType.tint)

theorem client_finitary : Finitary client :=
  Finitary.app (Finitary.rproj Finitary.query)
    (Finitary.app (Finitary.rproj Finitary.query) Finitary.lit)

-- Representation independence, instantiated: both sealed units give the client the same
-- answer.
example : ∃ i, MStep .unit (.box (.seal 0 .int Sig impl₁) client) (.lit i)
             ∧ MStep .unit (.box (.seal 0 R₂ Sig impl₂) client) (.lit i) :=
  representation_independence openbrand_ex wfsig_ex₁ wfsig_ex₂ impl_related client_typed
    client_finitary

-- ── The same example at the source level ────────────────────────────────────────────
-- The providers and the client are SCE programs; the source sealing form `mseal`
-- elaborates to λE^≤'s `seal`, and `source_representation_independence` (semantic
-- preservation + target RI + determinism) shows the two sealed *source* programs agree.

def sα : SCE.Typ := .brand 0
def sSig : SCE.Typ := .and (.rcd "mk" (.arr .int sα)) (.rcd "get" (.arr sα .int))
def sR₂ : SCE.Typ := .rcd "v" .int

def sIdClos : SCE.Exp := .clos .unit .int (.proj .query 0)
def sBoxClos : SCE.Exp := .clos .unit .int (.lrec "v" (.proj .query 0))
def sUnboxClos : SCE.Exp := .clos .unit sR₂ (.rproj (.proj .query 0) "v")

def sImpl₁ : SCE.Exp := .mrg (.lrec "mk" sIdClos) (.lrec "get" sIdClos)
def sImpl₂ : SCE.Exp := .mrg (.lrec "mk" sBoxClos) (.lrec "get" sUnboxClos)

-- Source stores; their sealTyp images are the target stores above.
def sstore₁ : SCE.BrandStore := fun n => if n = 0 then some .int else none
def sstore₂ : SCE.BrandStore := fun n => if n = 0 then some sR₂ else none

def sClient : SCE.Exp := .app (.rproj .query "get") (.app (.rproj .query "mk") (.lit 5))

theorem labelin_rcd_ne {l l' : String} (hne : l ≠ l') {T : SCE.Typ}
    : ¬ SCE.LabelIn l (.rcd l' T) := by
  intro h; cases h; exact hne rfl

-- Elaborations: each provider at the representation view of sSig, the client against
-- sSig with every brand opaque.
theorem sImpl₁_elab : elabSeal sstore₁ .top sImpl₁ (SCE.substBrand 0 .int sSig) impl₁ :=
  elabSeal.evmrg (SCE.Value.vlrec (SCE.Value.vclos SCE.Value.vunit))
    (SCE.Value.vlrec (SCE.Value.vclos SCE.Value.vunit))
    (elabSeal.elrec (elabSeal.eclos SCE.Value.vunit (elabSeal.eunit _)
      (elabSeal.eproj elabSeal.equery (SCE.SLookup.zero _ _)) disj_top))
    (elabSeal.elrec (elabSeal.eclos SCE.Value.vunit (elabSeal.eunit _)
      (elabSeal.eproj elabSeal.equery (SCE.SLookup.zero _ _)) disj_top))
    (disj_rcd_ne (by decide))

theorem sImpl₂_elab : elabSeal sstore₂ .top sImpl₂ (SCE.substBrand 0 sR₂ sSig) impl₂ :=
  elabSeal.evmrg (SCE.Value.vlrec (SCE.Value.vclos SCE.Value.vunit))
    (SCE.Value.vlrec (SCE.Value.vclos SCE.Value.vunit))
    (elabSeal.elrec (elabSeal.eclos SCE.Value.vunit (elabSeal.eunit _)
      (elabSeal.elrec (elabSeal.eproj elabSeal.equery (SCE.SLookup.zero _ _))) disj_top))
    (elabSeal.elrec (elabSeal.eclos SCE.Value.vunit (elabSeal.eunit _)
      (elabSeal.erproj (elabSeal.eproj elabSeal.equery (SCE.SLookup.zero _ _))
        (SCE.SRLookup.zero _ _)) disj_top))
    (disj_rcd_ne (by decide))

theorem sClient_elab : elabSeal SCE.noBrands sSig sClient .int client :=
  elabSeal.eapp
    (elabSeal.erproj elabSeal.equery
      (SCE.SRLookup.andr _ _ _ _ (SCE.SRLookup.zero _ _) (labelin_rcd_ne (by decide))))
    (elabSeal.eapp
      (elabSeal.erproj elabSeal.equery
        (SCE.SRLookup.andl _ _ _ _ (SCE.SRLookup.zero _ _) (labelin_rcd_ne (by decide))))
      (elabSeal.elit _ 5))

theorem openbrand_src : OpenBrand (sealStore sstore₁) (sealStore sstore₂) ηex 0 .int R₂ :=
  { openbrand_ex with st₁ := rfl, st₂ := rfl }

-- Both sealed source programs run (through the source coercion proxies) to 5.  The
-- sealed providers are the records of proxies the source coercion builds:
def sProxies₁ : SCE.Exp :=
  .mrg (.lrec "mk" (.clos (S_Sem.proxyEnv sIdClos) .int
        (.mseal 0 .int sα (.app S_Sem.proxyFun (.munseal 0 .int .int (.proj .query 0))))))
      (.lrec "get" (.clos (S_Sem.proxyEnv sIdClos) sα
        (.mseal 0 .int .int (.app S_Sem.proxyFun (.munseal 0 .int sα (.proj .query 0))))))

def sProxies₂ : SCE.Exp :=
  .mrg (.lrec "mk" (.clos (S_Sem.proxyEnv sBoxClos) .int
        (.mseal 0 sR₂ sα (.app S_Sem.proxyFun (.munseal 0 sR₂ .int (.proj .query 0))))))
      (.lrec "get" (.clos (S_Sem.proxyEnv sUnboxClos) sα
        (.mseal 0 sR₂ .int (.app S_Sem.proxyFun (.munseal 0 sR₂ sα (.proj .query 0))))))

open S_Sem in
theorem sRun₁ : BStep .unit (.box (.mseal 0 .int sSig sImpl₁) sClient) (.lit 5) := by
  have hc : SCE.Value sIdClos := SCE.Value.vclos SCE.Value.vunit
  have hPE : SCE.Value (S_Sem.proxyEnv sIdClos) := SCE.Value.vmrg SCE.Value.vunit (SCE.Value.vlrec hc)
  have hP : SCE.Value sProxies₁ :=
    SCE.Value.vmrg (SCE.Value.vlrec (SCE.Value.vclos hPE)) (SCE.Value.vlrec (SCE.Value.vclos hPE))
  have hE₁ : SCE.Value (.mrg (S_Sem.proxyEnv sIdClos) (.lit 5)) := SCE.Value.vmrg hPE SCE.Value.vint
  have hE₂ : SCE.Value (.mrg (S_Sem.proxyEnv sIdClos) (.wrap 0 (.lit 5))) :=
    SCE.Value.vmrg hPE (SCE.Value.vwrap SCE.Value.vint)
  have hE₀ : SCE.Value (.mrg .unit (.lit 5)) := SCE.Value.vmrg SCE.Value.vunit SCE.Value.vint
  refine BStep.box (v₁ := sProxies₁) SCE.Value.vunit ?_ ?_
  · -- the provider seals to the two proxies
    exact BStep.mseal SCE.Value.vunit
      (BStep.dmrg SCE.Value.vunit (BStep.lrec SCE.Value.vunit (BStep.clos_val SCE.Value.vunit SCE.Value.vunit))
        (BStep.lrec (SCE.Value.vmrg SCE.Value.vunit (SCE.Value.vlrec hc))
          (BStep.clos_val (SCE.Value.vmrg SCE.Value.vunit (SCE.Value.vlrec hc)) SCE.Value.vunit)))
      (SSealV.and (SSealV.rcd SSealV.arr) (SSealV.rcd SSealV.arr))
  · -- get (mk 5): mk's proxy unseals 5, applies id, seals to a wrapper; get's proxy
    -- unwraps it, applies id, and returns 5
    refine BStep.app_clos (v₂ := .wrap 0 (.lit 5)) hP (BStep.rproj hP (BStep.query hP) (Sel.dmrg_right Sel.rcd)) ?_ ?_
    · refine BStep.app_clos hP (BStep.rproj hP (BStep.query hP) (Sel.dmrg_left Sel.rcd))
        (BStep.lit hP) ?_
      exact BStep.mseal hE₁
        (BStep.app_clos hE₁
          (BStep.rproj hE₁ (BStep.proj hE₁ (BStep.query hE₁) (LookupV.dmrg_succ LookupV.dmrg_zero))
            Sel.rcd)
          (BStep.munseal hE₁ (BStep.proj hE₁ (BStep.query hE₁) LookupV.dmrg_zero) SUnsealV.int)
          (BStep.proj hE₀ (BStep.query hE₀) LookupV.dmrg_zero))
        SSealV.brand_eq
    · exact BStep.mseal hE₂
        (BStep.app_clos hE₂
          (BStep.rproj hE₂ (BStep.proj hE₂ (BStep.query hE₂) (LookupV.dmrg_succ LookupV.dmrg_zero))
            Sel.rcd)
          (BStep.munseal hE₂ (BStep.proj hE₂ (BStep.query hE₂) LookupV.dmrg_zero) SUnsealV.brand_eq)
          (BStep.proj hE₀ (BStep.query hE₀) LookupV.dmrg_zero))
        SSealV.int

open S_Sem in
theorem sRun₂ : BStep .unit (.box (.mseal 0 sR₂ sSig sImpl₂) sClient) (.lit 5) := by
  have hcm : SCE.Value sBoxClos := SCE.Value.vclos SCE.Value.vunit
  have hcg : SCE.Value sUnboxClos := SCE.Value.vclos SCE.Value.vunit
  have hPEm : SCE.Value (S_Sem.proxyEnv sBoxClos) := SCE.Value.vmrg SCE.Value.vunit (SCE.Value.vlrec hcm)
  have hPEg : SCE.Value (S_Sem.proxyEnv sUnboxClos) := SCE.Value.vmrg SCE.Value.vunit (SCE.Value.vlrec hcg)
  have hP : SCE.Value sProxies₂ :=
    SCE.Value.vmrg (SCE.Value.vlrec (SCE.Value.vclos hPEm)) (SCE.Value.vlrec (SCE.Value.vclos hPEg))
  have hE₁ : SCE.Value (.mrg (S_Sem.proxyEnv sBoxClos) (.lit 5)) := SCE.Value.vmrg hPEm SCE.Value.vint
  have hE₂ : SCE.Value (.mrg (S_Sem.proxyEnv sUnboxClos) (.wrap 0 (.lrec "v" (.lit 5)))) :=
    SCE.Value.vmrg hPEg (SCE.Value.vwrap (SCE.Value.vlrec SCE.Value.vint))
  have hE₀ : SCE.Value (.mrg .unit (.lit 5)) := SCE.Value.vmrg SCE.Value.vunit SCE.Value.vint
  have hE₀' : SCE.Value (.mrg .unit (.lrec "v" (.lit 5))) :=
    SCE.Value.vmrg SCE.Value.vunit (SCE.Value.vlrec SCE.Value.vint)
  refine BStep.box (v₁ := sProxies₂) SCE.Value.vunit ?_ ?_
  · exact BStep.mseal SCE.Value.vunit
      (BStep.dmrg SCE.Value.vunit (BStep.lrec SCE.Value.vunit (BStep.clos_val SCE.Value.vunit SCE.Value.vunit))
        (BStep.lrec (SCE.Value.vmrg SCE.Value.vunit (SCE.Value.vlrec hcm))
          (BStep.clos_val (SCE.Value.vmrg SCE.Value.vunit (SCE.Value.vlrec hcm)) SCE.Value.vunit)))
      (SSealV.and (SSealV.rcd SSealV.arr) (SSealV.rcd SSealV.arr))
  · refine BStep.app_clos (v₂ := .wrap 0 (.lrec "v" (.lit 5))) hP (BStep.rproj hP (BStep.query hP) (Sel.dmrg_right Sel.rcd)) ?_ ?_
    · refine BStep.app_clos hP (BStep.rproj hP (BStep.query hP) (Sel.dmrg_left Sel.rcd))
        (BStep.lit hP) ?_
      exact BStep.mseal hE₁
        (BStep.app_clos hE₁
          (BStep.rproj hE₁ (BStep.proj hE₁ (BStep.query hE₁) (LookupV.dmrg_succ LookupV.dmrg_zero))
            Sel.rcd)
          (BStep.munseal hE₁ (BStep.proj hE₁ (BStep.query hE₁) LookupV.dmrg_zero) SUnsealV.int)
          (BStep.lrec hE₀ (BStep.proj hE₀ (BStep.query hE₀) LookupV.dmrg_zero)))
        SSealV.brand_eq
    · exact BStep.mseal hE₂
        (BStep.app_clos hE₂
          (BStep.rproj hE₂ (BStep.proj hE₂ (BStep.query hE₂) (LookupV.dmrg_succ LookupV.dmrg_zero))
            Sel.rcd)
          (BStep.munseal hE₂ (BStep.proj hE₂ (BStep.query hE₂) LookupV.dmrg_zero) SUnsealV.brand_eq)
          (BStep.rproj hE₀' (BStep.proj hE₀' (BStep.query hE₀') LookupV.dmrg_zero) Sel.rcd))
        SSealV.int

-- Source-level representation independence, instantiated: whatever the two sealed source
-- programs `box (mseal 0 Rᵢ sSig sImplᵢ) sClient` evaluate to, it is the same literal
-- (and by sRun₁/sRun₂ they do evaluate).
example {v₁ v₂ : SCE.Exp}
    (h₁ : S_Sem.BStep .unit (.box (.mseal 0 .int sSig sImpl₁) sClient) v₁)
    (h₂ : S_Sem.BStep .unit (.box (.mseal 0 sR₂ sSig sImpl₂) sClient) v₂)
    : ∃ i, v₁ = .lit i ∧ v₂ = .lit i :=
  source_representation_independence openbrand_src rfl rfl wfsig_ex₁ wfsig_ex₂
    sImpl₁_elab sImpl₂_elab impl_related sClient_elab
    (by simp [sClient, SCE.SFinitary]) h₁ h₂

end RIExample

end Seal
