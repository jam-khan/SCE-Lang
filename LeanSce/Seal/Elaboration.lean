import LeanSce.SCE.Syntax
import LeanSce.SCE.Semantics
import LeanSce.Seal.CastingLemmas

-- Type-preserving elaboration of λSCE's module/linking fragment into λE^≤.
--
-- Scope: everything except unions (inl/inr/case), fix (flam/fclos), and iso-recursive
-- types (fold/unfold) — those require casting rules that exist in neither source paper
-- (see DESIGN.md).  `sealTyp` maps the unsupported type formers to ε as inert junk; no
-- elaboration rule produces an expression whose behavior depends on them.
--
-- Two things change relative to the SCE→Core elaboration (SCE/Elaboration.lean):
--
-- 1. Every rule that extends a context — merges, lambdas, closures, links — now carries
--    the disjointness premises λE^≤'s type system demands (Disj on the sealTyp images).
--    This is the obligation predicted by DESIGN.md (c): the source type system must
--    check disjointness or elaborated merges will not type.
--
-- 2. The bind-once combinators are gone.  Core's `nmrgCore`/`linkedCore` use the
--    self-application idiom (λ⟦Γ⟧. …) ? to evaluate both operands under the ambient
--    environment; that pattern is UNTYPEABLE in λE^≤, because tlam demands Disj Γ Γ,
--    which fails for any non-top-like Γ.  Sealing itself replaces the trick: (? : Γ)
--    restricts the extended environment back to the ambient one, so the non-capturing
--    merge is simply  mrg e₁ (box (? : Γ) e₂).  The construct that motivated λE's
--    combinator machinery is a one-liner once restriction is a first-class operation.
--
-- Type abstraction (DESIGN.md §(g)): the source sealing forms `wrap`/`mseal`/`munseal`
-- elaborate to λE^≤'s `wrap`/`seal`/`unseal` one-to-one, and `Typ.brand n` to
-- `Typ.brand n`.  The elaboration judgment carries a source brand store Δ (SCE types);
-- the elaborated code types under its image `sealStore Δ`.  Only the three sealing rules
-- consult Δ, exactly like the target's twrap/tseal/tunseal.
namespace Seal

variable {Δ : SCE.BrandStore}

mutual
@[simp]
def sealTyp : SCE.Typ → Seal.Typ
  | .int       => .int
  | .top       => .top
  | .arr A B   => .arr (sealTyp A) (sealTyp B)
  | .and A B   => .and (sealTyp A) (sealTyp B)
  | .or A B    => .or (sealTyp A) (sealTyp B)
  | .rcd l A   => .rcd l (sealTyp A)
  | .sig mt    => sealModTyp mt
  | .var n     => .var n
  | .mu T      => .mu (sealTyp T)
  | .brand n   => .brand n

@[simp]
def sealModTyp : SCE.ModTyp → Seal.Typ
  | .TyIntf T     => sealTyp T
  | .TyArrM T mt  => .arr (sealTyp T) (sealModTyp mt)
end

-- The target store is the image of the source store.
def sealStore (Δ : SCE.BrandStore) : Seal.BrandStore := fun n => (Δ n).map sealTyp

theorem sealStore_some {n : Nat} {R : SCE.Typ} (h : Δ n = some R)
    : sealStore Δ n = some (sealTyp R) := by
  simp [sealStore, h]

theorem sealStore_noBrands : sealStore SCE.noBrands = noBrands := rfl

theorem sealStore_le {Δ Δ' : SCE.BrandStore} (h : SCE.StoreLe Δ Δ')
    : StoreLe (sealStore Δ) (sealStore Δ') := by
  intro n R hn
  simp only [sealStore, Option.map_eq_some_iff] at hn ⊢
  obtain ⟨R₀, h₀, rfl⟩ := hn
  exact ⟨R₀, h _ _ h₀, rfl⟩

-- sealTyp images are brand-variable-free: the source has no brand variables, and
-- sealTyp never produces one.  This discharges the ¬HasBVar premises of tseal/tunseal
-- and the strengthened WfSig at every elaboration site.
mutual
theorem sealTyp_no_hasbvar : (S : SCE.Typ) → ¬ HasBVar (sealTyp S)
  | .int => fun h => nomatch h
  | .top => fun h => nomatch h
  | .arr A B => fun h => by
    cases h with
    | arrl h' => exact sealTyp_no_hasbvar A h'
    | arrr h' => exact sealTyp_no_hasbvar B h'
  | .and A B => fun h => by
    cases h with
    | andl h' => exact sealTyp_no_hasbvar A h'
    | andr h' => exact sealTyp_no_hasbvar B h'
  | .or A B => fun h => by
    cases h with
    | orl h' => exact sealTyp_no_hasbvar A h'
    | orr h' => exact sealTyp_no_hasbvar B h'
  | .rcd _ A => fun h => by
    cases h with
    | rcd h' => exact sealTyp_no_hasbvar A h'
  | .sig mt => sealModTyp_no_hasbvar mt
  | .var _ => fun h => nomatch h
  | .mu T => fun h => by
    cases h with
    | mu h' => exact sealTyp_no_hasbvar T h'
  | .brand _ => fun h => nomatch h

theorem sealModTyp_no_hasbvar : (mt : SCE.ModTyp) → ¬ HasBVar (sealModTyp mt)
  | .TyIntf T => sealTyp_no_hasbvar T
  | .TyArrM T mt => fun h => by
    cases h with
    | arrl h' => exact sealTyp_no_hasbvar T h'
    | arrr h' => exact sealModTyp_no_hasbvar mt h'
end

-- sealTyp images are likewise ∀-free (the source has no ∀-types), discharging the
-- ¬AllbIn μ-fence of tfold/tunfold at every elaboration site.
mutual
theorem sealTyp_no_allbin : (S : SCE.Typ) → ¬ AllbIn (sealTyp S)
  | .int => fun h => nomatch h
  | .top => fun h => nomatch h
  | .arr A B => fun h => by
    cases h with
    | arrl h' => exact sealTyp_no_allbin A h'
    | arrr h' => exact sealTyp_no_allbin B h'
  | .and A B => fun h => by
    cases h with
    | andl h' => exact sealTyp_no_allbin A h'
    | andr h' => exact sealTyp_no_allbin B h'
  | .or A B => fun h => by
    cases h with
    | orl h' => exact sealTyp_no_allbin A h'
    | orr h' => exact sealTyp_no_allbin B h'
  | .rcd _ A => fun h => by
    cases h with
    | rcd h' => exact sealTyp_no_allbin A h'
  | .sig mt => sealModTyp_no_allbin mt
  | .var _ => fun h => nomatch h
  | .mu T => fun h => by
    cases h with
    | mu h' => exact sealTyp_no_allbin T h'
  | .brand _ => fun h => nomatch h

theorem sealModTyp_no_allbin : (mt : SCE.ModTyp) → ¬ AllbIn (sealModTyp mt)
  | .TyIntf T => sealTyp_no_allbin T
  | .TyArrM T mt => fun h => by
    cases h with
    | arrl h' => exact sealTyp_no_allbin T h'
    | arrr h' => exact sealModTyp_no_allbin mt h'
end

-- sealTyp commutes with brand substitution (the representation view of a signature is
-- sealed pointwise).
mutual
theorem sealTyp_substBrand (n : Nat) (R : SCE.Typ) : (S : SCE.Typ)
    → sealTyp (SCE.substBrand n R S) = Seal.substBrand n (sealTyp R) (sealTyp S)
  | .int => rfl
  | .top => rfl
  | .arr A B => by
    simp only [SCE.substBrand, sealTyp, Seal.substBrand,
      sealTyp_substBrand n R A, sealTyp_substBrand n R B]
  | .and A B => by
    simp only [SCE.substBrand, sealTyp, Seal.substBrand,
      sealTyp_substBrand n R A, sealTyp_substBrand n R B]
  | .or A B => by
    simp only [SCE.substBrand, sealTyp, Seal.substBrand,
      sealTyp_substBrand n R A, sealTyp_substBrand n R B]
  | .rcd l A => by
    simp only [SCE.substBrand, sealTyp, Seal.substBrand, sealTyp_substBrand n R A]
  | .sig mt => sealModTyp_substBrand n R mt
  | .var _ => rfl
  | .mu T => by
    simp only [SCE.substBrand, sealTyp, Seal.substBrand, sealTyp_substBrand n R T]
  | .brand m => by
    simp only [SCE.substBrand, sealTyp, Seal.substBrand]
    split <;> rfl

theorem sealModTyp_substBrand (n : Nat) (R : SCE.Typ) : (mt : SCE.ModTyp)
    → sealModTyp (SCE.substBrandModTyp n R mt) = Seal.substBrand n (sealTyp R) (sealModTyp mt)
  | .TyIntf T => sealTyp_substBrand n R T
  | .TyArrM T mt => by
    simp only [SCE.substBrandModTyp, sealModTyp, Seal.substBrand,
      sealTyp_substBrand n R T, sealModTyp_substBrand n R mt]
end

-- sealTyp commutes with the μ-unfolding substitution (what efold/eunfold's type
-- preservation needs).
mutual
theorem sealTyp_substTyp (d : Nat) (S : SCE.Typ) : (T : SCE.Typ)
    → sealTyp (SCE.substTyp d S T) = Seal.substTyp d (sealTyp S) (sealTyp T)
  | .int => rfl
  | .top => rfl
  | .arr A B => by
    simp only [SCE.substTyp, sealTyp, Seal.substTyp,
      sealTyp_substTyp d S A, sealTyp_substTyp d S B]
  | .and A B => by
    simp only [SCE.substTyp, sealTyp, Seal.substTyp,
      sealTyp_substTyp d S A, sealTyp_substTyp d S B]
  | .or A B => by
    simp only [SCE.substTyp, sealTyp, Seal.substTyp,
      sealTyp_substTyp d S A, sealTyp_substTyp d S B]
  | .rcd l A => by
    simp only [SCE.substTyp, sealTyp, Seal.substTyp, sealTyp_substTyp d S A]
  | .sig mt => by
    simp only [SCE.substTyp, sealTyp, sealModTyp_substTyp d S mt]
  | .var m => by
    by_cases h : m = d <;> simp [SCE.substTyp, sealTyp, Seal.substTyp, h]
  | .mu T => by
    simp only [SCE.substTyp, sealTyp, Seal.substTyp, sealTyp_substTyp (d + 1) S T]
  | .brand _ => rfl

theorem sealModTyp_substTyp (d : Nat) (S : SCE.Typ) : (mt : SCE.ModTyp)
    → sealModTyp (SCE.substModTyp d S mt) = Seal.substTyp d (sealTyp S) (sealModTyp mt)
  | .TyIntf T => sealTyp_substTyp d S T
  | .TyArrM T mt => by
    simp only [SCE.substModTyp, sealModTyp, Seal.substTyp,
      sealTyp_substTyp d S T, sealModTyp_substTyp d S mt]
end

-- A source type whose image is brand-free is untouched by source brand substitution
-- (sealTyp preserves brands exactly, so occurrence in the image reflects occurrence in
-- the source).  This is what makes the identity coercion at brand-free μ signatures
-- type-correct at the source.
mutual
theorem sce_substBrand_notin {n : Nat} {R : SCE.Typ}
    : {S : SCE.Typ} → ¬ Seal.BrandIn n (sealTyp S) → SCE.substBrand n R S = S
  | .int, _ => rfl
  | .top, _ => rfl
  | .arr A B, h => by
    simp only [SCE.substBrand,
      sce_substBrand_notin (fun h' => h (BrandIn.arrl h')),
      sce_substBrand_notin (fun h' => h (BrandIn.arrr h'))]
  | .and A B, h => by
    simp only [SCE.substBrand,
      sce_substBrand_notin (fun h' => h (BrandIn.andl h')),
      sce_substBrand_notin (fun h' => h (BrandIn.andr h'))]
  | .or A B, h => by
    simp only [SCE.substBrand,
      sce_substBrand_notin (fun h' => h (BrandIn.orl h')),
      sce_substBrand_notin (fun h' => h (BrandIn.orr h'))]
  | .rcd l A, h => by
    simp only [SCE.substBrand, sce_substBrand_notin (fun h' => h (BrandIn.rcd h'))]
  | .sig mt, h => by
    simp only [SCE.substBrand, sce_substBrandModTyp_notin h]
  | .var _, _ => rfl
  | .mu T, h => by
    simp only [SCE.substBrand, sce_substBrand_notin (fun h' => h (BrandIn.mu h'))]
  | .brand m, h => by
    by_cases hm : m = n
    · subst hm; exact absurd BrandIn.self h
    · simp only [SCE.substBrand, hm, if_false]

theorem sce_substBrandModTyp_notin {n : Nat} {R : SCE.Typ}
    : {mt : SCE.ModTyp} → ¬ Seal.BrandIn n (sealModTyp mt) → SCE.substBrandModTyp n R mt = mt
  | .TyIntf T, h => by
    simp only [SCE.substBrandModTyp, sce_substBrand_notin h]
  | .TyArrM T mt, h => by
    simp only [SCE.substBrandModTyp,
      sce_substBrand_notin (fun h' => h (BrandIn.arrl h')),
      sce_substBrandModTyp_notin (fun h' => h (BrandIn.arrr h'))]
end

-- ── Transport of the lookup judgments along sealTyp ──────────────────────────────────

theorem slookup_seal {A : SCE.Typ} {n : Nat} {B : SCE.Typ} (h : SCE.SLookup A n B)
    : Seal.Lookup (sealTyp A) n (sealTyp B) := by
  induction h with
  | zero A B => exact Lookup.zero
  | succ A B n C _ ih => exact Lookup.succ ih

-- A label present in the image was present in the source (the direction the negative
-- containment premises need).
mutual
theorem lin_seal : {B : SCE.Typ} → {l : String} → Seal.Lin l (sealTyp B) → SCE.LabelIn l B
  | .rcd _ _, _, .rcd => SCE.LabelIn.rcd _ _
  | .and _ _, _, .andl h => SCE.LabelIn.andl _ _ _ (lin_seal h)
  | .and _ _, _, .andr h => SCE.LabelIn.andr _ _ _ (lin_seal h)
  | .sig _, _, h => lin_modtyp_seal h

theorem lin_modtyp_seal : {mt : SCE.ModTyp} → {l : String} → Seal.Lin l (sealModTyp mt)
    → SCE.LabelIn l (.sig mt)
  | .TyIntf _, _, h => SCE.LabelIn.sig _ _ (lin_seal h)
end

theorem srlookup_seal {B : SCE.Typ} {l : String} {A : SCE.Typ} (h : SCE.SRLookup B l A)
    : Seal.RLookup (sealTyp B) l (sealTyp A) := by
  induction h with
  | zero l T => exact RLookup.zero
  | andl A B l T _ hnl ih =>
    exact RLookup.landl ih (fun hlin => hnl (lin_seal hlin))
  | andr A B l T _ hnl ih =>
    exact RLookup.landr ih (fun hlin => hnl (lin_seal hlin))
  | sig l T A _ ih => exact ih

-- ── Seal-side link plumbing ──────────────────────────────────────────────────────────

-- Import package for an n-ary link: one record per labeled import, later components
-- evaluated under the ambient environment restored by sealing.
def wireArgSeal (ctx : Seal.Typ) (ce₁ : Seal.Exp) : SCE.Typ → Seal.Exp
  | .rcd l _ => .lrec l (.rproj ce₁ l)
  | .and D (.rcd l _) =>
    .mrg (wireArgSeal ctx ce₁ D) (.box (.anno .query ctx) (.lrec l (.rproj ce₁ l)))
  | _ => .unit

-- Well-formedness of an import interface for linking against a module of type Γ₁ in
-- ambient context Γ: every import is present in the module, and the accumulated package
-- is disjoint enough to merge.  This is the disjointness-enriched LinkOk that λE^≤
-- requires (SCE's LinkOk carries only the lookups).
inductive WireOk (Γ : Seal.Typ) (Γ₁ : SCE.Typ) : SCE.Typ → Prop where
  | one {l : String} {A : SCE.Typ}
    : SCE.SRLookup Γ₁ l A
    → WireOk Γ Γ₁ (.rcd l A)
  | more {D : SCE.Typ} {l : String} {A : SCE.Typ}
    : WireOk Γ Γ₁ D
    → SCE.SRLookup Γ₁ l A
    → Seal.Disj (sealTyp D) Γ
    → Seal.Disj (sealTyp D) (.rcd l (sealTyp A))
    → WireOk Γ Γ₁ (.and D (.rcd l A))

-- The package inhabits the import interface.
theorem wireArgSeal_typed {Δ' : Seal.BrandStore} {Γ : Seal.Typ} {Γ₁ : SCE.Typ}
    {ce₁ : Seal.Exp} {D : SCE.Typ}
    (hw : WireOk Γ Γ₁ D) (ht₁ : Seal.HasType Δ' Γ ce₁ (sealTyp Γ₁))
    : Seal.HasType Δ' Γ (wireArgSeal Γ ce₁ D) (sealTyp D) := by
  induction hw with
  | one hl => exact HasType.trcd (HasType.trproj ht₁ (srlookup_seal hl))
  | more _ hl hd₁ hd₂ ih =>
    exact HasType.tmrg ih
      (HasType.tbox (HasType.tanno HasType.tquery (Sub.sandl (sub_refl _)))
        (HasType.trcd (HasType.trproj ht₁ (srlookup_seal hl))))
      hd₁ hd₂

-- ── The elaboration relation ─────────────────────────────────────────────────────────

inductive elabSeal (Δ : SCE.BrandStore) : SCE.Typ → SCE.Exp → SCE.Typ → Seal.Exp → Prop where
  | equery {ctx}
    : elabSeal Δ ctx .query ctx .query
  | elit (ctx : SCE.Typ) (n : Nat)
    : elabSeal Δ ctx (.lit n) .int (.lit n)
  | eunit (ctx : SCE.Typ)
    : elabSeal Δ ctx .unit .top .unit
  | eapp {ctx A B : SCE.Typ} {se₁ se₂ : SCE.Exp} {ce₁ ce₂ : Seal.Exp}
    : elabSeal Δ ctx se₁ (.arr A B) ce₁
    → elabSeal Δ ctx se₂ A ce₂
    → elabSeal Δ ctx (.app se₁ se₂) B (.app ce₁ ce₂)
  | eproj {ctx A B : SCE.Typ} {se : SCE.Exp} {ce : Seal.Exp} {i : Nat}
    : elabSeal Δ ctx se A ce
    → SCE.SLookup A i B
    → elabSeal Δ ctx (.proj se i) B (.proj ce i)
  | ebox {ctx ctx' A : SCE.Typ} {se₁ se₂ : SCE.Exp} {ce₁ ce₂ : Seal.Exp}
    : elabSeal Δ ctx se₁ ctx' ce₁
    → elabSeal Δ ctx' se₂ A ce₂
    → elabSeal Δ ctx (.box se₁ se₂) A (.box ce₁ ce₂)
  -- dependent merge: now carries λE^≤'s two disjointness side conditions
  | edmrg {ctx A B : SCE.Typ} {se₁ se₂ : SCE.Exp} {ce₁ ce₂ : Seal.Exp}
    : elabSeal Δ ctx se₁ A ce₁
    → elabSeal Δ (.and ctx A) se₂ B ce₂
    → Seal.Disj (sealTyp A) (sealTyp ctx)
    → Seal.Disj (sealTyp A) (sealTyp B)
    → elabSeal Δ ctx (.mrg se₁ se₂) (.and A B) (.mrg ce₁ ce₂)
  -- value merges elaborate context-freely (the elaboration-level mirror of tmergev;
  -- needed so value elaborations stay context-irrelevant, since edmrg's Disj A Γ premise
  -- is context-sensitive)
  | evmrg {ctx A B : SCE.Typ} {v₁ v₂ : SCE.Exp} {w₁ w₂ : Seal.Exp}
    : SCE.Value v₁
    → SCE.Value v₂
    → elabSeal Δ .top v₁ A w₁
    → elabSeal Δ .top v₂ B w₂
    → Seal.Disj (sealTyp A) (sealTyp B)
    → elabSeal Δ ctx (.mrg v₁ v₂) (.and A B) (.mrg w₁ w₂)
  -- non-capturing merge: the bind-once combinator is replaced by sealing the extended
  -- environment back to the ambient context
  | enmrg {ctx A B : SCE.Typ} {se₁ se₂ : SCE.Exp} {ce₁ ce₂ : Seal.Exp}
    : elabSeal Δ ctx se₁ A ce₁
    → elabSeal Δ ctx se₂ B ce₂
    → Seal.Disj (sealTyp A) (sealTyp ctx)
    → Seal.Disj (sealTyp A) (sealTyp B)
    → elabSeal Δ ctx (.nmrg se₁ se₂) (.and A B)
        (.mrg ce₁ (.box (.anno .query (sealTyp ctx)) ce₂))
  -- λE^≤ lambdas carry the codomain, which elaboration already infers
  | elam {ctx A B : SCE.Typ} {se : SCE.Exp} {ce : Seal.Exp}
    : elabSeal Δ (.and ctx A) se B ce
    → Seal.Disj (sealTyp ctx) (sealTyp A)
    → elabSeal Δ ctx (.lam A se) (.arr A B) (.lam (sealTyp A) (sealTyp B) ce)
  | erproj {ctx A B : SCE.Typ} {se : SCE.Exp} {ce : Seal.Exp} {l : String}
    : elabSeal Δ ctx se B ce
    → SCE.SRLookup B l A
    → elabSeal Δ ctx (.rproj se l) A (.rproj ce l)
  | eclos {ctx ctx' A B : SCE.Typ} {se₁ se₂ : SCE.Exp} {ce₁ ce₂ : Seal.Exp}
    : SCE.Value se₁
    → elabSeal Δ .top se₁ ctx' ce₁
    → elabSeal Δ (.and ctx' A) se₂ B ce₂
    → Seal.Disj (sealTyp ctx') (sealTyp A)
    → elabSeal Δ ctx (.clos se₁ A se₂) (.arr A B)
        (.clos ce₁ (sealTyp A) (sealTyp B) ce₂)
  | elrec {ctx A : SCE.Typ} {se : SCE.Exp} {ce : Seal.Exp} {l : String}
    : elabSeal Δ ctx se A ce
    → elabSeal Δ ctx (.lrec l se) (.rcd l A) (.lrec l ce)
  | eletb {ctx A B : SCE.Typ} {se₁ se₂ : SCE.Exp} {ce₁ ce₂ : Seal.Exp}
    : elabSeal Δ ctx se₁ A ce₁
    → elabSeal Δ (.and ctx A) se₂ B ce₂
    → Seal.Disj (sealTyp ctx) (sealTyp A)
    → elabSeal Δ ctx (.letb se₁ se₂) B
        (.app (.lam (sealTyp A) (sealTyp B) ce₂) ce₁)
  | eopenm {ctx A B : SCE.Typ} {se₁ se₂ : SCE.Exp} {ce₁ ce₂ : Seal.Exp} {l : String}
    : elabSeal Δ ctx se₁ (.rcd l A) ce₁
    → elabSeal Δ (.and ctx A) se₂ B ce₂
    → Seal.Disj (sealTyp ctx) (sealTyp A)
    → elabSeal Δ ctx (.openm se₁ se₂) B
        (.app (.lam (sealTyp A) (sealTyp B) ce₂) (.rproj ce₁ l))
  -- unions: injections are free; case extends the context per branch, hence the Disj
  -- premises on the sealTyp images
  | einl {ctx A B : SCE.Typ} {se : SCE.Exp} {ce : Seal.Exp}
    : elabSeal Δ ctx se A ce
    → elabSeal Δ ctx (.inl B se) (.or A B) (.inl (sealTyp B) ce)
  | einr {ctx A B : SCE.Typ} {se : SCE.Exp} {ce : Seal.Exp}
    : elabSeal Δ ctx se B ce
    → elabSeal Δ ctx (.inr A se) (.or A B) (.inr (sealTyp A) ce)
  | ecase {ctx A B C : SCE.Typ} {se se₁ se₂ : SCE.Exp} {ce ce₁ ce₂ : Seal.Exp}
    : elabSeal Δ ctx se (.or A B) ce
    → elabSeal Δ (.and ctx A) se₁ C ce₁
    → elabSeal Δ (.and ctx B) se₂ C ce₂
    → Seal.Disj (sealTyp ctx) (sealTyp A)
    → Seal.Disj (sealTyp ctx) (sealTyp B)
    → elabSeal Δ ctx (.case se se₁ se₂) C (.case ce ce₁ ce₂)
  -- fixpoints: the body extends the context twice (self, then argument)
  | eflam {ctx A B : SCE.Typ} {se : SCE.Exp} {ce : Seal.Exp}
    : elabSeal Δ (.and (.and ctx (.arr A B)) A) se B ce
    → Seal.Disj (sealTyp ctx) (.arr (sealTyp A) (sealTyp B))
    → Seal.Disj (.and (sealTyp ctx) (.arr (sealTyp A) (sealTyp B))) (sealTyp A)
    → elabSeal Δ ctx (.flam A B se) (.arr A B) (.flam (sealTyp A) (sealTyp B) ce)
  | efclos {ctx ctx' A B : SCE.Typ} {se₁ se₂ : SCE.Exp} {ce₁ ce₂ : Seal.Exp}
    : SCE.Value se₁
    → elabSeal Δ .top se₁ ctx' ce₁
    → elabSeal Δ (.and (.and ctx' (.arr A B)) A) se₂ B ce₂
    → Seal.Disj (sealTyp ctx') (.arr (sealTyp A) (sealTyp B))
    → Seal.Disj (.and (sealTyp ctx') (.arr (sealTyp A) (sealTyp B))) (sealTyp A)
    → elabSeal Δ ctx (.fclos se₁ A B se₂) (.arr A B)
        (.fclos ce₁ (sealTyp A) (sealTyp B) (sealTyp B) ce₂)
  -- iso-recursive types: one-to-one; eunfold's result type is equation-guarded
  | efold {ctx T : SCE.Typ} {se : SCE.Exp} {ce : Seal.Exp}
    : elabSeal Δ ctx se (SCE.substTyp 0 (.mu T) T) ce
    → elabSeal Δ ctx (.fold T se) (.mu T) (.fold (sealTyp T) ce)
  | eunfold {ctx T A : SCE.Typ} {se : SCE.Exp} {ce : Seal.Exp}
    : elabSeal Δ ctx se (.mu T) ce
    → A = SCE.substTyp 0 (.mu T) T
    → elabSeal Δ ctx (.unfold se) A (.unfold ce)
  | emstruct {ctx ctxInner B : SCE.Typ} {sb : SCE.Sandbox} {se : SCE.Exp} {ce : Seal.Exp}
    : (sb = .sandboxed → ctxInner = .top)
    → (sb = .open_ → ctxInner = ctx)
    → elabSeal Δ ctxInner se B ce
    → elabSeal Δ ctx (.mstruct sb se) B
        (.box (match sb with | .sandboxed => .unit | .open_ => .query) ce)
  | emfunctor {ctx ctxInner A B : SCE.Typ} {sb : SCE.Sandbox} {se : SCE.Exp} {ce : Seal.Exp}
    : (sb = .sandboxed → ctxInner = .and .top A)
    → (sb = .open_ → ctxInner = .and ctx A)
    → (sb = .open_ → Seal.Disj (sealTyp ctx) (sealTyp A))
    → elabSeal Δ ctxInner se B ce
    → elabSeal Δ ctx (.mfunctor sb A se) (.sig (.TyArrM A (.TyIntf B)))
        (match sb with
          | .sandboxed => .box .unit (.lam (sealTyp A) (sealTyp B) ce)
          | .open_ => .lam (sealTyp A) (sealTyp B) ce)
  | emclos {ctx ctx' A B : SCE.Typ} {se₁ se₂ : SCE.Exp} {ce₁ ce₂ : Seal.Exp}
    : SCE.Value se₁
    → elabSeal Δ .top se₁ ctx' ce₁
    → elabSeal Δ (.and ctx' A) se₂ B ce₂
    → Seal.Disj (sealTyp ctx') (sealTyp A)
    → elabSeal Δ ctx (.mclos se₁ A se₂) (.sig (.TyArrM A (.TyIntf B)))
        (.clos ce₁ (sealTyp A) (sealTyp B) ce₂)
  | emapp {ctx A B : SCE.Typ} {se₁ se₂ : SCE.Exp} {ce₁ ce₂ : Seal.Exp}
    : elabSeal Δ ctx se₁ (.sig (.TyArrM A (.TyIntf B))) ce₁
    → elabSeal Δ ctx se₂ A ce₂
    → elabSeal Δ ctx (.mapp se₁ se₂) B (.app ce₁ ce₂)
  -- linking: the module's exports feed the functor's labeled import; both operands are
  -- evaluated under the ambient environment, restored by sealing
  | emlink {ctx Γ₁ A B : SCE.Typ} {l : String} {se₁ se₂ : SCE.Exp} {ce₁ ce₂ : Seal.Exp}
    : elabSeal Δ ctx se₁ Γ₁ ce₁
    → elabSeal Δ ctx se₂ (.sig (.TyArrM (.rcd l A) (.TyIntf B))) ce₂
    → SCE.SRLookup Γ₁ l A
    → Seal.Disj (sealTyp Γ₁) (sealTyp ctx)
    → Seal.Disj (sealTyp Γ₁) (sealTyp B)
    → elabSeal Δ ctx (.mlink se₁ se₂) (.and Γ₁ B)
        (.mrg ce₁ (.box (.anno .query (sealTyp ctx))
          (.app ce₂ (.lrec l (.rproj ce₁ l)))))
  -- n-ary linking, with the disjointness-enriched interface well-formedness
  | emlinkn {ctx Γ₁ D B : SCE.Typ} {se₁ se₂ : SCE.Exp} {ce₁ ce₂ : Seal.Exp}
    : elabSeal Δ ctx se₁ Γ₁ ce₁
    → elabSeal Δ ctx se₂ (.sig (.TyArrM D (.TyIntf B))) ce₂
    → WireOk (sealTyp ctx) Γ₁ D
    → Seal.Disj (sealTyp Γ₁) (sealTyp ctx)
    → Seal.Disj (sealTyp Γ₁) (sealTyp B)
    → elabSeal Δ ctx (.mlinkn se₁ se₂) (.and Γ₁ B)
        (.mrg ce₁ (.box (.anno .query (sealTyp ctx))
          (.app ce₂ (wireArgSeal (sealTyp ctx) ce₁ D))))
  -- ── type abstraction: the three sealing forms elaborate one-to-one ──
  -- A branded value (a runtime form: only the sealing coercion produces it).  Mirrors
  -- twrap: closed value payload at the representation type the store records.
  | ewrap {ctx R : SCE.Typ} {n : Nat} {v : SCE.Exp} {w : Seal.Exp}
    : Δ n = some R
    → SCE.Value v
    → elabSeal Δ .top v R w
    → elabSeal Δ ctx (.wrap n v) (.brand n) (.wrap n w)
  -- The sealing coercion S[n:=R] ⇒ S; the operand elaborates at the representation view.
  -- Side conditions are the target's (tseal): the store records R at n, R has no reserved
  -- label, and S is a well-formed signature for abstracting α_n over R.
  | emseal {ctx R S : SCE.Typ} {n : Nat} {se : SCE.Exp} {ce : Seal.Exp}
    : Δ n = some R
    → NoRes (sealTyp R)
    → WfSig n (sealTyp R) (sealTyp S)
    → elabSeal Δ ctx se (SCE.substBrand n R S) ce
    → elabSeal Δ ctx (.mseal n R S se) S (.seal n (sealTyp R) (sealTyp S) ce)
  -- The converse coercion S ⇒ S[n:=R].  As for the target's tunseal, the result type is
  -- an equation-guarded variable so that inversion at a concrete type does not get stuck
  -- on substBrand.
  | emunseal {ctx R S T : SCE.Typ} {n : Nat} {se : SCE.Exp} {ce : Seal.Exp}
    : Δ n = some R
    → NoRes (sealTyp R)
    → WfSig n (sealTyp R) (sealTyp S)
    → elabSeal Δ ctx se S ce
    → T = SCE.substBrand n R S
    → elabSeal Δ ctx (.munseal n R S se) T (.unseal n (sealTyp R) (sealTyp S) ce)

-- ── Elaboration maps source values to target values ──────────────────────────────────

theorem elabSeal_value {Γ : SCE.Typ} {es : SCE.Exp} {A : SCE.Typ} {ce : Seal.Exp}
    (h : elabSeal Δ Γ es A ce) (hv : SCE.Value es) : Seal.Value ce := by
  induction h with
  | elit _ _ => exact Value.vint
  | eunit _ => exact Value.vunit
  | eclos _ _ _ _ ih₁ _ =>
    cases hv with
    | vclos hv₁ => exact Value.vclos (ih₁ hv₁)
  | emclos _ _ _ _ ih₁ _ =>
    cases hv with
    | vmclos hv₁ => exact Value.vclos (ih₁ hv₁)
  | edmrg _ _ _ _ ih₁ ih₂ =>
    cases hv with
    | vmrg hv₁ hv₂ => exact Value.vmrg (ih₁ hv₁) (ih₂ hv₂)
  | evmrg hv₁ hv₂ _ _ _ ih₁ ih₂ => exact Value.vmrg (ih₁ hv₁) (ih₂ hv₂)
  | elrec _ ih =>
    cases hv with
    | vlrec hv' => exact Value.vrcd (ih hv')
  | equery => nomatch hv
  | eapp _ _ _ _ => nomatch hv
  | eproj _ _ _ => nomatch hv
  | ebox _ _ _ _ => nomatch hv
  | enmrg _ _ _ _ _ _ => nomatch hv
  | elam _ _ _ => nomatch hv
  | erproj _ _ _ => nomatch hv
  | eletb _ _ _ _ _ => nomatch hv
  | eopenm _ _ _ _ _ => nomatch hv
  | emstruct _ _ _ _ => nomatch hv
  | emfunctor _ _ _ _ _ => nomatch hv
  | emapp _ _ _ _ => nomatch hv
  | emlink _ _ _ _ _ _ _ => nomatch hv
  | emlinkn _ _ _ _ _ _ _ => nomatch hv
  | ewrap _ hv' _ ih => exact Value.vwrap (ih hv')
  | emseal _ _ _ _ _ => nomatch hv
  | emunseal _ _ _ _ _ _ => nomatch hv
  | einl _ ih => cases hv with | vinl hv' => exact Value.vinl (ih hv')
  | einr _ ih => cases hv with | vinr hv' => exact Value.vinr (ih hv')
  | ecase _ _ _ _ _ _ _ _ => nomatch hv
  | eflam _ _ _ _ => nomatch hv
  | efclos hval _ _ _ _ ih₁ _ =>
    cases hv with | vfclos _ => exact Value.vfclos (ih₁ hval)
  | efold _ ih => cases hv with | vfold hv' => exact Value.vfold (ih hv')
  | eunfold _ _ _ => nomatch hv

-- ── Store weakening: an elaboration derivation survives extending the store ──────────

-- Only ewrap/emseal/emunseal consult Δ, and each just needs its entry to be present.
-- (This is what lets a client compiled with no knowledge of a representation be composed
-- with the provider that has it.)
theorem elabSeal_weaken_store {Δ' : SCE.BrandStore} (hle : SCE.StoreLe Δ Δ')
    {Γ : SCE.Typ} {es : SCE.Exp} {A : SCE.Typ} {ce : Seal.Exp}
    (h : elabSeal Δ Γ es A ce) : elabSeal Δ' Γ es A ce := by
  induction h with
  | equery => exact elabSeal.equery
  | elit _ _ => exact elabSeal.elit _ _
  | eunit _ => exact elabSeal.eunit _
  | eapp _ _ ih₁ ih₂ => exact elabSeal.eapp ih₁ ih₂
  | eproj _ hl ih => exact elabSeal.eproj ih hl
  | ebox _ _ ih₁ ih₂ => exact elabSeal.ebox ih₁ ih₂
  | edmrg _ _ hd₁ hd₂ ih₁ ih₂ => exact elabSeal.edmrg ih₁ ih₂ hd₁ hd₂
  | evmrg hv₁ hv₂ _ _ hd ih₁ ih₂ => exact elabSeal.evmrg hv₁ hv₂ ih₁ ih₂ hd
  | enmrg _ _ hd₁ hd₂ ih₁ ih₂ => exact elabSeal.enmrg ih₁ ih₂ hd₁ hd₂
  | elam _ hd ih => exact elabSeal.elam ih hd
  | erproj _ hl ih => exact elabSeal.erproj ih hl
  | eclos hv _ _ hd ih₁ ih₂ => exact elabSeal.eclos hv ih₁ ih₂ hd
  | elrec _ ih => exact elabSeal.elrec ih
  | eletb _ _ hd ih₁ ih₂ => exact elabSeal.eletb ih₁ ih₂ hd
  | eopenm _ _ hd ih₁ ih₂ => exact elabSeal.eopenm ih₁ ih₂ hd
  | emstruct hsb hop _ ih => exact elabSeal.emstruct hsb hop ih
  | emfunctor hsb hop hdop _ ih => exact elabSeal.emfunctor hsb hop hdop ih
  | emclos hv _ _ hd ih₁ ih₂ => exact elabSeal.emclos hv ih₁ ih₂ hd
  | emapp _ _ ih₁ ih₂ => exact elabSeal.emapp ih₁ ih₂
  | emlink _ _ hl hd₁ hd₂ ih₁ ih₂ => exact elabSeal.emlink ih₁ ih₂ hl hd₁ hd₂
  | emlinkn _ _ hw hd₁ hd₂ ih₁ ih₂ => exact elabSeal.emlinkn ih₁ ih₂ hw hd₁ hd₂
  | ewrap hΔ hv _ ih => exact elabSeal.ewrap (hle _ _ hΔ) hv ih
  | emseal hΔ hnr hwf _ ih => exact elabSeal.emseal (hle _ _ hΔ) hnr hwf ih
  | emunseal hΔ hnr hwf _ heq ih => exact elabSeal.emunseal (hle _ _ hΔ) hnr hwf ih heq
  | einl _ ih => exact elabSeal.einl ih
  | einr _ ih => exact elabSeal.einr ih
  | ecase _ _ _ hd₁ hd₂ ih ih₁ ih₂ => exact elabSeal.ecase ih ih₁ ih₂ hd₁ hd₂
  | eflam _ hd₁ hd₂ ih => exact elabSeal.eflam ih hd₁ hd₂
  | efclos hv _ _ hd₁ hd₂ ih₁ ih₂ => exact elabSeal.efclos hv ih₁ ih₂ hd₁ hd₂
  | efold _ ih => exact elabSeal.efold ih
  | eunfold _ heq ih => exact elabSeal.eunfold ih heq

-- ── Type preservation: elaborated code is well-typed λE^≤ ────────────────────────────

theorem seal_type_preservation {Γ : SCE.Typ} {es : SCE.Exp} {A : SCE.Typ} {ce : Seal.Exp}
    (h : elabSeal Δ Γ es A ce)
    : Seal.HasType (sealStore Δ) (sealTyp Γ) ce (sealTyp A) := by
  induction h with
  | equery => exact HasType.tquery
  | elit _ _ => exact HasType.tint
  | eunit _ => exact HasType.tunit
  | eapp _ _ ih₁ ih₂ => exact HasType.tapp ih₁ ih₂
  | eproj _ hl ih => exact HasType.tproj ih (slookup_seal hl)
  | ebox _ _ ih₁ ih₂ => exact HasType.tbox ih₁ ih₂
  | edmrg _ _ hd₁ hd₂ ih₁ ih₂ => exact HasType.tmrg ih₁ ih₂ hd₁ hd₂
  | evmrg hv₁ hv₂ h₁ h₂ hd ih₁ ih₂ =>
    exact HasType.tmergev (elabSeal_value h₁ hv₁) (elabSeal_value h₂ hv₂) ih₁ ih₂ hd
      (disjoint_consistent (elabSeal_value h₁ hv₁) (elabSeal_value h₂ hv₂) ih₁ ih₂ hd)
  | enmrg _ _ hd₁ hd₂ ih₁ ih₂ =>
    exact HasType.tmrg ih₁
      (HasType.tbox (HasType.tanno HasType.tquery (Sub.sandl (sub_refl _))) ih₂)
      hd₁ hd₂
  | elam _ hd ih => exact HasType.tlam hd ih
  | erproj _ hl ih => exact HasType.trproj ih (srlookup_seal hl)
  | eclos hv _ _ hd ih₁ ih₂ =>
    exact HasType.tclos (elabSeal_value (by assumption) hv) ih₁ hd ih₂
      (sub_refl _) (sub_refl _)
  | elrec _ ih => exact HasType.trcd ih
  | eletb _ _ hd ih₁ ih₂ => exact HasType.tapp (HasType.tlam hd ih₂) ih₁
  | eopenm _ _ hd ih₁ ih₂ =>
    exact HasType.tapp (HasType.tlam hd ih₂)
      (HasType.trproj ih₁ RLookup.zero)
  | @emstruct ctx ctxInner B sb se ce hsb hop _ ih =>
    cases sb with
    | sandboxed =>
      rw [hsb rfl] at ih
      exact HasType.tbox HasType.tunit ih
    | open_ =>
      rw [hop rfl] at ih
      exact HasType.tbox HasType.tquery ih
  | @emfunctor ctx ctxInner A B sb se ce hsb hop hdop _ ih =>
    cases sb with
    | sandboxed =>
      rw [hsb rfl] at ih
      exact HasType.tbox HasType.tunit (HasType.tlam disj_top ih)
    | open_ =>
      rw [hop rfl] at ih
      exact HasType.tlam (hdop rfl) ih
  | emclos hv _ _ hd ih₁ ih₂ =>
    exact HasType.tclos (elabSeal_value (by assumption) hv) ih₁ hd ih₂
      (sub_refl _) (sub_refl _)
  | emapp _ _ ih₁ ih₂ => exact HasType.tapp ih₁ ih₂
  | emlink _ _ hl hd₁ hd₂ ih₁ ih₂ =>
    exact HasType.tmrg ih₁
      (HasType.tbox (HasType.tanno HasType.tquery (Sub.sandl (sub_refl _)))
        (HasType.tapp ih₂ (HasType.trcd (HasType.trproj ih₁ (srlookup_seal hl)))))
      hd₁ hd₂
  | emlinkn _ _ hw hd₁ hd₂ ih₁ ih₂ =>
    exact HasType.tmrg ih₁
      (HasType.tbox (HasType.tanno HasType.tquery (Sub.sandl (sub_refl _)))
        (HasType.tapp ih₂ (wireArgSeal_typed hw ih₁)))
      hd₁ hd₂
  | ewrap hΔ hv h ih =>
    exact HasType.twrap (sealStore_some hΔ) (sealTyp_no_hasbvar _) (elabSeal_value h hv) ih
  | emseal hΔ hnr hwf _ ih =>
    rw [sealTyp_substBrand] at ih
    exact HasType.tseal (sealStore_some hΔ) hnr (sealTyp_no_hasbvar _) hwf ih
  | emunseal hΔ hnr hwf _ heq ih =>
    subst heq
    exact HasType.tunseal (sealStore_some hΔ) hnr (sealTyp_no_hasbvar _) hwf ih
      (sealTyp_substBrand _ _ _)
  | einl _ ih =>
    exact HasType.tinl ih
  | einr _ ih =>
    exact HasType.tinr ih
  | ecase _ _ _ hd₁ hd₂ ih ih₁ ih₂ =>
    exact HasType.tcase ih hd₁ hd₂ ih₁ ih₂
  | eflam _ hd₁ hd₂ ih =>
    exact HasType.tflam hd₁ hd₂ ih
  | efclos hv h₁ _ hd₁ hd₂ ih₁ ih₂ =>
    exact HasType.tfclos (elabSeal_value h₁ hv) ih₁ hd₁ hd₂ ih₂ (sub_refl _) (sub_refl _)
      (sub_refl _)
  | efold _ ih =>
    rw [sealTyp_substTyp] at ih
    exact HasType.tfold (sealTyp_no_allbin _) ih
  | eunfold _ heq ih =>
    subst heq
    rw [sealTyp_substTyp]
    exact HasType.tunfold (sealTyp_no_allbin _) ih rfl

-- ── Value elaborations are context-irrelevant ────────────────────────────────────────

-- Mirror of SCE's elab_value_weaken; the edmrg case re-elaborates through the
-- context-free evmrg.
theorem elabSeal_weaken {Γ A : SCE.Typ} {v : SCE.Exp} {ce : Seal.Exp}
    (helab : elabSeal Δ Γ v A ce) (hv : SCE.Value v)
    : ∀ Γ', elabSeal Δ Γ' v A ce := by
  induction helab with
  | equery => nomatch hv
  | elit _ n => intro Γ'; exact elabSeal.elit Γ' n
  | eunit _ => intro Γ'; exact elabSeal.eunit Γ'
  | eapp _ _ _ _ => nomatch hv
  | eproj _ _ _ => nomatch hv
  | ebox _ _ _ _ => nomatch hv
  | edmrg _ _ _ hd₂ ih₁ ih₂ =>
    intro Γ'
    cases hv with
    | vmrg hv₁ hv₂ => exact elabSeal.evmrg hv₁ hv₂ (ih₁ hv₁ .top) (ih₂ hv₂ .top) hd₂
  | evmrg hv₁ hv₂ h₁ h₂ hd _ _ =>
    intro Γ'
    exact elabSeal.evmrg hv₁ hv₂ h₁ h₂ hd
  | enmrg _ _ _ _ _ _ => nomatch hv
  | elam _ _ _ => nomatch hv
  | erproj _ _ _ => nomatch hv
  | eclos hval h₁ h₂ hd _ _ =>
    intro Γ'
    exact elabSeal.eclos hval h₁ h₂ hd
  | elrec _ ih =>
    intro Γ'
    cases hv with
    | vlrec hv' => exact elabSeal.elrec (ih hv' Γ')
  | eletb _ _ _ _ _ => nomatch hv
  | eopenm _ _ _ _ _ => nomatch hv
  | emstruct _ _ _ _ => nomatch hv
  | emfunctor _ _ _ _ _ => nomatch hv
  | emclos hval h₁ h₂ hd _ _ =>
    intro Γ'
    exact elabSeal.emclos hval h₁ h₂ hd
  | emapp _ _ _ _ => nomatch hv
  | emlink _ _ _ _ _ _ _ => nomatch hv
  | emlinkn _ _ _ _ _ _ _ => nomatch hv
  | ewrap hΔ hv' h _ =>
    intro Γ'
    exact elabSeal.ewrap hΔ hv' h
  | emseal _ _ _ _ _ => nomatch hv
  | emunseal _ _ _ _ _ _ => nomatch hv
  | einl _ ih =>
    intro Γ'
    cases hv with
    | vinl hv' => exact elabSeal.einl (ih hv' Γ')
  | einr _ ih =>
    intro Γ'
    cases hv with
    | vinr hv' => exact elabSeal.einr (ih hv' Γ')
  | ecase _ _ _ _ _ _ _ _ => nomatch hv
  | eflam _ _ _ _ => nomatch hv
  | efclos hval h₁ h₂ hd₁ hd₂ _ _ =>
    intro Γ'
    exact elabSeal.efclos hval h₁ h₂ hd₁ hd₂
  | efold _ ih =>
    intro Γ'
    cases hv with
    | vfold hv' => exact elabSeal.efold (ih hv' Γ')
  | eunfold _ _ _ => nomatch hv

-- ── Source-side selection lemmas on elaboration witnesses ────────────────────────────

-- No value elaborates at a bare interface type.
theorem value_elab_sig_intf {Γ : SCE.Typ} {v : SCE.Exp} {T : SCE.Typ} {w : Seal.Exp}
    (h : elabSeal Δ Γ v (.sig (.TyIntf T)) w) (hv : SCE.Value v) : False := by
  cases h <;> nomatch hv

theorem elabSeal_lookup_pres {A B : SCE.Typ} {n : Nat} (hl : SCE.SLookup A n B)
    : ∀ {Γ : SCE.Typ} {v v' : SCE.Exp} {ce : Seal.Exp}, elabSeal Δ Γ v A ce → SCE.Value v
    → S_Sem.LookupV v n v' → ∃ w, elabSeal Δ .top v' B w := by
  induction hl with
  | zero A B =>
    intro Γ v v' ce helab hv hlv
    cases hlv with
    | dmrg_zero =>
      cases helab with
      | edmrg _ h₂ _ _ =>
        cases hv with
        | vmrg _ hv₂ => exact ⟨_, elabSeal_weaken h₂ hv₂ .top⟩
      | evmrg _ _ _ h₂ _ => exact ⟨_, h₂⟩
    | nmrg_zero => nomatch hv
  | succ A B n C _ ih =>
    intro Γ v v' ce helab hv hlv
    cases hlv with
    | dmrg_succ hlv' =>
      cases helab with
      | edmrg h₁ _ _ _ =>
        cases hv with
        | vmrg hv₁ _ => exact ih h₁ hv₁ hlv'
      | evmrg hv₁ _ h₁ _ _ => exact ih h₁ hv₁ hlv'
    | nmrg_succ _ => nomatch hv

theorem elabSeal_sel_absent {v v' : SCE.Exp} {l : String} (hsel : S_Sem.Sel v l v')
    : ∀ {Γ B : SCE.Typ} {ce : Seal.Exp}, elabSeal Δ Γ v B ce → SCE.Value v
    → ¬ SCE.LabelIn l B → False := by
  induction hsel with
  | rcd =>
    intro Γ B ce helab hv hnl
    cases helab with
    | elrec _ => exact hnl (SCE.LabelIn.rcd _ _)
  | dmrg_left _ ih =>
    intro Γ B ce helab hv hnl
    cases helab with
    | edmrg h₁ _ _ _ =>
      cases hv with
      | vmrg hv₁ _ => exact ih h₁ hv₁ (fun hli => hnl (SCE.LabelIn.andl _ _ _ hli))
    | evmrg hv₁ _ h₁ _ _ => exact ih h₁ hv₁ (fun hli => hnl (SCE.LabelIn.andl _ _ _ hli))
  | dmrg_right _ ih =>
    intro Γ B ce helab hv hnl
    cases helab with
    | edmrg _ h₂ _ _ =>
      cases hv with
      | vmrg _ hv₂ => exact ih h₂ hv₂ (fun hli => hnl (SCE.LabelIn.andr _ _ _ hli))
    | evmrg _ hv₂ _ h₂ _ => exact ih h₂ hv₂ (fun hli => hnl (SCE.LabelIn.andr _ _ _ hli))
  | nmrg_left _ _ =>
    intro Γ B ce _ hv _
    nomatch hv
  | nmrg_right _ _ =>
    intro Γ B ce _ hv _
    nomatch hv

theorem elabSeal_sel_pres {B : SCE.Typ} {l : String} {A : SCE.Typ}
    (hl : SCE.SRLookup B l A)
    : ∀ {Γ : SCE.Typ} {v v' : SCE.Exp} {ce : Seal.Exp}, elabSeal Δ Γ v B ce → SCE.Value v
    → S_Sem.Sel v l v' → ∃ w, elabSeal Δ .top v' A w := by
  induction hl with
  | zero label T =>
    intro Γ v v' ce helab hv hsel
    cases hsel with
    | rcd =>
      cases helab with
      | elrec h =>
        cases hv with
        | vlrec hv' => exact ⟨_, elabSeal_weaken h hv' .top⟩
    | dmrg_left _ => nomatch helab
    | dmrg_right _ => nomatch helab
    | nmrg_left _ => nomatch hv
    | nmrg_right _ => nomatch hv
  | andl A' B' label T hl' hnl ih =>
    intro Γ v v' ce helab hv hsel
    cases hsel with
    | rcd =>
      cases helab
    | dmrg_left hsel' =>
      cases helab with
      | edmrg h₁ _ _ _ =>
        cases hv with
        | vmrg hv₁ _ => exact ih h₁ hv₁ hsel'
      | evmrg hv₁ _ h₁ _ _ => exact ih h₁ hv₁ hsel'
    | dmrg_right hsel' =>
      cases helab with
      | edmrg _ h₂ _ _ =>
        cases hv with
        | vmrg _ hv₂ => exact (elabSeal_sel_absent hsel' h₂ hv₂ hnl).elim
      | evmrg _ hv₂ _ h₂ _ => exact (elabSeal_sel_absent hsel' h₂ hv₂ hnl).elim
    | nmrg_left _ => nomatch hv
    | nmrg_right _ => nomatch hv
  | andr A' B' label T hl' hnl ih =>
    intro Γ v v' ce helab hv hsel
    cases hsel with
    | rcd =>
      cases helab
    | dmrg_right hsel' =>
      cases helab with
      | edmrg _ h₂ _ _ =>
        cases hv with
        | vmrg _ hv₂ => exact ih h₂ hv₂ hsel'
      | evmrg _ hv₂ _ h₂ _ => exact ih h₂ hv₂ hsel'
    | dmrg_left hsel' =>
      cases helab with
      | edmrg h₁ _ _ _ =>
        cases hv with
        | vmrg hv₁ _ => exact (elabSeal_sel_absent hsel' h₁ hv₁ hnl).elim
      | evmrg hv₁ _ h₁ _ _ => exact (elabSeal_sel_absent hsel' h₁ hv₁ hnl).elim
    | nmrg_left _ => nomatch hv
    | nmrg_right _ => nomatch hv
  | sig label T A' _ _ =>
    intro Γ v v' ce helab hv hsel
    exact (value_elab_sig_intf helab hv).elim

end Seal
