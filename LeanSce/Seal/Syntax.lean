-- λE^≤ (Seal): λE's de Bruijn binding discipline + Eᵢ's subtyping and restriction.
-- Paper fragment Int | ε | A → B | A & B | {l : A}, plus abstract type names (brands) for
-- module sealing with type abstraction.  See LeanSce/Seal/DESIGN.md.
namespace Seal

-- `brand n` is an abstract type name α_n.  Brands are statically allocated (one per
-- sealed compilation unit / seal occurrence); their representations live in a private
-- brand store `BrandStore` that only the sealing unit's typing derivation consults.  To
-- everyone else a brand is an opaque ordinary type: it is a subtype only of itself and ε,
-- disjoint from every type in which it does not occur, and casting at it is the identity
-- on values already wrapped at that brand.
inductive Typ where
  | int   : Typ
  | top   : Typ
  | arr   : Typ → Typ → Typ
  | and   : Typ → Typ → Typ
  | rcd   : String → Typ → Typ
  | brand : Nat → Typ
  -- Unions.  Subtyping is component-wise only (no injection subtyping A <: A∨B): union
  -- values are always explicitly tagged, so casting can follow the tag deterministically
  -- and COST extends without touching the arrow/record story.
  | or    : Typ → Typ → Typ
  -- Iso-recursive types.  De Bruijn: var 0 is bound by the nearest mu.  Under sealing a
  -- μ-type is OPAQUE, exactly like a brand: subtyping at μ is reflexive only, casting is
  -- the identity on same-body folds, and signatures may mention μ only brand-free.
  -- (Amber-style width/depth subtyping under μ is future work.)
  | var   : Nat → Typ
  | mu    : Typ → Typ
  -- Brand polymorphism.  `bvar i` is a brand VARIABLE (de Bruijn, bound by the nearest
  -- `allb`) — a namespace separate from both `var` (μ) and `brand` (concrete names).
  -- Instantiation substitutes a CLOSED `brand n`, so no shifting is ever needed (the
  -- `var`/μ trick).  `allb A` is ∀β. A.
  | bvar  : Nat → Typ
  | allb  : Typ → Typ
  deriving Repr

-- The private brand store: `Δ n = some R` means the sealing unit knows α_n ≈ R.  Clients
-- are typed with `Δ n = none`.
def BrandStore := Nat → Option Typ

def noBrands : BrandStore := fun _ => none

-- `substBrand n R S` replaces `brand n` by `R` in `S` (types have no binders, so this is
-- plain structural recursion).  `S[n := R]` is the *representation view* of the signature
-- `S`; `seal`/`unseal` coerce between the two views.
def substBrand (n : Nat) (R : Typ) : Typ → Typ
  | .int       => .int
  | .top       => .top
  | .arr A B   => .arr (substBrand n R A) (substBrand n R B)
  | .and A B   => .and (substBrand n R A) (substBrand n R B)
  | .rcd l A   => .rcd l (substBrand n R A)
  | .brand m   => if m = n then R else .brand m
  | .or A B    => .or (substBrand n R A) (substBrand n R B)
  -- Brands and μ's de Bruijn variables live in separate namespaces: no capture.
  | .var m     => .var m
  | .mu T      => .mu (substBrand n R T)
  -- Brand variables are a third namespace: substBrand replaces only concrete brands.
  | .bvar i    => .bvar i
  | .allb A    => .allb (substBrand n R A)

-- `substTyp d S T` replaces var d by S in T (S is closed, so no shifting) — the
-- μ-unfolding substitution.
def substTyp (d : Nat) (S : Typ) : Typ → Typ
  | .int       => .int
  | .top       => .top
  | .arr A B   => .arr (substTyp d S A) (substTyp d S B)
  | .and A B   => .and (substTyp d S A) (substTyp d S B)
  | .rcd l A   => .rcd l (substTyp d S A)
  | .brand m   => .brand m
  | .or A B    => .or (substTyp d S A) (substTyp d S B)
  | .var m     => if m = d then S else .var m
  | .mu T      => .mu (substTyp (d + 1) S T)
  -- μ-vars and brand variables never interact: allb binds bvars, not vars — no bump.
  | .bvar i    => .bvar i
  | .allb A    => .allb (substTyp d S A)

-- `bsubst d n T` replaces the brand variable `bvar d` by the CONCRETE `brand n` in `T` —
-- the ∀β-instantiation substitution.  The substitutend is closed, so no shifting (the
-- substTyp/μ trick); `d` bumps only under `allb` (μ binds `var`, not bvars).
def bsubst (d n : Nat) : Typ → Typ
  | .int       => .int
  | .top       => .top
  | .arr A B   => .arr (bsubst d n A) (bsubst d n B)
  | .and A B   => .and (bsubst d n A) (bsubst d n B)
  | .rcd l A   => .rcd l (bsubst d n A)
  | .brand m   => .brand m
  | .or A B    => .or (bsubst d n A) (bsubst d n B)
  | .var m     => .var m
  | .mu T      => .mu (bsubst d n T)
  | .bvar i    => if i = d then .brand n else .bvar i
  | .allb A    => .allb (bsubst (d + 1) n A)

-- `AllbIn T`: a ∀-type occurs somewhere in `T`.  Its negation fences the μ typing rules:
-- the μ-unfolding substTyp does not shift brand variables, so inserting a μ-type under a
-- ∀ INSIDE the μ-body would capture cross-binder bvars and break the ∀β-instantiation
-- lemma.  μ-bodies OVER an outer β (no ∀ inside) remain fully allowed.
inductive AllbIn : Typ → Prop where
  | self {A}      : AllbIn (.allb A)
  | arrl {A B}    : AllbIn A → AllbIn (.arr A B)
  | arrr {A B}    : AllbIn B → AllbIn (.arr A B)
  | andl {A B}    : AllbIn A → AllbIn (.and A B)
  | andr {A B}    : AllbIn B → AllbIn (.and A B)
  | rcd {l A}     : AllbIn A → AllbIn (.rcd l A)
  | orl {A B}     : AllbIn A → AllbIn (.or A B)
  | orr {A B}     : AllbIn B → AllbIn (.or A B)
  | mu {T}        : AllbIn T → AllbIn (.mu T)

-- `HasBVar T`: some brand variable occurs in `T` (ANY index — index-blind on purpose:
-- it feeds the conservative COST rules and the bsubst-invariance side conditions, both
-- of which quantify over every possible instantiation depth).
inductive HasBVar : Typ → Prop where
  | bvar {i}      : HasBVar (.bvar i)
  | arrl {A B}    : HasBVar A → HasBVar (.arr A B)
  | arrr {A B}    : HasBVar B → HasBVar (.arr A B)
  | andl {A B}    : HasBVar A → HasBVar (.and A B)
  | andr {A B}    : HasBVar B → HasBVar (.and A B)
  | rcd {l A}     : HasBVar A → HasBVar (.rcd l A)
  | orl {A B}     : HasBVar A → HasBVar (.or A B)
  | orr {A B}     : HasBVar B → HasBVar (.or A B)
  | mu {T}        : HasBVar T → HasBVar (.mu T)
  | allb {A}      : HasBVar A → HasBVar (.allb A)

-- Expressions.  Deviation from λE (forced, see DESIGN.md (f)): lambdas and closures carry
-- the codomain annotation, because Casting-arrow must check and rewrite it and beta must
-- reseal the result.  `anno e A` is the value-level sealing primitive `(e : A)`, ported
-- from Eᵢ (hides width and depth).
--
-- Type abstraction adds three forms:
--   `wrap n v`         — a value branded at α_n (runtime form; the only inhabitants of a brand);
--   `seal n R S e`     — coerce `e : S[n:=R]` to `S`, wrapping at every positive α_n position
--                        (proxying arrows); "sealing = casting + branding";
--   `unseal n R S e`   — the converse coercion `S ⇒ S[n:=R]`, used inside the proxies that
--                        `seal` builds at arrow types.
-- Only a unit whose brand store knows α_n ≈ R can type `seal`/`unseal`/`wrap` at n.
inductive Exp where
  | query  : Exp
  | proj   : Exp → Nat → Exp
  | lit    : Nat → Exp
  | unit   : Exp
  | lam    : Typ → Typ → Exp → Exp
  | box    : Exp → Exp → Exp
  | clos   : Exp → Typ → Typ → Exp → Exp
  | app    : Exp → Exp → Exp
  | mrg    : Exp → Exp → Exp
  | lrec   : String → Exp → Exp
  | rproj  : Exp → String → Exp
  | anno   : Exp → Typ → Exp
  | wrap   : Nat → Exp → Exp
  | seal   : Nat → Typ → Typ → Exp → Exp
  | unseal : Nat → Typ → Typ → Exp → Exp
  -- Unions: inl B e injects into _ ∨ B, inr A e into A ∨ _.
  | inl    : Typ → Exp → Exp
  | inr    : Typ → Exp → Exp
  | case   : Exp → Exp → Exp → Exp
  -- Iso-recursive types: fold T e stores the mu-body T, folds into mu T.
  | fold   : Typ → Exp → Exp
  | unfold : Exp → Exp
  -- Fixpoints (Eᵢ App. B, adapted to environment semantics): `flam A B e` is a recursive
  -- function of type A → B whose body sees ?.0 = argument, ?.1 = the function itself.
  -- `fclos v A B Bx e` is its closure.  It carries TWO codomains: the *internal* B is what
  -- the body and the self-reference in beta see and is never rewritten; the *external* Bx
  -- is the client-facing codomain, rewritten by casts exactly as a clos's codomain is.
  -- One annotation cannot serve both: casting must be able to widen the visible codomain
  -- (cast_progress along S-arr), but the body was typed with (A → B) in its context, and
  -- there is no subsumption to absorb a widened self-entry.
  | flam   : Typ → Typ → Exp → Exp
  | fclos  : Exp → Typ → Typ → Typ → Exp → Exp
  -- Brand polymorphism: `blam A e` abstracts over a brand (∀β-introduction; steps to
  -- `bclos ρ A e`, capturing the ambient environment — the lam→clos pattern), and
  -- `bapp e n` instantiates at the concrete brand n.  The ∀-body annotation A is
  -- carried on the closure for the same reason fold carries its μ-body: casting at a
  -- ∀-type is an identity that the VALUE must pin (cast_preservation's cbclos case).
  | blam   : Typ → Exp → Exp
  | bclos  : Exp → Typ → Exp → Exp
  | bapp   : Exp → Nat → Exp
  deriving Repr

-- `bsubstExp d n e` pushes the ∀β-instantiation into every type annotation of `e`,
-- bumping `d` under `blam`/`bclos` (their bodies sit under one more brand binder).
def bsubstExp (d n : Nat) : Exp → Exp
  | .query        => .query
  | .proj e k     => .proj (bsubstExp d n e) k
  | .lit k        => .lit k
  | .unit         => .unit
  | .lam A B e    => .lam (bsubst d n A) (bsubst d n B) (bsubstExp d n e)
  | .box e₁ e₂    => .box (bsubstExp d n e₁) (bsubstExp d n e₂)
  | .clos v A B e => .clos (bsubstExp d n v) (bsubst d n A) (bsubst d n B) (bsubstExp d n e)
  | .app e₁ e₂    => .app (bsubstExp d n e₁) (bsubstExp d n e₂)
  | .mrg e₁ e₂    => .mrg (bsubstExp d n e₁) (bsubstExp d n e₂)
  | .lrec l e     => .lrec l (bsubstExp d n e)
  | .rproj e l    => .rproj (bsubstExp d n e) l
  | .anno e A     => .anno (bsubstExp d n e) (bsubst d n A)
  | .wrap m v     => .wrap m (bsubstExp d n v)
  | .seal m R S e   => .seal m (bsubst d n R) (bsubst d n S) (bsubstExp d n e)
  | .unseal m R S e => .unseal m (bsubst d n R) (bsubst d n S) (bsubstExp d n e)
  | .inl B e      => .inl (bsubst d n B) (bsubstExp d n e)
  | .inr A e      => .inr (bsubst d n A) (bsubstExp d n e)
  | .case e e₁ e₂ => .case (bsubstExp d n e) (bsubstExp d n e₁) (bsubstExp d n e₂)
  | .fold T e     => .fold (bsubst d n T) (bsubstExp d n e)
  | .unfold e     => .unfold (bsubstExp d n e)
  | .flam A B e   => .flam (bsubst d n A) (bsubst d n B) (bsubstExp d n e)
  | .fclos v A B Bx e =>
    .fclos (bsubstExp d n v) (bsubst d n A) (bsubst d n B) (bsubst d n Bx) (bsubstExp d n e)
  | .blam A e     => .blam (bsubst (d + 1) n A) (bsubstExp (d + 1) n e)
  -- The captured environment was the AMBIENT value at capture time — it sits outside
  -- the binder, so it substitutes at d; the annotation and body are one binder deeper.
  | .bclos ρ A e  => .bclos (bsubstExp d n ρ) (bsubst (d + 1) n A) (bsubstExp (d + 1) n e)
  | .bapp e m     => .bapp (bsubstExp d n e) m

inductive Value : Exp → Prop where
  | vint  {n}       : Value (.lit n)
  | vunit           : Value .unit
  | vclos {v A B e} : Value v → Value (.clos v A B e)
  | vrcd  {v l}     : Value v → Value (.lrec l v)
  | vmrg  {v₁ v₂}   : Value v₁ → Value v₂ → Value (.mrg v₁ v₂)
  | vwrap {n v}     : Value v → Value (.wrap n v)
  | vinl  {v B}     : Value v → Value (.inl B v)
  | vinr  {v A}     : Value v → Value (.inr A v)
  | vfold {v T}     : Value v → Value (.fold T v)
  | vfclos {v A B Bx e} : Value v → Value (.fclos v A B Bx e)
  | vbclos {ρ A e}  : Value ρ → Value (.bclos ρ A e)

theorem value_clos_env {v : Exp} {A B : Typ} {e : Exp} (h : Value (.clos v A B e))
    : Value v := by cases h with | vclos h' => exact h'

theorem value_fclos_env {v : Exp} {A B Bx : Typ} {e : Exp} (h : Value (.fclos v A B Bx e))
    : Value v := by cases h with | vfclos h' => exact h'

theorem value_bclos_env {ρ e : Exp} {A : Typ} (h : Value (.bclos ρ A e)) : Value ρ := by
  cases h with | vbclos h' => exact h'

theorem value_inl_payload {v : Exp} {B : Typ} (h : Value (.inl B v)) : Value v := by
  cases h with | vinl h' => exact h'

theorem value_inr_payload {v : Exp} {A : Typ} (h : Value (.inr A v)) : Value v := by
  cases h with | vinr h' => exact h'

theorem value_fold_payload {v : Exp} {T : Typ} (h : Value (.fold T v)) : Value v := by
  cases h with | vfold h' => exact h'

-- Positional lookup on types (λE, unchanged): index 0 is the rightmost component.
inductive Lookup : Typ → Nat → Typ → Prop where
  | zero {A B}
    : Lookup (.and A B) 0 B
  | succ {A B n C}
    : Lookup A n C
    → Lookup (.and A B) (n+1) C

-- Positional lookup on value environments (λE, unchanged).
inductive LookupV : Exp → Nat → Exp → Prop where
  | lvzero {v₁ v₂ : Exp}
    : LookupV (.mrg v₁ v₂) 0 v₂
  | lvsucc {v₁ v₂ v₃ : Exp} {n : Nat}
    : LookupV v₁ n v₃
    → LookupV (.mrg v₁ v₂) (n + 1) v₃

-- l occurs in A (λE's label membership, used for the containment side conditions).
inductive Lin : String → Typ → Prop where
  | rcd {l A}
    : Lin l (.rcd l A)
  | andl {l A B}
    : Lin l A
    → Lin l (.and A B)
  | andr {l B A}
    : Lin l B
    → Lin l (.and A B)

-- λE's containment judgment l : A ∈ B — the negative premises rule out ambiguous labels.
inductive RLookup : Typ → String → Typ → Prop where
  | zero {l A}
    : RLookup (.rcd l A) l A
  | landl {A l C B}
    : RLookup A l C
    → ¬Lin l B
    → RLookup (.and A B) l C
  | landr {B l C A}
    : RLookup B l C
    → ¬Lin l A
    → RLookup (.and A B) l C

theorem rlookup_lin {A : Typ} {l : String} {C : Typ} : RLookup A l C → Lin l A := by
  intro h
  induction h with
  | zero => exact Lin.rcd
  | landl _ _ ih => exact Lin.andl ih
  | landr _ _ ih => exact Lin.andr ih

-- Value-level selection (λE sel-mrgl/sel-mrgr): nondeterministic as a relation, tamed by
-- typing through containment (see Determinism.lean).
inductive RLookupV : Exp → String → Exp → Prop where
  | rvlzero {l : String} {e : Exp}
    : RLookupV (.lrec l e) l e
  | vlandl {e₁ e₂ e : Exp} {l : String}
    : RLookupV e₁ l e
    → RLookupV (.mrg e₁ e₂) l e
  | vlandr {e₁ e₂ e : Exp} {l : String}
    : RLookupV e₂ l e
    → RLookupV (.mrg e₁ e₂) l e

-- Ordinary types, casting variant (Eᵢ): not ε and not an intersection.  Brands are
-- ordinary: casting selects them out of merges like any other leaf type.
inductive Ordinary : Typ → Prop where
  | oint         : Ordinary .int
  | oarr {A B}   : Ordinary (.arr A B)
  | orcd {l A}   : Ordinary (.rcd l A)
  | obrand {n}   : Ordinary (.brand n)
  | oor {A B}    : Ordinary (.or A B)
  | ovar {n}     : Ordinary (.var n)
  | omu {T}      : Ordinary (.mu T)
  | obvar {i}    : Ordinary (.bvar i)
  | oallb {A}    : Ordinary (.allb A)

-- Top-like types ⌉A⌈ (Eᵢ, with ε playing Top).
inductive TopLike : Typ → Prop where
  | tltop        : TopLike .top
  | tland {A B}  : TopLike A → TopLike B → TopLike (.and A B)
  | tlarr {A B}  : TopLike B → TopLike (.arr A B)
  | tlrcd {l B}  : TopLike B → TopLike (.rcd l B)

-- Value generator A↑ (Eᵢ Definition 23), total with junk at Int and at brands: every lemma
-- about genVal is guarded by TopLike A, so the junk values are never observable.
def genVal : Typ → Exp
  | .int     => .unit
  | .top     => .unit
  | .arr A B => .clos .unit A B (genVal B)
  | .and A B => .mrg (genVal A) (genVal B)
  | .rcd l A => .lrec l (genVal A)
  | .brand _ => .unit
  | .or _ _  => .unit
  | .var _   => .unit
  | .mu _    => .unit
  | .bvar _  => .unit
  | .allb _  => .unit

theorem genVal_value : (A : Typ) → Value (genVal A)
  | .int     => Value.vunit
  | .top     => Value.vunit
  | .arr _ _ => Value.vclos Value.vunit
  | .and A B => Value.vmrg (genVal_value A) (genVal_value B)
  | .rcd _ A => Value.vrcd (genVal_value A)
  | .brand _ => Value.vunit
  | .or _ _  => Value.vunit
  | .var _   => Value.vunit
  | .mu _    => Value.vunit
  | .bvar _  => Value.vunit
  | .allb _  => Value.vunit

-- Top-likeness is decidable (constructively, by inversion at each shape).
theorem toplike_dec : (A : Typ) → TopLike A ∨ ¬ TopLike A
  | .int => Or.inr (fun h => nomatch h)
  | .brand _ => Or.inr (fun h => nomatch h)
  | .or _ _ => Or.inr (fun h => nomatch h)
  | .var _ => Or.inr (fun h => nomatch h)
  | .mu _ => Or.inr (fun h => nomatch h)
  | .bvar _ => Or.inr (fun h => nomatch h)
  | .allb _ => Or.inr (fun h => nomatch h)
  | .top => Or.inl TopLike.tltop
  | .arr _ B =>
    match toplike_dec B with
    | Or.inl h => Or.inl (TopLike.tlarr h)
    | Or.inr h => Or.inr (fun htl => by cases htl with | tlarr hB => exact h hB)
  | .and A B =>
    match toplike_dec A, toplike_dec B with
    | Or.inl hA, Or.inl hB => Or.inl (TopLike.tland hA hB)
    | Or.inr hA, _ => Or.inr (fun htl => by cases htl with | tland h1 _ => exact hA h1)
    | _, Or.inr hB => Or.inr (fun htl => by cases htl with | tland _ h2 => exact hB h2)
  | .rcd l A =>
    match toplike_dec A with
    | Or.inl h => Or.inl (TopLike.tlrcd h)
    | Or.inr h => Or.inr (fun htl => by cases htl with | tlrcd hA => exact h hA)

end Seal
