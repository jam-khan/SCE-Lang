import LeanSce.Seal.Determinism
import LeanSce.Seal.Progress
import LeanSce.Seal.Preservation

-- The sealing theorem for λE^≤: a binary, type-indexed logical relation (the binary
-- generalization of λE Figure 4's semantic typing), its fundamental lemma, the lemma that
-- casting is a coercion between the relations, and the sealing corollary — clients typed
-- against a seal cannot distinguish providers that agree at the seal.  Strong
-- normalization of well-typed λE^≤ programs falls out (no TDOS merge calculus had a
-- mechanized normalization result before; Eᵢ's termination is listed as unknown).
--
-- Type abstraction: the relation is indexed by two brand stores Δ₁ Δ₂ (the two providers
-- may use different representations, so left values type under Δ₁ and right values under
-- Δ₂) and by a brand interpretation η : Nat → Exp → Exp → Prop.  At `brand n` two values
-- are related iff both are wrappers whose payloads are η-related — the standard relational
-- interpretation of an abstract type; η is arbitrary.  The fundamental lemma is stated for
-- *client* typing (`HasType noBrands`, every brand opaque): a client cannot wrap, seal or
-- unseal, and everything else it can do respects η by construction.  Provider-side
-- values enter the relation through the sealing coercion (Abstraction.lean: coe_lr).
namespace Seal

variable {Δ Δ₁ Δ₂ : BrandStore} {η : Nat → Exp → Exp → Prop}

-- ── Brand views ─────────────────────────────────────────────────────────────────────
-- The relation is parametrized by an *open brand* `o`.  With `o = none` every brand is
-- abstract: values at `brand m` are wrappers whose payloads are η-related.  With
-- `o = some (n, R₁, R₂)` brand n is open: values at `brand n` are raw representations
-- (typed at R₁ on the left, R₂ on the right) related by η n, and every type is read
-- through the corresponding substitution.  `LR := LRg none` is the relation clients are
-- reasoned about in; `LRg (some …)` is the relation the *implementations* of a sealed
-- unit stand in before sealing.  The sealing coercion maps one to the other
-- (Abstraction.lean), and `cast_lr` is proved once for both.
abbrev BrandOpen := Option (Nat × Typ × Typ)

def viewL : BrandOpen → Typ → Typ
  | none, T => T
  | some (n, R₁, _), T => substBrand n R₁ T

def viewR : BrandOpen → Typ → Typ
  | none, T => T
  | some (n, _, R₂), T => substBrand n R₂ T

-- Values related at an abstract brand: both wrappers, payloads η-related.
def WrapRel (Δ₁ Δ₂ : BrandStore) (η : Nat → Exp → Exp → Prop) (m : Nat) (v₁ v₂ : Exp) : Prop :=
  HasType Δ₁ .top v₁ (.brand m) ∧ HasType Δ₂ .top v₂ (.brand m) ∧
  ∃ w₁ w₂, v₁ = .wrap m w₁ ∧ v₂ = .wrap m w₂ ∧ η m w₁ w₂

-- Values related at an open brand: raw representations, η-related.
def RawRel (Δ₁ Δ₂ : BrandStore) (η : Nat → Exp → Exp → Prop) (n : Nat) (R₁ R₂ : Typ)
    (v₁ v₂ : Exp) : Prop :=
  Value v₁ ∧ Value v₂ ∧ HasType Δ₁ .top v₁ R₁ ∧ HasType Δ₂ .top v₂ R₂ ∧ η n v₁ v₂

-- δ-environments: the relational interpretation of BRAND VARIABLES (milestone 4
-- prep).  Each entry names the concrete brand both sides instantiated the binder at,
-- and the relation the binder was opened with; index 0 will be the nearest enclosing
-- ∀-binder.  Not yet consumed by LRg — see HANDOFF §3.7 for the open design questions.
abbrev DEnv := Nat → Nat × (Exp → Exp → Prop)

def dbrands (δ : DEnv) : Nat → Nat := fun i => (δ i).1

def demp : DEnv := fun _ => (0, fun _ _ => False)

-- Admissibility of a binder relation: closed under casting at the (viewed) brand —
-- the OpenAdm pattern, one binder at a time.
def RelAdm (o : BrandOpen) (m : Nat) (rel : Exp → Exp → Prop) : Prop :=
  ∀ w₁ w₂, rel w₁ w₂ → ∀ w₁' w₂', Cast w₁ (viewL o (.brand m)) w₁'
    → Cast w₂ (viewR o (.brand m)) w₂' → rel w₁' w₂'

def DeltaAdm (o : BrandOpen) (δ : DEnv) : Prop := ∀ i, RelAdm o (δ i).1 (δ i).2

theorem deltaAdm_demp {o : BrandOpen} : DeltaAdm o demp := fun _ _ _ h => h.elim

theorem deltaAdm_insert {o : BrandOpen} {δ : DEnv} {m : Nat} {rel : Exp → Exp → Prop}
    (hδ : DeltaAdm o δ) (hrel : RelAdm o m rel) : DeltaAdm o (bvInsert 0 (m, rel) δ) := by
  intro i
  cases i with
  | zero => exact hrel
  | succ i => exact hδ i

-- The relation, by structural recursion on the type.  Every clause that cannot re-derive
-- the values' typing carries it (& needs the consistency baked into the typing; arrows
-- carry their closure typing; brands carry it because the payload's typing lives in the
-- respective store).  The arrow clause is extensional and phrased at the application
-- level with existential runs, over arbitrary value environments: the semantics' internal
-- argument-cast at the closure's annotation input is thereby absorbed.
def LRg (Δ₁ Δ₂ : BrandStore) (η : Nat → Exp → Exp → Prop) (o : BrandOpen)
    : Typ → Exp → Exp → Prop
  | .int, v₁, v₂ => ∃ i, v₁ = .lit i ∧ v₂ = .lit i
  | .top, v₁, v₂ => v₁ = .unit ∧ v₂ = .unit
  | .brand m, v₁, v₂ =>
      match o with
      | some (n, R₁, R₂) =>
          if m = n then RawRel Δ₁ Δ₂ η n R₁ R₂ v₁ v₂ else WrapRel Δ₁ Δ₂ η m v₁ v₂
      | none => WrapRel Δ₁ Δ₂ η m v₁ v₂
  | .and A B, v₁, v₂ =>
      HasType Δ₁ .top v₁ (viewL o (.and A B)) ∧ HasType Δ₂ .top v₂ (viewR o (.and A B)) ∧
      ∃ a₁ b₁ a₂ b₂, v₁ = .mrg a₁ b₁ ∧ v₂ = .mrg a₂ b₂ ∧
        LRg Δ₁ Δ₂ η o A a₁ a₂ ∧ LRg Δ₁ Δ₂ η o B b₁ b₂
  | .rcd l A, v₁, v₂ =>
      ∃ w₁ w₂, v₁ = .lrec l w₁ ∧ v₂ = .lrec l w₂ ∧ LRg Δ₁ Δ₂ η o A w₁ w₂
  | .arr A B, v₁, v₂ =>
      Value v₁ ∧ Value v₂ ∧
      HasType Δ₁ .top v₁ (viewL o (.arr A B)) ∧ HasType Δ₂ .top v₂ (viewR o (.arr A B)) ∧
      ∀ u₁ u₂, LRg Δ₁ Δ₂ η o A u₁ u₂ →
        ∀ ρ₁ ρ₂, Value ρ₁ → Value ρ₂ →
          ∃ w₁ w₂, MStep ρ₁ (.app v₁ u₁) w₁ ∧ MStep ρ₂ (.app v₂ u₂) w₂ ∧
            LRg Δ₁ Δ₂ η o B w₁ w₂
  | .or A B, v₁, v₂ =>
      (∃ w₁ w₂, v₁ = .inl (viewL o B) w₁ ∧ v₂ = .inl (viewR o B) w₂ ∧ LRg Δ₁ Δ₂ η o A w₁ w₂) ∨
      (∃ w₁ w₂, v₁ = .inr (viewL o A) w₁ ∧ v₂ = .inr (viewR o A) w₂ ∧ LRg Δ₁ Δ₂ η o B w₁ w₂)
  -- μ is OPAQUE to the relation (the brand pattern, but with plain equality: the fold
  -- annotation itself pins the body).  Recursing through the unfolding would break the
  -- structural recursion this definition lives by; a step-indexed relation is the
  -- future-work route to a finer clause.  Type variables relate nothing (they never
  -- close-type a value).
  | .var _, _, _ => False
  | .mu T, v₁, v₂ =>
      Value v₁ ∧ Value v₂ ∧
      HasType Δ₁ .top v₁ (viewL o (.mu T)) ∧ HasType Δ₂ .top v₂ (viewR o (.mu T)) ∧ v₁ = v₂
  -- Brand variables never close-type a value (like μ-vars).  ∀ is opaque to the relation
  -- for now, exactly like μ: the real ∀-clause quantifying over η-extensions is the
  -- relational milestone (HANDOFF §3.7, milestone 4).
  | .bvar _, _, _ => False
  | .allb A, v₁, v₂ =>
      Value v₁ ∧ Value v₂ ∧
      HasType Δ₁ .top v₁ (viewL o (.allb A)) ∧ HasType Δ₂ .top v₂ (viewR o (.allb A)) ∧ v₁ = v₂

-- The client-facing relation: every brand abstract.
abbrev LR (Δ₁ Δ₂ : BrandStore) (η : Nat → Exp → Exp → Prop) : Typ → Exp → Exp → Prop :=
  LRg Δ₁ Δ₂ η none

-- What an open brand must satisfy for casting to respect the relation: the
-- representations are not top-like (so top-likeness of a type is the same in the abstract
-- and the representation views), and η n is closed under casting the representations at
-- their own types (self-casts are the identity up to top-like collapse, so this is a mild
-- admissibility condition; it is what beta's argument-cast at a proxy's annotation needs).
def OpenAdm (η : Nat → Exp → Exp → Prop) (o : BrandOpen) : Prop :=
  ∀ n R₁ R₂, o = some (n, R₁, R₂) →
    ¬ TopLike R₁ ∧ ¬ TopLike R₂ ∧
    ∀ w₁ w₂, η n w₁ w₂ → ∀ w₁' w₂', Cast w₁ R₁ w₁' → Cast w₂ R₂ w₂' → η n w₁' w₂'

theorem openadm_none : OpenAdm η none := fun _ _ _ h => nomatch h

-- View lemmas: the views commute with every type former (only brands are affected).
theorem viewL_int {o : BrandOpen} : viewL o .int = .int := by cases o with | none => rfl | some p => rfl
theorem viewR_int {o : BrandOpen} : viewR o .int = .int := by cases o with | none => rfl | some p => rfl
theorem viewL_top {o : BrandOpen} : viewL o .top = .top := by cases o with | none => rfl | some p => rfl
theorem viewR_top {o : BrandOpen} : viewR o .top = .top := by cases o with | none => rfl | some p => rfl
theorem viewL_arr {o : BrandOpen} {A B : Typ} : viewL o (.arr A B) = .arr (viewL o A) (viewL o B) := by
  cases o with | none => rfl | some p => rfl
theorem viewR_arr {o : BrandOpen} {A B : Typ} : viewR o (.arr A B) = .arr (viewR o A) (viewR o B) := by
  cases o with | none => rfl | some p => rfl
theorem viewL_and {o : BrandOpen} {A B : Typ} : viewL o (.and A B) = .and (viewL o A) (viewL o B) := by
  cases o with | none => rfl | some p => rfl
theorem viewR_and {o : BrandOpen} {A B : Typ} : viewR o (.and A B) = .and (viewR o A) (viewR o B) := by
  cases o with | none => rfl | some p => rfl
theorem viewL_rcd {o : BrandOpen} {l : String} {A : Typ} : viewL o (.rcd l A) = .rcd l (viewL o A) := by
  cases o with | none => rfl | some p => rfl
theorem viewR_rcd {o : BrandOpen} {l : String} {A : Typ} : viewR o (.rcd l A) = .rcd l (viewR o A) := by
  cases o with | none => rfl | some p => rfl
theorem viewL_or {o : BrandOpen} {A B : Typ} : viewL o (.or A B) = .or (viewL o A) (viewL o B) := by
  cases o with | none => rfl | some p => rfl
theorem viewR_or {o : BrandOpen} {A B : Typ} : viewR o (.or A B) = .or (viewR o A) (viewR o B) := by
  cases o with | none => rfl | some p => rfl
theorem viewL_mu {o : BrandOpen} {T : Typ} : viewL o (.mu T) = .mu (viewL o T) := by
  cases o with | none => rfl | some p => rfl
theorem viewR_mu {o : BrandOpen} {T : Typ} : viewR o (.mu T) = .mu (viewR o T) := by
  cases o with | none => rfl | some p => rfl
theorem viewL_allb {o : BrandOpen} {A : Typ} : viewL o (.allb A) = .allb (viewL o A) := by
  cases o with | none => rfl | some p => rfl
theorem viewR_allb {o : BrandOpen} {A : Typ} : viewR o (.allb A) = .allb (viewR o A) := by
  cases o with | none => rfl | some p => rfl

-- Substitution preserves subtyping (brands are subtypes only of themselves and ε).
theorem sub_subst {n : Nat} {R : Typ} {A B : Typ} (h : Sub A B)
    : Sub (substBrand n R A) (substBrand n R B) := by
  induction h with
  | sint => exact Sub.sint
  | stop => exact Sub.stop
  | sarr _ _ ih₁ ih₂ => exact Sub.sarr ih₁ ih₂
  | sandl _ ih => exact Sub.sandl ih
  | sandr _ ih => exact Sub.sandr ih
  | sand _ _ ih₁ ih₂ => exact Sub.sand ih₁ ih₂
  | srcd _ ih => exact Sub.srcd ih
  | sbrand => exact sub_refl _
  | sor _ _ ih₁ ih₂ => exact Sub.sor ih₁ ih₂
  | svar => exact sub_refl _
  | smu => exact sub_refl _
  | sbvar => exact sub_refl _
  | sallb => exact sub_refl _

theorem sub_viewL {o : BrandOpen} {A B : Typ} (h : Sub A B) : Sub (viewL o A) (viewL o B) := by
  cases o with
  | none => exact h
  | some p => obtain ⟨n, R₁, R₂⟩ := p; exact sub_subst h

theorem sub_viewR {o : BrandOpen} {A B : Typ} (h : Sub A B) : Sub (viewR o A) (viewR o B) := by
  cases o with
  | none => exact h
  | some p => obtain ⟨n, R₁, R₂⟩ := p; exact sub_subst h

-- Top-likeness under substitution: preserved always; reflected when the representation
-- is not top-like.
theorem toplike_subst {n : Nat} {R : Typ} {A : Typ} (h : TopLike A)
    : TopLike (substBrand n R A) := by
  induction h with
  | tltop => exact TopLike.tltop
  | tland _ _ ih₁ ih₂ => exact TopLike.tland ih₁ ih₂
  | tlarr _ ih => exact TopLike.tlarr ih
  | tlrcd _ ih => exact TopLike.tlrcd ih

theorem toplike_subst_inv {n : Nat} {R : Typ} (hR : ¬ TopLike R) : {A : Typ}
    → TopLike (substBrand n R A) → TopLike A
  | .int, h => nomatch h
  | .top, _ => TopLike.tltop
  | .brand m, h => by
    by_cases hm : m = n
    · simp only [substBrand, hm, if_true] at h; exact absurd h hR
    · simp only [substBrand, hm, if_false] at h; nomatch h
  | .arr A B, h => by
    cases h with | tlarr h' => exact TopLike.tlarr (toplike_subst_inv hR h')
  | .and A B, h => by
    cases h with | tland h₁ h₂ => exact TopLike.tland (toplike_subst_inv hR h₁) (toplike_subst_inv hR h₂)
  | .rcd l A, h => by
    cases h with | tlrcd h' => exact TopLike.tlrcd (toplike_subst_inv hR h')

theorem toplike_viewL {o : BrandOpen} {A : Typ} (h : TopLike A) : TopLike (viewL o A) := by
  cases o with
  | none => exact h
  | some p => obtain ⟨n, R₁, R₂⟩ := p; exact toplike_subst h

theorem toplike_viewR {o : BrandOpen} {A : Typ} (h : TopLike A) : TopLike (viewR o A) := by
  cases o with
  | none => exact h
  | some p => obtain ⟨n, R₁, R₂⟩ := p; exact toplike_subst h

theorem toplike_viewL_inv {o : BrandOpen} (hadm : OpenAdm η o) {A : Typ}
    (h : TopLike (viewL o A)) : TopLike A := by
  cases o with
  | none => exact h
  | some p =>
    obtain ⟨n, R₁, R₂⟩ := p
    exact toplike_subst_inv (hadm n R₁ R₂ rfl).1 h

theorem toplike_viewR_inv {o : BrandOpen} (hadm : OpenAdm η o) {A : Typ}
    (h : TopLike (viewR o A)) : TopLike A := by
  cases o with
  | none => exact h
  | some p =>
    obtain ⟨n, R₁, R₂⟩ := p
    exact toplike_subst_inv (hadm n R₁ R₂ rfl).2.1 h

theorem lr_value {o : BrandOpen} : {T : Typ} → {v₁ v₂ : Exp} → LRg Δ₁ Δ₂ η o T v₁ v₂
    → Value v₁ ∧ Value v₂
  | .int, _, _, ⟨_, h₁, h₂⟩ => by subst h₁; subst h₂; exact ⟨Value.vint, Value.vint⟩
  | .top, _, _, ⟨h₁, h₂⟩ => by subst h₁; subst h₂; exact ⟨Value.vunit, Value.vunit⟩
  | .brand m, v₁, v₂, h => by
    have wrap_val : WrapRel Δ₁ Δ₂ η m v₁ v₂ → Value v₁ ∧ Value v₂ := by
      intro ⟨ht₁, ht₂, _, _, h₁, h₂, _⟩
      subst h₁; subst h₂
      cases ht₁ with | twrap _ _ hv₁ _ =>
      cases ht₂ with | twrap _ _ hv₂ _ =>
      exact ⟨Value.vwrap hv₁, Value.vwrap hv₂⟩
    cases o with
    | none => exact wrap_val h
    | some p =>
      obtain ⟨n, R₁, R₂⟩ := p
      by_cases hm : m = n
      · simp only [LRg, hm, if_true] at h; exact ⟨h.1, h.2.1⟩
      · simp only [LRg, hm, if_false] at h; exact wrap_val h
  | .and A B, _, _, ⟨_, _, a₁, b₁, a₂, b₂, h₁, h₂, hA, hB⟩ => by
    subst h₁; subst h₂
    exact ⟨Value.vmrg (lr_value hA).1 (lr_value hB).1,
           Value.vmrg (lr_value hA).2 (lr_value hB).2⟩
  | .rcd l A, _, _, ⟨w₁, w₂, h₁, h₂, hA⟩ => by
    subst h₁; subst h₂
    exact ⟨Value.vrcd (lr_value hA).1, Value.vrcd (lr_value hA).2⟩
  | .arr A B, _, _, ⟨hv₁, hv₂, _, _, _⟩ => ⟨hv₁, hv₂⟩
  | .or A B, _, _, h => by
    cases h with
    | inl h' =>
      obtain ⟨w₁, w₂, h₁, h₂, hA⟩ := h'
      subst h₁; subst h₂
      exact ⟨Value.vinl (lr_value hA).1, Value.vinl (lr_value hA).2⟩
    | inr h' =>
      obtain ⟨w₁, w₂, h₁, h₂, hB⟩ := h'
      subst h₁; subst h₂
      exact ⟨Value.vinr (lr_value hB).1, Value.vinr (lr_value hB).2⟩
  | .var _, _, _, h => h.elim
  | .mu T, _, _, h => ⟨h.1, h.2.1⟩
  | .bvar _, _, _, h => h.elim
  | .allb _, _, _, h => ⟨h.1, h.2.1⟩

theorem lr_typed {o : BrandOpen} : {T : Typ} → {v₁ v₂ : Exp} → LRg Δ₁ Δ₂ η o T v₁ v₂
    → HasType Δ₁ .top v₁ (viewL o T) ∧ HasType Δ₂ .top v₂ (viewR o T)
  | .int, _, _, ⟨_, h₁, h₂⟩ => by
    subst h₁; subst h₂; rw [viewL_int, viewR_int]; exact ⟨HasType.tint, HasType.tint⟩
  | .top, _, _, ⟨h₁, h₂⟩ => by
    subst h₁; subst h₂; rw [viewL_top, viewR_top]; exact ⟨HasType.tunit, HasType.tunit⟩
  | .brand m, v₁, v₂, h => by
    cases o with
    | none => exact ⟨h.1, h.2.1⟩
    | some p =>
      obtain ⟨n, R₁, R₂⟩ := p
      by_cases hm : m = n
      · simp only [LRg, hm, if_true] at h
        simp only [viewL, viewR, substBrand, hm, if_true]
        exact ⟨h.2.2.1, h.2.2.2.1⟩
      · simp only [LRg, hm, if_false] at h
        simp only [viewL, viewR, substBrand, hm, if_false]
        exact ⟨h.1, h.2.1⟩
  | .and _ _, _, _, ⟨ht₁, ht₂, _⟩ => ⟨ht₁, ht₂⟩
  | .rcd l A, _, _, ⟨w₁, w₂, h₁, h₂, hA⟩ => by
    subst h₁; subst h₂
    rw [viewL_rcd, viewR_rcd]
    exact ⟨HasType.trcd (lr_typed hA).1, HasType.trcd (lr_typed hA).2⟩
  | .arr _ _, _, _, ⟨_, _, ht₁, ht₂, _⟩ => ⟨ht₁, ht₂⟩
  | .or A B, _, _, h => by
    rw [viewL_or, viewR_or]
    cases h with
    | inl h' =>
      obtain ⟨w₁, w₂, h₁, h₂, hA⟩ := h'
      subst h₁; subst h₂
      exact ⟨HasType.tinl (lr_typed hA).1, HasType.tinl (lr_typed hA).2⟩
    | inr h' =>
      obtain ⟨w₁, w₂, h₁, h₂, hB⟩ := h'
      subst h₁; subst h₂
      exact ⟨HasType.tinr (lr_typed hB).1, HasType.tinr (lr_typed hB).2⟩
  | .var _, _, _, h => h.elim
  | .mu T, _, _, h => ⟨h.2.2.1, h.2.2.2.1⟩
  | .bvar _, _, _, h => h.elim
  | .allb _, _, _, h => ⟨h.2.2.1, h.2.2.2.1⟩

-- ── MStep congruence toolkit ─────────────────────────────────────────────────────────

theorem mstep_appl {v e₁ e₁' e₂ : Exp} (hv : Value v) (h : MStep v e₁ e₁')
    : MStep v (.app e₁ e₂) (.app e₁' e₂) := by
  induction h with
  | refl => exact MStep.refl
  | step hs _ ih => exact MStep.step (Step.sappl hv hs) ih

theorem mstep_appr {v v₁ e₂ e₂' : Exp} (hv : Value v) (hv₁ : Value v₁) (h : MStep v e₂ e₂')
    : MStep v (.app v₁ e₂) (.app v₁ e₂') := by
  induction h with
  | refl => exact MStep.refl
  | step hs _ ih => exact MStep.step (Step.sappr hv hv₁ hs) ih

theorem mstep_boxl {v e₁ e₁' e₂ : Exp} (hv : Value v) (h : MStep v e₁ e₁')
    : MStep v (.box e₁ e₂) (.box e₁' e₂) := by
  induction h with
  | refl => exact MStep.refl
  | step hs _ ih => exact MStep.step (Step.sboxl hv hs) ih

theorem mstep_boxr {v v₁ e₂ e₂' : Exp} (hv : Value v) (hv₁ : Value v₁) (h : MStep v₁ e₂ e₂')
    : MStep v (.box v₁ e₂) (.box v₁ e₂') := by
  induction h with
  | refl => exact MStep.refl
  | step hs _ ih => exact MStep.step (Step.sboxr hv hv₁ hs) ih

theorem mstep_mrgl {v e₁ e₁' e₂ : Exp} (hv : Value v) (h : MStep v e₁ e₁')
    : MStep v (.mrg e₁ e₂) (.mrg e₁' e₂) := by
  induction h with
  | refl => exact MStep.refl
  | step hs _ ih => exact MStep.step (Step.smrgl hv hs) ih

theorem mstep_mrgr {v v₁ e₂ e₂' : Exp} (hv : Value v) (hv₁ : Value v₁)
    (h : MStep (.mrg v v₁) e₂ e₂') : MStep v (.mrg v₁ e₂) (.mrg v₁ e₂') := by
  induction h with
  | refl => exact MStep.refl
  | step hs _ ih => exact MStep.step (Step.smrgr hv hv₁ hs) ih

theorem mstep_proj {v e e' : Exp} {n : Nat} (hv : Value v) (h : MStep v e e')
    : MStep v (.proj e n) (.proj e' n) := by
  induction h with
  | refl => exact MStep.refl
  | step hs _ ih => exact MStep.step (Step.sproj hv hs) ih

theorem mstep_lrec {v e e' : Exp} {l : String} (hv : Value v) (h : MStep v e e')
    : MStep v (.lrec l e) (.lrec l e') := by
  induction h with
  | refl => exact MStep.refl
  | step hs _ ih => exact MStep.step (Step.slrec hv hs) ih

theorem mstep_rproj {v e e' : Exp} {l : String} (hv : Value v) (h : MStep v e e')
    : MStep v (.rproj e l) (.rproj e' l) := by
  induction h with
  | refl => exact MStep.refl
  | step hs _ ih => exact MStep.step (Step.srproj hv hs) ih

theorem mstep_anno {v e e' : Exp} {A : Typ} (hv : Value v) (h : MStep v e e')
    : MStep v (.anno e A) (.anno e' A) := by
  induction h with
  | refl => exact MStep.refl
  | step hs _ ih => exact MStep.step (Step.sanno hv hs) ih

theorem mstep_inl {v e e' : Exp} {B : Typ} (hv : Value v) (h : MStep v e e')
    : MStep v (.inl B e) (.inl B e') := by
  induction h with
  | refl => exact MStep.refl
  | step hs _ ih => exact MStep.step (Step.sinl hv hs) ih

theorem mstep_inr {v e e' : Exp} {A : Typ} (hv : Value v) (h : MStep v e e')
    : MStep v (.inr A e) (.inr A e') := by
  induction h with
  | refl => exact MStep.refl
  | step hs _ ih => exact MStep.step (Step.sinr hv hs) ih

theorem mstep_case {v e e' e₁ e₂ : Exp} (hv : Value v) (h : MStep v e e')
    : MStep v (.case e e₁ e₂) (.case e' e₁ e₂) := by
  induction h with
  | refl => exact MStep.refl
  | step hs _ ih => exact MStep.step (Step.scase hv hs) ih

theorem mstep_fold {v e e' : Exp} {T : Typ} (hv : Value v) (h : MStep v e e')
    : MStep v (.fold T e) (.fold T e') := by
  induction h with
  | refl => exact MStep.refl
  | step hs _ ih => exact MStep.step (Step.sfold hv hs) ih

theorem mstep_unfold {v e e' : Exp} (hv : Value v) (h : MStep v e e')
    : MStep v (.unfold e) (.unfold e') := by
  induction h with
  | refl => exact MStep.refl
  | step hs _ ih => exact MStep.step (Step.sunfold hv hs) ih

-- ── Run inversions (for the surgery inside cast_lr's arrow case) ─────────────────────

-- The first step of a terminating run of an application of values is beta.
theorem mstep_app_val_inv {ρ u r : Exp} {venv : Exp} {A₀ B₀ : Typ} {e : Exp}
    (h : MStep ρ (.app (.clos venv A₀ B₀ e) u) r) (hvenv : Value venv) (hu : Value u)
    (hr : Value r)
    : ∃ u', Cast u A₀ u' ∧ MStep ρ (.box (.mrg venv u') (.anno e B₀)) r := by
  cases h with
  | refl => nomatch hr
  | step hs h' =>
    cases hs with
    | sappl _ hs' => exact (value_not_step (Value.vclos hvenv) hs').elim
    | sappr _ _ hs' => exact (value_not_step hu hs').elim
    | sbeta _ _ _ hc => exact ⟨_, hc, h'⟩

-- A terminating run of a box with a value environment runs the body under that
-- environment and returns its value.
theorem mstep_box_inv_aux {ρ bx r : Exp} (h : MStep ρ bx r)
    : ∀ {venv e : Exp}, bx = .box venv e → Value venv → Value r
    → ∃ b, MStep venv e b ∧ Value b ∧ r = b := by
  induction h with
  | refl =>
    intro venv e hbx hvenv hr
    subst hbx
    nomatch hr
  | step hs h' ih =>
    intro venv e hbx hvenv hr
    subst hbx
    cases hs with
    | sboxl _ hs' => exact (value_not_step hvenv hs').elim
    | sboxr _ _ hs' =>
      obtain ⟨b, hrun, hvb, hrb⟩ := ih rfl hvenv hr
      exact ⟨b, MStep.step hs' hrun, hvb, hrb⟩
    | sboxv _ _ hv₂ =>
      exact ⟨_, MStep.refl, hv₂, (mstep_value_eq hv₂ h').symm⟩

theorem mstep_box_inv {ρ venv e r : Exp} (h : MStep ρ (.box venv e) r)
    (hvenv : Value venv) (hr : Value r) : ∃ b, MStep venv e b ∧ Value b ∧ r = b :=
  mstep_box_inv_aux h rfl hvenv hr

-- A terminating run of an annotated term runs the term to a value and casts it.
theorem mstep_anno_inv_aux {venv an r : Exp} (h : MStep venv an r)
    : ∀ {e : Exp} {T : Typ}, an = .anno e T → Value r
    → ∃ b, MStep venv e b ∧ Value b ∧ Cast b T r := by
  induction h with
  | refl =>
    intro e T han hr
    subst han
    nomatch hr
  | step hs h' ih =>
    intro e T han hr
    subst han
    cases hs with
    | sanno _ hs' =>
      obtain ⟨b, hrun, hvb, hcb⟩ := ih rfl hr
      exact ⟨b, MStep.step hs' hrun, hvb, hcb⟩
    | sannov _ hv₁ hc =>
      exact ⟨_, MStep.refl, hv₁, (mstep_value_eq (cast_value hv₁ hc) h') ▸ hc⟩

theorem mstep_anno_inv {venv e r : Exp} {T : Typ} (h : MStep venv (.anno e T) r)
    (hr : Value r) : ∃ b, MStep venv e b ∧ Value b ∧ Cast b T r :=
  mstep_anno_inv_aux h rfl hr

-- The first step of a terminating run of a fixpoint application is sfbeta.  Note the
-- self-copy in the resulting environment carries the INTERNAL codomain in both slots —
-- it is therefore the same for the original closure and for any codomain-recast of it.
theorem mstep_fapp_val_inv {ρ u r : Exp} {venv : Exp} {A₀ B₀ Bx₀ : Typ} {e : Exp}
    (h : MStep ρ (.app (.fclos venv A₀ B₀ Bx₀ e) u) r) (hvenv : Value venv) (hu : Value u)
    (hr : Value r)
    : ∃ u', Cast u A₀ u' ∧
        MStep ρ (.box (.mrg (.mrg venv (.fclos venv A₀ B₀ B₀ e)) u') (.anno e Bx₀)) r := by
  cases h with
  | refl => nomatch hr
  | step hs h' =>
    cases hs with
    | sappl _ hs' => exact (value_not_step (Value.vfclos hvenv) hs').elim
    | sappr _ _ hs' => exact (value_not_step hu hs').elim
    | sfbeta _ _ _ hc => exact ⟨_, hc, h'⟩

-- ── Recasting a closure's behavior (the per-side surgery of cast_lr's arrow case) ─────

-- From a terminating run of the ORIGINAL closure applied to a pre-cast argument, rebuild
-- a terminating run of the codomain-RECAST closure applied to the original argument:
-- the argument casts compose by transitivity, and so do the result reseals.
theorem clos_recast_run {ρ env u uc r s : Exp} {S A₀ B₀ T : Typ} {eb : Exp}
    (hρ : Value ρ) (henv : Value env) (hvu : Value u) (hvuc : Value uc) (hvr : Value r)
    (hcu : Cast u S uc) (run : MStep ρ (.app (.clos env A₀ B₀ eb) uc) r) (hcr : Cast r T s)
    : MStep ρ (.app (.clos env A₀ T eb) u) s := by
  obtain ⟨us, cus, runbox⟩ := mstep_app_val_inv run henv hvuc hvr
  have hvm : Value (.mrg env us) := Value.vmrg henv (cast_value hvuc cus)
  obtain ⟨rr, runbody, hvrr, hreq⟩ := mstep_box_inv runbox hvm hvr
  obtain ⟨b, runb, hvb, hcb⟩ := mstep_anno_inv runbody hvrr
  have hcs' : Cast b T s := cast_trans hcb (hreq ▸ hcr)
  refine MStep.step (Step.sbeta hρ henv hvu (cast_trans hcu cus)) ?_
  refine mstep_trans (mstep_boxr hρ hvm (mstep_anno hvm runb)) ?_
  refine MStep.step (Step.sboxr hρ hvm (Step.sannov hvm hvb hcs')) ?_
  exact MStep.step (Step.sboxv hρ hvm (cast_value hvb hcs')) MStep.refl

-- The fixpoint analogue.  The self-copy inside the environment is unchanged by the
-- recast (it always carries the internal codomain), so the box runs coincide.
theorem fclos_recast_run {ρ env u uc r s : Exp} {S A₀ B₀ Bx₀ T : Typ} {eb : Exp}
    (hρ : Value ρ) (henv : Value env) (hvu : Value u) (hvuc : Value uc) (hvr : Value r)
    (hcu : Cast u S uc) (run : MStep ρ (.app (.fclos env A₀ B₀ Bx₀ eb) uc) r)
    (hcr : Cast r T s)
    : MStep ρ (.app (.fclos env A₀ B₀ T eb) u) s := by
  obtain ⟨us, cus, runbox⟩ := mstep_fapp_val_inv run henv hvuc hvr
  have hvm : Value (.mrg (.mrg env (.fclos env A₀ B₀ B₀ eb)) us) :=
    Value.vmrg (Value.vmrg henv (Value.vfclos henv)) (cast_value hvuc cus)
  obtain ⟨rr, runbody, hvrr, hreq⟩ := mstep_box_inv runbox hvm hvr
  obtain ⟨b, runb, hvb, hcb⟩ := mstep_anno_inv runbody hvrr
  have hcs' : Cast b T s := cast_trans hcb (hreq ▸ hcr)
  refine MStep.step (Step.sfbeta hρ henv hvu (cast_trans hcu cus)) ?_
  refine mstep_trans (mstep_boxr hρ hvm (mstep_anno hvm runb)) ?_
  refine MStep.step (Step.sboxr hρ hvm (Step.sannov hvm hvb hcs')) ?_
  exact MStep.step (Step.sboxv hρ hvm (cast_value hvb hcs')) MStep.refl

-- ── Merge-cast reconciliation ────────────────────────────────────────────────────────

-- Casting a well-typed merge at (a supertype of) its left component's type agrees with
-- casting the component directly.  Ordinary targets close by determinism/consistency;
-- only the & case recurses.
theorem cast_merge_eq_l_ord {a b : Exp} {Γ B₁ B₂ T : Typ} {w w' : Exp}
    (hord : Ordinary T) (hv : Value (.mrg a b)) (ht : HasType Δ Γ (.mrg a b) (.and B₁ B₂))
    (hc : Cast (.mrg a b) T w) (hc' : Cast a T w') : w = w' := by
  cases hv with
  | vmrg hva hvb =>
    cases hc with
    | cmrgl _ hx =>
      cases ht with
      | tmrg hp _ _ _ => exact cast_determinism hx hva hp hc'
      | tmergev _ _ hp _ _ _ => exact cast_determinism hx hva hp hc'
      | tmergevc _ _ hp _ _ _ _ _ _ => exact cast_determinism hx hva hp hc'
    | cmrgr _ hy =>
      cases ht with
      | tmrg hp hq _ hd₂ =>
        exact (disjoint_consistent hva hvb hp hq hd₂ hc' hy).symm
      | tmergev _ _ _ _ _ hcons => exact (hcons hc' hy).symm
      | tmergevc _ _ _ _ _ _ _ _ hcons => exact (hcons hc' hy).symm
    | cand _ _ => nomatch hord
    | ctop => nomatch hord

theorem cast_merge_eq_l {a b : Exp} {Γ B₁ B₂ : Typ} : ∀ {T : Typ} {w w' : Exp},
    Value (.mrg a b) → HasType Δ Γ (.mrg a b) (.and B₁ B₂)
    → Cast (.mrg a b) T w → Cast a T w' → w = w' := by
  intro T
  induction T with
  | top =>
    intro w w' _ _ hc hc'
    cases hc with
    | ctop =>
      cases hc' with
      | ctop => rfl
      | cmrgl hord _ => nomatch hord
      | cmrgr hord _ => nomatch hord
    | cmrgl hord _ => nomatch hord
    | cmrgr hord _ => nomatch hord
  | and T₁ T₂ ih₁ ih₂ =>
    intro w w' hv ht hc hc'
    cases hc with
    | cand hx₁ hx₂ =>
      cases hc' with
      | cand hy₁ hy₂ => rw [ih₁ hv ht hx₁ hy₁, ih₂ hv ht hx₂ hy₂]
      | cmrgl hord _ => nomatch hord
      | cmrgr hord _ => nomatch hord
    | cmrgl hord _ => nomatch hord
    | cmrgr hord _ => nomatch hord
  | int =>
    intro w w' hv ht hc hc'
    exact cast_merge_eq_l_ord Ordinary.oint hv ht hc hc'
  | arr T₁ T₂ _ _ =>
    intro w w' hv ht hc hc'
    exact cast_merge_eq_l_ord Ordinary.oarr hv ht hc hc'
  | rcd l T' _ =>
    intro w w' hv ht hc hc'
    exact cast_merge_eq_l_ord Ordinary.orcd hv ht hc hc'
  | brand _ =>
    intro w w' hv ht hc hc'
    exact cast_merge_eq_l_ord Ordinary.obrand hv ht hc hc'
  | or _ _ _ _ =>
    intro w w' hv ht hc hc'
    exact cast_merge_eq_l_ord Ordinary.oor hv ht hc hc'
  | var _ =>
    intro w w' hv ht hc hc'
    exact cast_merge_eq_l_ord Ordinary.ovar hv ht hc hc'
  | mu _ _ =>
    intro w w' hv ht hc hc'
    exact cast_merge_eq_l_ord Ordinary.omu hv ht hc hc'
  | bvar _ =>
    intro w w' hv ht hc hc'
    exact cast_merge_eq_l_ord Ordinary.obvar hv ht hc hc'
  | allb _ _ =>
    intro w w' hv ht hc hc'
    exact cast_merge_eq_l_ord Ordinary.oallb hv ht hc hc'

theorem cast_merge_eq_r_ord {a b : Exp} {Γ B₁ B₂ T : Typ} {w w' : Exp}
    (hord : Ordinary T) (hv : Value (.mrg a b)) (ht : HasType Δ Γ (.mrg a b) (.and B₁ B₂))
    (hc : Cast (.mrg a b) T w) (hc' : Cast b T w') : w = w' := by
  cases hv with
  | vmrg hva hvb =>
    cases hc with
    | cmrgr _ hy =>
      cases ht with
      | tmrg _ hq _ _ => exact cast_determinism hy hvb hq hc'
      | tmergev _ _ _ hq _ _ => exact cast_determinism hy hvb hq hc'
      | tmergevc _ _ _ hq _ _ _ _ _ => exact cast_determinism hy hvb hq hc'
    | cmrgl _ hx =>
      cases ht with
      | tmrg hp hq _ hd₂ => exact disjoint_consistent hva hvb hp hq hd₂ hx hc'
      | tmergev _ _ _ _ _ hcons => exact hcons hx hc'
      | tmergevc _ _ _ _ _ _ _ _ hcons => exact hcons hx hc'
    | cand _ _ => nomatch hord
    | ctop => nomatch hord

theorem cast_merge_eq_r {a b : Exp} {Γ B₁ B₂ : Typ} : ∀ {T : Typ} {w w' : Exp},
    Value (.mrg a b) → HasType Δ Γ (.mrg a b) (.and B₁ B₂)
    → Cast (.mrg a b) T w → Cast b T w' → w = w' := by
  intro T
  induction T with
  | top =>
    intro w w' _ _ hc hc'
    cases hc with
    | ctop =>
      cases hc' with
      | ctop => rfl
      | cmrgl hord _ => nomatch hord
      | cmrgr hord _ => nomatch hord
    | cmrgl hord _ => nomatch hord
    | cmrgr hord _ => nomatch hord
  | and T₁ T₂ ih₁ ih₂ =>
    intro w w' hv ht hc hc'
    cases hc with
    | cand hx₁ hx₂ =>
      cases hc' with
      | cand hy₁ hy₂ => rw [ih₁ hv ht hx₁ hy₁, ih₂ hv ht hx₂ hy₂]
      | cmrgl hord _ => nomatch hord
      | cmrgr hord _ => nomatch hord
    | cmrgl hord _ => nomatch hord
    | cmrgr hord _ => nomatch hord
  | int =>
    intro w w' hv ht hc hc'
    exact cast_merge_eq_r_ord Ordinary.oint hv ht hc hc'
  | arr T₁ T₂ _ _ =>
    intro w w' hv ht hc hc'
    exact cast_merge_eq_r_ord Ordinary.oarr hv ht hc hc'
  | rcd l T' _ =>
    intro w w' hv ht hc hc'
    exact cast_merge_eq_r_ord Ordinary.orcd hv ht hc hc'
  | brand _ =>
    intro w w' hv ht hc hc'
    exact cast_merge_eq_r_ord Ordinary.obrand hv ht hc hc'
  | or _ _ _ _ =>
    intro w w' hv ht hc hc'
    exact cast_merge_eq_r_ord Ordinary.oor hv ht hc hc'
  | var _ =>
    intro w w' hv ht hc hc'
    exact cast_merge_eq_r_ord Ordinary.ovar hv ht hc hc'
  | mu _ _ =>
    intro w w' hv ht hc hc'
    exact cast_merge_eq_r_ord Ordinary.omu hv ht hc hc'
  | bvar _ =>
    intro w w' hv ht hc hc'
    exact cast_merge_eq_r_ord Ordinary.obvar hv ht hc hc'
  | allb _ _ =>
    intro w w' hv ht hc hc'
    exact cast_merge_eq_r_ord Ordinary.oallb hv ht hc hc'

-- ── The generator is self-related at top-like types ──────────────────────────────────

theorem toplike_lr_gen {o : BrandOpen} (hadm : OpenAdm η o) {D : Typ} (htl : TopLike D)
    : LRg Δ₁ Δ₂ η o D (genVal (viewL o D)) (genVal (viewR o D)) := by
  induction htl with
  | tltop => rw [viewL_top, viewR_top]; exact ⟨rfl, rfl⟩
  | tland h₁ h₂ ih₁ ih₂ =>
    rw [viewL_and, viewR_and]
    exact ⟨by rw [viewL_and]; exact genVal_typed (TopLike.tland (toplike_viewL h₁) (toplike_viewL h₂)) .top,
      by rw [viewR_and]; exact genVal_typed (TopLike.tland (toplike_viewR h₁) (toplike_viewR h₂)) .top,
      _, _, _, _, rfl, rfl, ih₁, ih₂⟩
  | tlrcd h ih => rw [viewL_rcd, viewR_rcd]; exact ⟨_, _, rfl, rfl, ih⟩
  | tlarr h ih =>
    rename_i A₀ D'
    rw [viewL_arr, viewR_arr]
    refine ⟨genVal_value _, genVal_value _,
      by rw [viewL_arr]; exact genVal_typed (TopLike.tlarr (toplike_viewL h)) .top,
      by rw [viewR_arr]; exact genVal_typed (TopLike.tlarr (toplike_viewR h)) .top,
      ?_⟩
    intro u₁ u₂ hu ρ₁ ρ₂ hρ₁ hρ₂
    -- both applications run: beta (cast the argument at A₀), body is the generator of D',
    -- reseal at D' collapses to the generator again
    have hvu := lr_value hu
    have htu := lr_typed hu
    obtain ⟨u₁', hc₁⟩ := cast_progress hvu.1 htu.1 (sub_refl _)
    obtain ⟨u₂', hc₂⟩ := cast_progress hvu.2 htu.2 (sub_refl _)
    have hrun : ∀ (T : Typ) (ρ u u' : Exp), TopLike T → Value ρ → Value u → Cast u (viewL o A₀) u' →
        MStep ρ (.app (genVal (.arr (viewL o A₀) T)) u) (genVal T) := by
      intro T ρ u u' hT hρ hvu' hc
      obtain ⟨g', hcg⟩ := cast_progress (genVal_value T) (genVal_typed (Δ := Δ₁) hT .top) (sub_refl T)
      have hg' : g' = genVal T := (toplike_gen_cast hT hcg).1
      subst hg'
      refine MStep.step (Step.sbeta hρ Value.vunit hvu' hc) ?_
      have hvm : Value (.mrg .unit u') := Value.vmrg Value.vunit (cast_value hvu' hc)
      refine MStep.step (Step.sboxr hρ hvm (Step.sannov hvm (genVal_value T) hcg)) ?_
      exact MStep.step (Step.sboxv hρ hvm (cast_value (genVal_value T) hcg)) MStep.refl
    have hrun' : ∀ (T : Typ) (ρ u u' : Exp), TopLike T → Value ρ → Value u → Cast u (viewR o A₀) u' →
        MStep ρ (.app (genVal (.arr (viewR o A₀) T)) u) (genVal T) := by
      intro T ρ u u' hT hρ hvu' hc
      obtain ⟨g', hcg⟩ := cast_progress (genVal_value T) (genVal_typed (Δ := Δ₁) hT .top) (sub_refl T)
      have hg' : g' = genVal T := (toplike_gen_cast hT hcg).1
      subst hg'
      refine MStep.step (Step.sbeta hρ Value.vunit hvu' hc) ?_
      have hvm : Value (.mrg .unit u') := Value.vmrg Value.vunit (cast_value hvu' hc)
      refine MStep.step (Step.sboxr hρ hvm (Step.sannov hvm (genVal_value T) hcg)) ?_
      exact MStep.step (Step.sboxv hρ hvm (cast_value (genVal_value T) hcg)) MStep.refl
    exact ⟨genVal (viewL o D'), genVal (viewR o D'),
      hrun _ ρ₁ u₁ u₁' (toplike_viewL h) hρ₁ hvu.1 hc₁,
      hrun' _ ρ₂ u₂ u₂' (toplike_viewR h) hρ₂ hvu.2 hc₂, ih⟩

-- ── Casting is a coercion between the relations ──────────────────────────────────────
-- The semantic content of sealing.  Single structural induction on the subtyping
-- derivation: sandl/sandr reconcile the merge-peeling casts via cast_merge_eq;
-- the arrow case rebuilds the applications' runs, using cast transitivity to identify
-- the argument casts and to compose the reseal at the wider codomain.  Stated for any
-- open brand: the casts happen at the *viewed* types (that is what the semantics does).
-- Casting at a μ-type is the identity on μ-typed values (typing rules out merge peels).
theorem cast_mu_id {Δ' : BrandStore} : {v w : Exp} → {T : Typ} → {Γ : Typ} → Cast v (.mu T) w
    → Value v → HasType Δ' Γ v (.mu T) → w = v
  | _, _, _, _, .cfold, _, _ => rfl
  | _, _, _, _, .cmrgl _ _, _, ht => absurd ht (by intro h; nomatch h)
  | _, _, _, _, .cmrgr _ _, _, ht => absurd ht (by intro h; nomatch h)

-- Casting at a ∀-type is the identity on ∀-typed values (the same argument).
theorem cast_allb_id {Δ' : BrandStore} : {v w : Exp} → {A : Typ} → {Γ : Typ}
    → Cast v (.allb A) w → Value v → HasType Δ' Γ v (.allb A) → w = v
  | _, _, _, _, .cbclos, _, _ => rfl
  | _, _, _, _, .cmrgl _ _, _, ht => absurd ht (by intro h; nomatch h)
  | _, _, _, _, .cmrgr _ _, _, ht => absurd ht (by intro h; nomatch h)

-- Casting at a brand is the identity on brand-typed values (typing rules out merge
-- peels; the only leaf rule is the cwrap identity).
theorem cast_brand_id {Δ' : BrandStore} : {v w : Exp} → {n : Nat} → {Γ : Typ}
    → Cast v (.brand n) w → Value v → HasType Δ' Γ v (.brand n) → w = v
  | _, _, _, _, .cwrap, _, _ => rfl
  | _, _, _, _, .cmrgl _ _, _, ht => absurd ht (by intro h; nomatch h)
  | _, _, _, _, .cmrgr _ _, _, ht => absurd ht (by intro h; nomatch h)

-- Nothing casts at a brand VARIABLE: there is no leaf rule, and the merge peels only
-- recurse.  (Runtime types are always concrete — bvars exist only inside ∀-bodies.)
theorem cast_bvar_empty : {v w : Exp} → {i : Nat} → Cast v (.bvar i) w → False
  | _, _, _, .cmrgl _ h => cast_bvar_empty h
  | _, _, _, .cmrgr _ h => cast_bvar_empty h

theorem cast_lr {o : BrandOpen} (hadm : OpenAdm η o) {B A : Typ} (hs : Sub B A)
    {v₁ v₂ w₁ w₂ : Exp} (hlr : LRg Δ₁ Δ₂ η o B v₁ v₂)
    (c₁ : Cast v₁ (viewL o A) w₁) (c₂ : Cast v₂ (viewR o A) w₂) : LRg Δ₁ Δ₂ η o A w₁ w₂ := by
  induction hs generalizing v₁ v₂ w₁ w₂ with
  | sint =>
    obtain ⟨i, e₁, e₂⟩ := hlr
    subst e₁; subst e₂
    rw [viewL_int] at c₁; rw [viewR_int] at c₂
    cases c₁ with
    | cint =>
      cases c₂ with
      | cint => exact ⟨i, rfl, rfl⟩
  | stop =>
    rw [viewL_top] at c₁; rw [viewR_top] at c₂
    cases c₁ with
    | ctop =>
      cases c₂ with
      | ctop => exact ⟨rfl, rfl⟩
      | cmrgl hord _ => nomatch hord
      | cmrgr hord _ => nomatch hord
    | cmrgl hord _ => nomatch hord
    | cmrgr hord _ => nomatch hord
  | sand hs₁ hs₂ ih₁ ih₂ =>
    have hv := lr_value hlr
    have ht := lr_typed hlr
    rw [viewL_and] at c₁; rw [viewR_and] at c₂
    cases c₁ with
    | cand c₁ₗ c₁ᵣ =>
      cases c₂ with
      | cand c₂ₗ c₂ᵣ =>
        exact ⟨by rw [viewL_and]; exact cast_preservation (Cast.cand c₁ₗ c₁ᵣ) hv.1 ht.1,
          by rw [viewR_and]; exact cast_preservation (Cast.cand c₂ₗ c₂ᵣ) hv.2 ht.2,
          _, _, _, _, rfl, rfl, ih₁ hlr c₁ₗ c₂ₗ, ih₂ hlr c₁ᵣ c₂ᵣ⟩
      | cmrgl hord _ => nomatch hord
      | cmrgr hord _ => nomatch hord
    | cmrgl hord _ => nomatch hord
    | cmrgr hord _ => nomatch hord
  | sandl hs' ih =>
    obtain ⟨htm₁, htm₂, a₁, b₁, a₂, b₂, e₁, e₂, hA₁, hA₂⟩ := hlr
    subst e₁; subst e₂
    rw [viewL_and] at htm₁; rw [viewR_and] at htm₂
    have hva := lr_value hA₁
    have hta := lr_typed hA₁
    have hvb := lr_value hA₂
    obtain ⟨w₁', c₁'⟩ := cast_progress hva.1 hta.1 (sub_viewL hs')
    obtain ⟨w₂', c₂'⟩ := cast_progress hva.2 hta.2 (sub_viewR hs')
    rw [cast_merge_eq_l (Value.vmrg hva.1 hvb.1) htm₁ c₁ c₁',
        cast_merge_eq_l (Value.vmrg hva.2 hvb.2) htm₂ c₂ c₂']
    exact ih hA₁ c₁' c₂'
  | sandr hs' ih =>
    obtain ⟨htm₁, htm₂, a₁, b₁, a₂, b₂, e₁, e₂, hA₁, hA₂⟩ := hlr
    subst e₁; subst e₂
    rw [viewL_and] at htm₁; rw [viewR_and] at htm₂
    have hva := lr_value hA₁
    have hvb := lr_value hA₂
    have htb := lr_typed hA₂
    obtain ⟨w₁', c₁'⟩ := cast_progress hvb.1 htb.1 (sub_viewL hs')
    obtain ⟨w₂', c₂'⟩ := cast_progress hvb.2 htb.2 (sub_viewR hs')
    rw [cast_merge_eq_r (Value.vmrg hva.1 hvb.1) htm₁ c₁ c₁',
        cast_merge_eq_r (Value.vmrg hva.2 hvb.2) htm₂ c₂ c₂']
    exact ih hA₂ c₁' c₂'
  | srcd hs' ih =>
    obtain ⟨u₁, u₂, e₁, e₂, hInner⟩ := hlr
    subst e₁; subst e₂
    rw [viewL_rcd] at c₁; rw [viewR_rcd] at c₂
    cases c₁ with
    | crcd d₁ =>
      cases c₂ with
      | crcd d₂ => exact ⟨_, _, rfl, rfl, ih hInner d₁ d₂⟩
  | sbrand =>
    rename_i m
    -- abstract brand: casts are the identity on wrappers; open brand: η is cast-closed
    have wrap_case : ∀ {v₁ v₂ w₁ w₂ : Exp}, WrapRel Δ₁ Δ₂ η m v₁ v₂
        → Cast v₁ (.brand m) w₁ → Cast v₂ (.brand m) w₂ → WrapRel Δ₁ Δ₂ η m w₁ w₂ := by
      intro v₁ v₂ w₁ w₂ ⟨ht₁, ht₂, u₁, u₂, e₁, e₂, hη⟩ c₁ c₂
      subst e₁; subst e₂
      cases c₁ with
      | cwrap =>
        cases c₂ with
        | cwrap => exact ⟨ht₁, ht₂, u₁, u₂, rfl, rfl, hη⟩
    cases o with
    | none => exact wrap_case hlr c₁ c₂
    | some p =>
      obtain ⟨n, R₁, R₂⟩ := p
      by_cases hm : m = n
      · simp only [LRg, hm, if_true] at hlr ⊢
        simp only [viewL, viewR, substBrand, hm, if_true] at c₁ c₂
        obtain ⟨hv₁, hv₂, ht₁, ht₂, hη⟩ := hlr
        exact ⟨cast_value hv₁ c₁, cast_value hv₂ c₂, cast_preservation c₁ hv₁ ht₁,
          cast_preservation c₂ hv₂ ht₂, (hadm n R₁ R₂ rfl).2.2 _ _ hη _ _ c₁ c₂⟩
      · simp only [LRg, hm, if_false] at hlr ⊢
        simp only [viewL, viewR, substBrand, hm, if_false] at c₁ c₂
        exact wrap_case hlr c₁ c₂
  | svar => exact hlr.elim
  | smu =>
    obtain ⟨hv₁, hv₂, ht₁, ht₂, heq⟩ := hlr
    subst heq
    rw [viewL_mu] at c₁ ht₁; rw [viewR_mu] at c₂ ht₂
    rw [cast_mu_id c₁ hv₁ ht₁, cast_mu_id c₂ hv₂ ht₂]
    exact ⟨hv₁, hv₂, by rw [viewL_mu]; exact ht₁, by rw [viewR_mu]; exact ht₂, rfl⟩
  | sbvar => exact hlr.elim
  | sallb =>
    obtain ⟨hv₁, hv₂, ht₁, ht₂, heq⟩ := hlr
    subst heq
    rw [viewL_allb] at c₁ ht₁; rw [viewR_allb] at c₂ ht₂
    rw [cast_allb_id c₁ hv₁ ht₁, cast_allb_id c₂ hv₂ ht₂]
    exact ⟨hv₁, hv₂, by rw [viewL_allb]; exact ht₁, by rw [viewR_allb]; exact ht₂, rfl⟩
  | sor hsA hsB ihA ihB =>
    rw [viewL_or] at c₁; rw [viewR_or] at c₂
    cases hlr with
    | inl h' =>
      obtain ⟨w₁', w₂', e₁, e₂, hA⟩ := h'
      subst e₁; subst e₂
      cases c₁ with
      | cinl d₁ =>
        cases c₂ with
        | cinl d₂ => exact Or.inl ⟨_, _, rfl, rfl, ihA hA d₁ d₂⟩
    | inr h' =>
      obtain ⟨w₁', w₂', e₁, e₂, hB⟩ := h'
      subst e₁; subst e₂
      cases c₁ with
      | cinr d₁ =>
        cases c₂ with
        | cinr d₂ => exact Or.inr ⟨_, _, rfl, rfl, ihB hB d₁ d₂⟩
  | @sarr C' D' C D hsC hsD ihC ihD =>
    obtain ⟨hv₁, hv₂, ht₁, ht₂, CL⟩ := hlr
    rw [viewL_arr] at ht₁; rw [viewR_arr] at ht₂
    rw [viewL_arr] at c₁; rw [viewR_arr] at c₂
    -- The shared payload of every non-collapsing combination: cast the arguments down,
    -- run the old behavior, reseal the results up, and rebuild each side's run with the
    -- appropriate recast lemma (clos_recast_run / fclos_recast_run).
    cases c₁ with
    | cmrgl hord _ => exact absurd ht₁ (by intro h; nomatch h)
    | cmrgr hord _ => exact absurd ht₁ (by intro h; nomatch h)
    | carrowtl htlD hsc₁ hsb₁ =>
      cases c₂ with
      | cmrgl _ _ => exact absurd ht₂ (by intro h; nomatch h)
      | cmrgr _ _ => exact absurd ht₂ (by intro h; nomatch h)
      | carrow hntlD _ _ =>
        exact absurd (toplike_viewR (toplike_viewL_inv hadm htlD)) hntlD
      | cfarrow hntlD _ _ =>
        exact absurd (toplike_viewR (toplike_viewL_inv hadm htlD)) hntlD
      | carrowtl _ _ _ =>
        have := toplike_lr_gen hadm (TopLike.tlarr (toplike_viewL_inv hadm htlD))
          (Δ₁ := Δ₁) (Δ₂ := Δ₂) (o := o) (D := .arr C D) (η := η)
        rw [viewL_arr, viewR_arr] at this
        exact this
      | cfarrowtl _ _ _ =>
        have := toplike_lr_gen hadm (TopLike.tlarr (toplike_viewL_inv hadm htlD))
          (Δ₁ := Δ₁) (Δ₂ := Δ₂) (o := o) (D := .arr C D) (η := η)
        rw [viewL_arr, viewR_arr] at this
        exact this
    | cfarrowtl htlD hsc₁ hsb₁ =>
      cases c₂ with
      | cmrgl _ _ => exact absurd ht₂ (by intro h; nomatch h)
      | cmrgr _ _ => exact absurd ht₂ (by intro h; nomatch h)
      | carrow hntlD _ _ =>
        exact absurd (toplike_viewR (toplike_viewL_inv hadm htlD)) hntlD
      | cfarrow hntlD _ _ =>
        exact absurd (toplike_viewR (toplike_viewL_inv hadm htlD)) hntlD
      | carrowtl _ _ _ =>
        have := toplike_lr_gen hadm (TopLike.tlarr (toplike_viewL_inv hadm htlD))
          (Δ₁ := Δ₁) (Δ₂ := Δ₂) (o := o) (D := .arr C D) (η := η)
        rw [viewL_arr, viewR_arr] at this
        exact this
      | cfarrowtl _ _ _ =>
        have := toplike_lr_gen hadm (TopLike.tlarr (toplike_viewL_inv hadm htlD))
          (Δ₁ := Δ₁) (Δ₂ := Δ₂) (o := o) (D := .arr C D) (η := η)
        rw [viewL_arr, viewR_arr] at this
        exact this
    | carrow hntlD hsc₁ hsb₁ =>
      have hvenv₁ := value_clos_env hv₁
      cases c₂ with
      | cmrgl _ _ => exact absurd ht₂ (by intro h; nomatch h)
      | cmrgr _ _ => exact absurd ht₂ (by intro h; nomatch h)
      | carrowtl htlD _ _ =>
        exact absurd (toplike_viewL (toplike_viewR_inv hadm htlD)) hntlD
      | cfarrowtl htlD _ _ =>
        exact absurd (toplike_viewL (toplike_viewR_inv hadm htlD)) hntlD
      | carrow hntlD₂ hsc₂ hsb₂ =>
        have hvenv₂ := value_clos_env hv₂
        refine ⟨Value.vclos hvenv₁, Value.vclos hvenv₂,
          by rw [viewL_arr]; exact cast_preservation (Cast.carrow hntlD hsc₁ hsb₁) hv₁ ht₁,
          by rw [viewR_arr]; exact cast_preservation (Cast.carrow hntlD₂ hsc₂ hsb₂) hv₂ ht₂, ?_⟩
        intro u₁ u₂ hu ρ₁ ρ₂ hρ₁ hρ₂
        have hvu := lr_value hu
        have htu := lr_typed hu
        obtain ⟨u₁c, cu₁⟩ := cast_progress hvu.1 htu.1 (sub_viewL hsC)
        obtain ⟨u₂c, cu₂⟩ := cast_progress hvu.2 htu.2 (sub_viewR hsC)
        obtain ⟨r₁, r₂, run₁, run₂, hr⟩ := CL u₁c u₂c (ihC hu cu₁ cu₂) ρ₁ ρ₂ hρ₁ hρ₂
        have hvr := lr_value hr
        have htr := lr_typed hr
        obtain ⟨s₁, cs₁⟩ := cast_progress hvr.1 htr.1 (sub_viewL hsD)
        obtain ⟨s₂, cs₂⟩ := cast_progress hvr.2 htr.2 (sub_viewR hsD)
        exact ⟨s₁, s₂,
          clos_recast_run hρ₁ hvenv₁ hvu.1 (cast_value hvu.1 cu₁) hvr.1 cu₁ run₁ cs₁,
          clos_recast_run hρ₂ hvenv₂ hvu.2 (cast_value hvu.2 cu₂) hvr.2 cu₂ run₂ cs₂,
          ihD hr cs₁ cs₂⟩
      | cfarrow hntlD₂ hsc₂ hsb₂ =>
        have hvenv₂ := value_fclos_env hv₂
        refine ⟨Value.vclos hvenv₁, Value.vfclos hvenv₂,
          by rw [viewL_arr]; exact cast_preservation (Cast.carrow hntlD hsc₁ hsb₁) hv₁ ht₁,
          by rw [viewR_arr]; exact cast_preservation (Cast.cfarrow hntlD₂ hsc₂ hsb₂) hv₂ ht₂, ?_⟩
        intro u₁ u₂ hu ρ₁ ρ₂ hρ₁ hρ₂
        have hvu := lr_value hu
        have htu := lr_typed hu
        obtain ⟨u₁c, cu₁⟩ := cast_progress hvu.1 htu.1 (sub_viewL hsC)
        obtain ⟨u₂c, cu₂⟩ := cast_progress hvu.2 htu.2 (sub_viewR hsC)
        obtain ⟨r₁, r₂, run₁, run₂, hr⟩ := CL u₁c u₂c (ihC hu cu₁ cu₂) ρ₁ ρ₂ hρ₁ hρ₂
        have hvr := lr_value hr
        have htr := lr_typed hr
        obtain ⟨s₁, cs₁⟩ := cast_progress hvr.1 htr.1 (sub_viewL hsD)
        obtain ⟨s₂, cs₂⟩ := cast_progress hvr.2 htr.2 (sub_viewR hsD)
        exact ⟨s₁, s₂,
          clos_recast_run hρ₁ hvenv₁ hvu.1 (cast_value hvu.1 cu₁) hvr.1 cu₁ run₁ cs₁,
          fclos_recast_run hρ₂ hvenv₂ hvu.2 (cast_value hvu.2 cu₂) hvr.2 cu₂ run₂ cs₂,
          ihD hr cs₁ cs₂⟩
    | cfarrow hntlD hsc₁ hsb₁ =>
      have hvenv₁ := value_fclos_env hv₁
      cases c₂ with
      | cmrgl _ _ => exact absurd ht₂ (by intro h; nomatch h)
      | cmrgr _ _ => exact absurd ht₂ (by intro h; nomatch h)
      | carrowtl htlD _ _ =>
        exact absurd (toplike_viewL (toplike_viewR_inv hadm htlD)) hntlD
      | cfarrowtl htlD _ _ =>
        exact absurd (toplike_viewL (toplike_viewR_inv hadm htlD)) hntlD
      | carrow hntlD₂ hsc₂ hsb₂ =>
        have hvenv₂ := value_clos_env hv₂
        refine ⟨Value.vfclos hvenv₁, Value.vclos hvenv₂,
          by rw [viewL_arr]; exact cast_preservation (Cast.cfarrow hntlD hsc₁ hsb₁) hv₁ ht₁,
          by rw [viewR_arr]; exact cast_preservation (Cast.carrow hntlD₂ hsc₂ hsb₂) hv₂ ht₂, ?_⟩
        intro u₁ u₂ hu ρ₁ ρ₂ hρ₁ hρ₂
        have hvu := lr_value hu
        have htu := lr_typed hu
        obtain ⟨u₁c, cu₁⟩ := cast_progress hvu.1 htu.1 (sub_viewL hsC)
        obtain ⟨u₂c, cu₂⟩ := cast_progress hvu.2 htu.2 (sub_viewR hsC)
        obtain ⟨r₁, r₂, run₁, run₂, hr⟩ := CL u₁c u₂c (ihC hu cu₁ cu₂) ρ₁ ρ₂ hρ₁ hρ₂
        have hvr := lr_value hr
        have htr := lr_typed hr
        obtain ⟨s₁, cs₁⟩ := cast_progress hvr.1 htr.1 (sub_viewL hsD)
        obtain ⟨s₂, cs₂⟩ := cast_progress hvr.2 htr.2 (sub_viewR hsD)
        exact ⟨s₁, s₂,
          fclos_recast_run hρ₁ hvenv₁ hvu.1 (cast_value hvu.1 cu₁) hvr.1 cu₁ run₁ cs₁,
          clos_recast_run hρ₂ hvenv₂ hvu.2 (cast_value hvu.2 cu₂) hvr.2 cu₂ run₂ cs₂,
          ihD hr cs₁ cs₂⟩
      | cfarrow hntlD₂ hsc₂ hsb₂ =>
        have hvenv₂ := value_fclos_env hv₂
        refine ⟨Value.vfclos hvenv₁, Value.vfclos hvenv₂,
          by rw [viewL_arr]; exact cast_preservation (Cast.cfarrow hntlD hsc₁ hsb₁) hv₁ ht₁,
          by rw [viewR_arr]; exact cast_preservation (Cast.cfarrow hntlD₂ hsc₂ hsb₂) hv₂ ht₂, ?_⟩
        intro u₁ u₂ hu ρ₁ ρ₂ hρ₁ hρ₂
        have hvu := lr_value hu
        have htu := lr_typed hu
        obtain ⟨u₁c, cu₁⟩ := cast_progress hvu.1 htu.1 (sub_viewL hsC)
        obtain ⟨u₂c, cu₂⟩ := cast_progress hvu.2 htu.2 (sub_viewR hsC)
        obtain ⟨r₁, r₂, run₁, run₂, hr⟩ := CL u₁c u₂c (ihC hu cu₁ cu₂) ρ₁ ρ₂ hρ₁ hρ₂
        have hvr := lr_value hr
        have htr := lr_typed hr
        obtain ⟨s₁, cs₁⟩ := cast_progress hvr.1 htr.1 (sub_viewL hsD)
        obtain ⟨s₂, cs₂⟩ := cast_progress hvr.2 htr.2 (sub_viewR hsD)
        exact ⟨s₁, s₂,
          fclos_recast_run hρ₁ hvenv₁ hvu.1 (cast_value hvu.1 cu₁) hvr.1 cu₁ run₁ cs₁,
          fclos_recast_run hρ₂ hvenv₂ hvu.2 (cast_value hvu.2 cu₂) hvr.2 cu₂ run₂ cs₂,
          ihD hr cs₁ cs₂⟩

-- ── Semantic typing and the fundamental lemma ────────────────────────────────────────

-- Open-term relatedness.  Because contexts are types, LR Δ₁ Δ₂ η Γ *is* the environment
-- relation — no separate context clauses are needed (the λE Fig. 4 unification).
def SemTyp (Δ₁ Δ₂ : BrandStore) (η : Nat → Exp → Exp → Prop) (Γ : Typ) (e₁ e₂ : Exp) (A : Typ) : Prop :=
  ∀ {ρ₁ ρ₂ : Exp}, LR Δ₁ Δ₂ η Γ ρ₁ ρ₂ →
    ∃ w₁ w₂, MStep ρ₁ e₁ w₁ ∧ MStep ρ₂ e₂ w₂ ∧ LR Δ₁ Δ₂ η A w₁ w₂

theorem lr_top_unit : LR Δ₁ Δ₂ η .top .unit .unit := ⟨rfl, rfl⟩

-- A value semantically self-related under the empty context is LR-self-related.
theorem semtyp_value_self {v : Exp} {T : Typ} (h : SemTyp Δ₁ Δ₂ η .top v v T) (hv : Value v)
    : LR Δ₁ Δ₂ η T v v := by
  obtain ⟨w₁, w₂, r₁, r₂, hlr⟩ := h lr_top_unit
  rw [← mstep_value_eq hv r₁, ← mstep_value_eq hv r₂] at hlr
  exact hlr

-- Positional lookup respects the relation.
theorem lr_lookup {B : Typ} {n : Nat} {A : Typ} (hl : Lookup B n A)
    {r₁ r₂ : Exp} (hr : LR Δ₁ Δ₂ η B r₁ r₂)
    : ∃ s₁ s₂, LookupV r₁ n s₁ ∧ LookupV r₂ n s₂ ∧ LR Δ₁ Δ₂ η A s₁ s₂ := by
  induction hl generalizing r₁ r₂ with
  | zero =>
    obtain ⟨_, _, a₁, b₁, a₂, b₂, e₁, e₂, _, hB⟩ := hr
    subst e₁; subst e₂
    exact ⟨b₁, b₂, LookupV.lvzero, LookupV.lvzero, hB⟩
  | succ _ ih =>
    obtain ⟨_, _, a₁, b₁, a₂, b₂, e₁, e₂, hA, _⟩ := hr
    subst e₁; subst e₂
    obtain ⟨s₁, s₂, l₁, l₂, hlr'⟩ := ih hA
    exact ⟨s₁, s₂, LookupV.lvsucc l₁, LookupV.lvsucc l₂, hlr'⟩

-- Selection respects the relation.
theorem lr_rlookup {B : Typ} {l : String} {A : Typ} (hl : RLookup B l A)
    {r₁ r₂ : Exp} (hr : LR Δ₁ Δ₂ η B r₁ r₂)
    : ∃ s₁ s₂, RLookupV r₁ l s₁ ∧ RLookupV r₂ l s₂ ∧ LR Δ₁ Δ₂ η A s₁ s₂ := by
  induction hl generalizing r₁ r₂ with
  | zero =>
    obtain ⟨u₁, u₂, e₁, e₂, hInner⟩ := hr
    subst e₁; subst e₂
    exact ⟨u₁, u₂, RLookupV.rvlzero, RLookupV.rvlzero, hInner⟩
  | landl _ _ ih =>
    obtain ⟨_, _, a₁, b₁, a₂, b₂, e₁, e₂, hA, _⟩ := hr
    subst e₁; subst e₂
    obtain ⟨s₁, s₂, l₁, l₂, hlr'⟩ := ih hA
    exact ⟨s₁, s₂, RLookupV.vlandl l₁, RLookupV.vlandl l₂, hlr'⟩
  | landr _ _ ih =>
    obtain ⟨_, _, a₁, b₁, a₂, b₂, e₁, e₂, _, hB⟩ := hr
    subst e₁; subst e₂
    obtain ⟨s₁, s₂, l₁, l₂, hlr'⟩ := ih hB
    exact ⟨s₁, s₂, RLookupV.vlandr l₁, RLookupV.vlandr l₂, hlr'⟩

-- The normalizing fragment: every term former except the fixpoints.  The relational
-- layer (fundamental lemma, normalization, sealing, RI) is stated for clients in this
-- fragment — with general recursion the calculus is not normalizing and the
-- termination-flavored fundamental lemma below is simply false.  The SAFETY layer
-- (determinism, progress, preservation) covers fixpoints unconditionally.  Restoring the
-- relational results over fixpoints would need a step-indexed relation (future work).
inductive Finitary : Exp → Prop where
  | query : Finitary .query
  | proj {e : Exp} {n : Nat} : Finitary e → Finitary (.proj e n)
  | lit {n : Nat} : Finitary (.lit n)
  | unit : Finitary .unit
  | lam {A B : Typ} {e : Exp} : Finitary e → Finitary (.lam A B e)
  | box {e₁ e₂ : Exp} : Finitary e₁ → Finitary e₂ → Finitary (.box e₁ e₂)
  | clos {v : Exp} {A B : Typ} {e : Exp} : Finitary v → Finitary e → Finitary (.clos v A B e)
  | app {e₁ e₂ : Exp} : Finitary e₁ → Finitary e₂ → Finitary (.app e₁ e₂)
  | mrg {e₁ e₂ : Exp} : Finitary e₁ → Finitary e₂ → Finitary (.mrg e₁ e₂)
  | lrec {l : String} {e : Exp} : Finitary e → Finitary (.lrec l e)
  | rproj {e : Exp} {l : String} : Finitary e → Finitary (.rproj e l)
  | anno {e : Exp} {A : Typ} : Finitary e → Finitary (.anno e A)
  | wrap {n : Nat} {e : Exp} : Finitary e → Finitary (.wrap n e)
  | seal {n : Nat} {R S : Typ} {e : Exp} : Finitary e → Finitary (.seal n R S e)
  | unseal {n : Nat} {R S : Typ} {e : Exp} : Finitary e → Finitary (.unseal n R S e)
  | inl {B : Typ} {e : Exp} : Finitary e → Finitary (.inl B e)
  | inr {A : Typ} {e : Exp} : Finitary e → Finitary (.inr A e)
  | case {e e₁ e₂ : Exp} : Finitary e → Finitary e₁ → Finitary e₂ → Finitary (.case e e₁ e₂)

theorem Finitary.proj_inv {e : Exp} {n : Nat} (h : Finitary (.proj e n)) : Finitary e := by
  cases h with | proj h' => exact h'
theorem Finitary.lam_inv {A B : Typ} {e : Exp} (h : Finitary (.lam A B e)) : Finitary e := by
  cases h with | lam h' => exact h'
theorem Finitary.box_inv {e₁ e₂ : Exp} (h : Finitary (.box e₁ e₂))
    : Finitary e₁ ∧ Finitary e₂ := by cases h with | box h₁ h₂ => exact ⟨h₁, h₂⟩
theorem Finitary.clos_inv {v : Exp} {A B : Typ} {e : Exp} (h : Finitary (.clos v A B e))
    : Finitary v ∧ Finitary e := by cases h with | clos h₁ h₂ => exact ⟨h₁, h₂⟩
theorem Finitary.app_inv {e₁ e₂ : Exp} (h : Finitary (.app e₁ e₂))
    : Finitary e₁ ∧ Finitary e₂ := by cases h with | app h₁ h₂ => exact ⟨h₁, h₂⟩
theorem Finitary.mrg_inv {e₁ e₂ : Exp} (h : Finitary (.mrg e₁ e₂))
    : Finitary e₁ ∧ Finitary e₂ := by cases h with | mrg h₁ h₂ => exact ⟨h₁, h₂⟩
theorem Finitary.lrec_inv {l : String} {e : Exp} (h : Finitary (.lrec l e)) : Finitary e := by
  cases h with | lrec h' => exact h'
theorem Finitary.rproj_inv {e : Exp} {l : String} (h : Finitary (.rproj e l)) : Finitary e := by
  cases h with | rproj h' => exact h'
theorem Finitary.anno_inv {e : Exp} {A : Typ} (h : Finitary (.anno e A)) : Finitary e := by
  cases h with | anno h' => exact h'
theorem Finitary.inl_inv {B : Typ} {e : Exp} (h : Finitary (.inl B e)) : Finitary e := by
  cases h with | inl h' => exact h'
theorem Finitary.inr_inv {A : Typ} {e : Exp} (h : Finitary (.inr A e)) : Finitary e := by
  cases h with | inr h' => exact h'
theorem Finitary.case_inv {e e₁ e₂ : Exp} (h : Finitary (.case e e₁ e₂))
    : Finitary e ∧ Finitary e₁ ∧ Finitary e₂ := by
  cases h with | case h' h₁ h₂ => exact ⟨h', h₁, h₂⟩

-- The fundamental lemma: every well-typed term of the normalizing fragment is
-- semantically self-related.  Strong normalization of that fragment is an immediate
-- corollary.
theorem fundamental {Γ : Typ} {e : Exp} {A : Typ} (ht : HasType noBrands Γ e A)
    (hfin : Finitary e) : SemTyp Δ₁ Δ₂ η Γ e e A := by
  induction ht with
  | tquery =>
    intro ρ₁ ρ₂ hρ
    have hv := lr_value hρ
    exact ⟨ρ₁, ρ₂, mstep_one (Step.squery hv.1), mstep_one (Step.squery hv.2), hρ⟩
  | tint =>
    intro ρ₁ ρ₂ _
    exact ⟨_, _, MStep.refl, MStep.refl, _, rfl, rfl⟩
  | tunit =>
    intro ρ₁ ρ₂ _
    exact ⟨_, _, MStep.refl, MStep.refl, rfl, rfl⟩
  | tapp _ _ ih₁ ih₂ =>
    intro ρ₁ ρ₂ hρ
    obtain ⟨hf₁, hf₂⟩ := Finitary.app_inv hfin
    have hvρ := lr_value hρ
    obtain ⟨f₁, f₂, rf₁, rf₂, hf⟩ := ih₁ hf₁ hρ
    obtain ⟨a₁, a₂, ra₁, ra₂, ha⟩ := ih₂ hf₂ hρ
    obtain ⟨hvf₁, hvf₂, _, _, CL⟩ := hf
    obtain ⟨w₁, w₂, rw₁, rw₂, hw⟩ := CL a₁ a₂ ha ρ₁ ρ₂ hvρ.1 hvρ.2
    refine ⟨w₁, w₂, ?_, ?_, hw⟩
    · exact mstep_trans (mstep_appl hvρ.1 rf₁)
        (mstep_trans (mstep_appr hvρ.1 hvf₁ ra₁) rw₁)
    · exact mstep_trans (mstep_appl hvρ.2 rf₂)
        (mstep_trans (mstep_appr hvρ.2 hvf₂ ra₂) rw₂)
  | tbox _ _ ih₁ ih₂ =>
    intro ρ₁ ρ₂ hρ
    obtain ⟨hf₁, hf₂⟩ := Finitary.box_inv hfin
    have hvρ := lr_value hρ
    obtain ⟨g₁, g₂, rg₁, rg₂, hg⟩ := ih₁ hf₁ hρ
    have hvg := lr_value hg
    obtain ⟨w₁, w₂, rw₁, rw₂, hw⟩ := ih₂ hf₂ hg
    have hvw := lr_value hw
    refine ⟨w₁, w₂, ?_, ?_, hw⟩
    · exact mstep_trans (mstep_boxl hvρ.1 rg₁)
        (mstep_trans (mstep_boxr hvρ.1 hvg.1 rw₁)
          (mstep_one (Step.sboxv hvρ.1 hvg.1 hvw.1)))
    · exact mstep_trans (mstep_boxl hvρ.2 rg₂)
        (mstep_trans (mstep_boxr hvρ.2 hvg.2 rw₂)
          (mstep_one (Step.sboxv hvρ.2 hvg.2 hvw.2)))
  | tproj _ hl ih =>
    intro ρ₁ ρ₂ hρ
    have hvρ := lr_value hρ
    obtain ⟨r₁, r₂, rr₁, rr₂, hr⟩ := ih (Finitary.proj_inv hfin) hρ
    have hvr := lr_value hr
    obtain ⟨s₁, s₂, l₁, l₂, hs⟩ := lr_lookup hl hr
    refine ⟨s₁, s₂, ?_, ?_, hs⟩
    · exact mstep_trans (mstep_proj hvρ.1 rr₁) (mstep_one (Step.sprojv hvρ.1 hvr.1 l₁))
    · exact mstep_trans (mstep_proj hvρ.2 rr₂) (mstep_one (Step.sprojv hvρ.2 hvr.2 l₂))
  | trcd _ ih =>
    intro ρ₁ ρ₂ hρ
    have hvρ := lr_value hρ
    obtain ⟨w₁, w₂, rw₁, rw₂, hw⟩ := ih (Finitary.lrec_inv hfin) hρ
    exact ⟨_, _, mstep_lrec hvρ.1 rw₁, mstep_lrec hvρ.2 rw₂, _, _, rfl, rfl, hw⟩
  | trproj _ hl ih =>
    intro ρ₁ ρ₂ hρ
    have hvρ := lr_value hρ
    obtain ⟨r₁, r₂, rr₁, rr₂, hr⟩ := ih (Finitary.rproj_inv hfin) hρ
    have hvr := lr_value hr
    obtain ⟨s₁, s₂, l₁, l₂, hs⟩ := lr_rlookup hl hr
    refine ⟨s₁, s₂, ?_, ?_, hs⟩
    · exact mstep_trans (mstep_rproj hvρ.1 rr₁) (mstep_one (Step.srprojv hvρ.1 hvr.1 l₁))
    · exact mstep_trans (mstep_rproj hvρ.2 rr₂) (mstep_one (Step.srprojv hvρ.2 hvr.2 l₂))
  | tmrg _ _ hd₁ hd₂ ih₁ ih₂ =>
    intro ρ₁ ρ₂ hρ
    obtain ⟨hf₁, hf₂⟩ := Finitary.mrg_inv hfin
    have hvρ := lr_value hρ
    have htρ := lr_typed hρ
    obtain ⟨a₁, a₂, ra₁, ra₂, ha⟩ := ih₁ hf₁ hρ
    have hva := lr_value ha
    have hta := lr_typed ha
    have hρ' : LR Δ₁ Δ₂ η (.and _ _) (.mrg ρ₁ a₁) (.mrg ρ₂ a₂) :=
      ⟨HasType.tmergev hvρ.1 hva.1 htρ.1 hta.1 (disj_symm hd₁)
          (disjoint_consistent hvρ.1 hva.1 htρ.1 hta.1 (disj_symm hd₁)),
        HasType.tmergev hvρ.2 hva.2 htρ.2 hta.2 (disj_symm hd₁)
          (disjoint_consistent hvρ.2 hva.2 htρ.2 hta.2 (disj_symm hd₁)),
        _, _, _, _, rfl, rfl, hρ, ha⟩
    obtain ⟨b₁, b₂, rb₁, rb₂, hb⟩ := ih₂ hf₂ hρ'
    have hvb := lr_value hb
    have htb := lr_typed hb
    refine ⟨.mrg a₁ b₁, .mrg a₂ b₂, ?_, ?_, ?_⟩
    · exact mstep_trans (mstep_mrgl hvρ.1 ra₁) (mstep_mrgr hvρ.1 hva.1 rb₁)
    · exact mstep_trans (mstep_mrgl hvρ.2 ra₂) (mstep_mrgr hvρ.2 hva.2 rb₂)
    · exact ⟨HasType.tmergev hva.1 hvb.1 hta.1 htb.1 hd₂
          (disjoint_consistent hva.1 hvb.1 hta.1 htb.1 hd₂),
        HasType.tmergev hva.2 hvb.2 hta.2 htb.2 hd₂
          (disjoint_consistent hva.2 hvb.2 hta.2 htb.2 hd₂),
        _, _, _, _, rfl, rfl, ha, hb⟩
  | tmergev hv₁ hv₂ hp hq hd hcons ih₁ ih₂ =>
    intro ρ₁ ρ₂ _
    obtain ⟨hf₁, hf₂⟩ := Finitary.mrg_inv hfin
    exact ⟨_, _, MStep.refl, MStep.refl,
      HasType.tmergev hv₁ hv₂ (hastype_weaken_store storele_noBrands hp)
        (hastype_weaken_store storele_noBrands hq) hd hcons,
      HasType.tmergev hv₁ hv₂ (hastype_weaken_store storele_noBrands hp)
        (hastype_weaken_store storele_noBrands hq) hd hcons,
      _, _, _, _, rfl, rfl, semtyp_value_self (ih₁ hf₁) hv₁, semtyp_value_self (ih₂ hf₂) hv₂⟩
  | tmergevc hv₁ hv₂ hp hq hv ht hc₁ hc₂ hcons ih₁ ih₂ _ =>
    intro ρ₁ ρ₂ _
    obtain ⟨hf₁, hf₂⟩ := Finitary.mrg_inv hfin
    exact ⟨_, _, MStep.refl, MStep.refl,
      HasType.tmergevc hv₁ hv₂ (hastype_weaken_store storele_noBrands hp)
        (hastype_weaken_store storele_noBrands hq) hv
        (hastype_weaken_store storele_noBrands ht) hc₁ hc₂ hcons,
      HasType.tmergevc hv₁ hv₂ (hastype_weaken_store storele_noBrands hp)
        (hastype_weaken_store storele_noBrands hq) hv
        (hastype_weaken_store storele_noBrands ht) hc₁ hc₂ hcons,
      _, _, _, _, rfl, rfl, semtyp_value_self (ih₁ hf₁) hv₁, semtyp_value_self (ih₂ hf₂) hv₂⟩
  | tlam hd hb ih =>
    intro ρ₁ ρ₂ hρ
    have hfb := Finitary.lam_inv hfin
    have hvρ := lr_value hρ
    have htρ := lr_typed hρ
    refine ⟨_, _, mstep_one (Step.sclos hvρ.1), mstep_one (Step.sclos hvρ.2), ?_⟩
    refine ⟨Value.vclos hvρ.1, Value.vclos hvρ.2,
      HasType.tclos hvρ.1 htρ.1 hd (hastype_weaken_store storele_noBrands hb)
        (sub_refl _) (sub_refl _),
      HasType.tclos hvρ.2 htρ.2 hd (hastype_weaken_store storele_noBrands hb)
        (sub_refl _) (sub_refl _), ?_⟩
    intro u₁ u₂ hu σ₁ σ₂ hσ₁ hσ₂
    have hvu := lr_value hu
    have htu := lr_typed hu
    obtain ⟨u₁', cu₁⟩ := cast_progress hvu.1 htu.1 (sub_refl _)
    obtain ⟨u₂', cu₂⟩ := cast_progress hvu.2 htu.2 (sub_refl _)
    have hu' := cast_lr openadm_none (sub_refl _) hu cu₁ cu₂
    have hvu' := lr_value hu'
    have htu' := lr_typed hu'
    have hρ' : LR Δ₁ Δ₂ η (.and _ _) (.mrg ρ₁ u₁') (.mrg ρ₂ u₂') :=
      ⟨HasType.tmergev hvρ.1 hvu'.1 htρ.1 htu'.1 hd
          (disjoint_consistent hvρ.1 hvu'.1 htρ.1 htu'.1 hd),
        HasType.tmergev hvρ.2 hvu'.2 htρ.2 htu'.2 hd
          (disjoint_consistent hvρ.2 hvu'.2 htρ.2 htu'.2 hd),
        _, _, _, _, rfl, rfl, hρ, hu'⟩
    obtain ⟨b₁, b₂, rb₁, rb₂, hbb⟩ := ih hfb hρ'
    have hvb := lr_value hbb
    have htb := lr_typed hbb
    obtain ⟨s₁, cs₁⟩ := cast_progress hvb.1 htb.1 (sub_refl _)
    obtain ⟨s₂, cs₂⟩ := cast_progress hvb.2 htb.2 (sub_refl _)
    have hvm₁ : Value (.mrg ρ₁ u₁') := Value.vmrg hvρ.1 hvu'.1
    have hvm₂ : Value (.mrg ρ₂ u₂') := Value.vmrg hvρ.2 hvu'.2
    refine ⟨s₁, s₂, ?_, ?_, cast_lr openadm_none (sub_refl _) hbb cs₁ cs₂⟩
    · refine MStep.step (Step.sbeta hσ₁ hvρ.1 hvu.1 cu₁) ?_
      refine mstep_trans (mstep_boxr hσ₁ hvm₁ (mstep_anno hvm₁ rb₁)) ?_
      refine MStep.step (Step.sboxr hσ₁ hvm₁ (Step.sannov hvm₁ hvb.1 cs₁)) ?_
      exact MStep.step (Step.sboxv hσ₁ hvm₁ (cast_value hvb.1 cs₁)) MStep.refl
    · refine MStep.step (Step.sbeta hσ₂ hvρ.2 hvu.2 cu₂) ?_
      refine mstep_trans (mstep_boxr hσ₂ hvm₂ (mstep_anno hvm₂ rb₂)) ?_
      refine MStep.step (Step.sboxr hσ₂ hvm₂ (Step.sannov hvm₂ hvb.2 cs₂)) ?_
      exact MStep.step (Step.sboxv hσ₂ hvm₂ (cast_value hvb.2 cs₂)) MStep.refl
  | tclos hv henv₁ hd hb hs₁ hs₂ ih_env ih_b =>
    intro ρ₁ ρ₂ _
    obtain ⟨hfv, hfb⟩ := Finitary.clos_inv hfin
    have hgg := semtyp_value_self (ih_env hfv) hv
    refine ⟨_, _, MStep.refl, MStep.refl, ?_⟩
    refine ⟨Value.vclos hv, Value.vclos hv,
      HasType.tclos hv (hastype_weaken_store storele_noBrands henv₁) hd
        (hastype_weaken_store storele_noBrands hb) hs₁ hs₂,
      HasType.tclos hv (hastype_weaken_store storele_noBrands henv₁) hd
        (hastype_weaken_store storele_noBrands hb) hs₁ hs₂, ?_⟩
    intro u₁ u₂ hu σ₁ σ₂ hσ₁ hσ₂
    have hvu := lr_value hu
    have htu := lr_typed hu
    obtain ⟨u₁', cu₁⟩ := cast_progress hvu.1 htu.1 hs₂
    obtain ⟨u₂', cu₂⟩ := cast_progress hvu.2 htu.2 hs₂
    have hu' := cast_lr openadm_none hs₂ hu cu₁ cu₂
    have hvu' := lr_value hu'
    have htu' := lr_typed hu'
    have hgv := lr_value hgg
    have hgt := lr_typed hgg
    have hρ' : LR Δ₁ Δ₂ η (.and _ _) (.mrg _ u₁') (.mrg _ u₂') :=
      ⟨HasType.tmergev hgv.1 hvu'.1 hgt.1 htu'.1 hd
          (disjoint_consistent hgv.1 hvu'.1 hgt.1 htu'.1 hd),
        HasType.tmergev hgv.2 hvu'.2 hgt.2 htu'.2 hd
          (disjoint_consistent hgv.2 hvu'.2 hgt.2 htu'.2 hd),
        _, _, _, _, rfl, rfl, hgg, hu'⟩
    obtain ⟨b₁, b₂, rb₁, rb₂, hbb⟩ := ih_b hfb hρ'
    have hvb := lr_value hbb
    have htb := lr_typed hbb
    obtain ⟨s₁, cs₁⟩ := cast_progress hvb.1 htb.1 hs₁
    obtain ⟨s₂, cs₂⟩ := cast_progress hvb.2 htb.2 hs₁
    have hvm₁ : Value (.mrg _ u₁') := Value.vmrg hv hvu'.1
    have hvm₂ : Value (.mrg _ u₂') := Value.vmrg hv hvu'.2
    refine ⟨s₁, s₂, ?_, ?_, cast_lr openadm_none hs₁ hbb cs₁ cs₂⟩
    · refine MStep.step (Step.sbeta hσ₁ hv hvu.1 cu₁) ?_
      refine mstep_trans (mstep_boxr hσ₁ hvm₁ (mstep_anno hvm₁ rb₁)) ?_
      refine MStep.step (Step.sboxr hσ₁ hvm₁ (Step.sannov hvm₁ hvb.1 cs₁)) ?_
      exact MStep.step (Step.sboxv hσ₁ hvm₁ (cast_value hvb.1 cs₁)) MStep.refl
    · refine MStep.step (Step.sbeta hσ₂ hv hvu.2 cu₂) ?_
      refine mstep_trans (mstep_boxr hσ₂ hvm₂ (mstep_anno hvm₂ rb₂)) ?_
      refine MStep.step (Step.sboxr hσ₂ hvm₂ (Step.sannov hvm₂ hvb.2 cs₂)) ?_
      exact MStep.step (Step.sboxv hσ₂ hvm₂ (cast_value hvb.2 cs₂)) MStep.refl
  | tanno _ hsub ih =>
    intro ρ₁ ρ₂ hρ
    have hvρ := lr_value hρ
    obtain ⟨r₁, r₂, rr₁, rr₂, hr⟩ := ih (Finitary.anno_inv hfin) hρ
    have hvr := lr_value hr
    have htr := lr_typed hr
    obtain ⟨s₁, cs₁⟩ := cast_progress hvr.1 htr.1 hsub
    obtain ⟨s₂, cs₂⟩ := cast_progress hvr.2 htr.2 hsub
    refine ⟨s₁, s₂, ?_, ?_, cast_lr openadm_none hsub hr cs₁ cs₂⟩
    · exact mstep_trans (mstep_anno hvρ.1 rr₁) (mstep_one (Step.sannov hvρ.1 hvr.1 cs₁))
    · exact mstep_trans (mstep_anno hvρ.2 rr₂) (mstep_one (Step.sannov hvρ.2 hvr.2 cs₂))
  | tinl _ ih =>
    intro ρ₁ ρ₂ hρ
    have hvρ := lr_value hρ
    obtain ⟨w₁, w₂, rw₁, rw₂, hw⟩ := ih (Finitary.inl_inv hfin) hρ
    exact ⟨_, _, mstep_inl hvρ.1 rw₁, mstep_inl hvρ.2 rw₂, Or.inl ⟨w₁, w₂, rfl, rfl, hw⟩⟩
  | tinr _ ih =>
    intro ρ₁ ρ₂ hρ
    have hvρ := lr_value hρ
    obtain ⟨w₁, w₂, rw₁, rw₂, hw⟩ := ih (Finitary.inr_inv hfin) hρ
    exact ⟨_, _, mstep_inr hvρ.1 rw₁, mstep_inr hvρ.2 rw₂, Or.inr ⟨w₁, w₂, rfl, rfl, hw⟩⟩
  | tcase _ hd₁ hd₂ _ _ ih ih₁ ih₂ =>
    intro ρ₁ ρ₂ hρ
    obtain ⟨hfe, hfe₁, hfe₂⟩ := Finitary.case_inv hfin
    have hvρ := lr_value hρ
    have htρ := lr_typed hρ
    obtain ⟨r₁, r₂, rr₁, rr₂, hr⟩ := ih hfe hρ
    cases hr with
    | inl h' =>
      obtain ⟨w₁, w₂, e₁eq, e₂eq, hA⟩ := h'
      subst e₁eq; subst e₂eq
      have hvw := lr_value hA
      have htw := lr_typed hA
      have hρ' : LR Δ₁ Δ₂ η (.and _ _) (.mrg ρ₁ w₁) (.mrg ρ₂ w₂) :=
        ⟨HasType.tmergev hvρ.1 hvw.1 htρ.1 htw.1 hd₁
            (disjoint_consistent hvρ.1 hvw.1 htρ.1 htw.1 hd₁),
          HasType.tmergev hvρ.2 hvw.2 htρ.2 htw.2 hd₁
            (disjoint_consistent hvρ.2 hvw.2 htρ.2 htw.2 hd₁),
          _, _, _, _, rfl, rfl, hρ, hA⟩
      obtain ⟨s₁, s₂, rs₁, rs₂, hs⟩ := ih₁ hfe₁ hρ'
      have hvs := lr_value hs
      refine ⟨s₁, s₂, ?_, ?_, hs⟩
      · refine mstep_trans (mstep_case hvρ.1 rr₁) ?_
        refine MStep.step (Step.scasel hvρ.1 hvw.1) ?_
        refine mstep_trans (mstep_boxr hvρ.1 (Value.vmrg hvρ.1 hvw.1) rs₁) ?_
        exact mstep_one (Step.sboxv hvρ.1 (Value.vmrg hvρ.1 hvw.1) hvs.1)
      · refine mstep_trans (mstep_case hvρ.2 rr₂) ?_
        refine MStep.step (Step.scasel hvρ.2 hvw.2) ?_
        refine mstep_trans (mstep_boxr hvρ.2 (Value.vmrg hvρ.2 hvw.2) rs₂) ?_
        exact mstep_one (Step.sboxv hvρ.2 (Value.vmrg hvρ.2 hvw.2) hvs.2)
    | inr h' =>
      obtain ⟨w₁, w₂, e₁eq, e₂eq, hB⟩ := h'
      subst e₁eq; subst e₂eq
      have hvw := lr_value hB
      have htw := lr_typed hB
      have hρ' : LR Δ₁ Δ₂ η (.and _ _) (.mrg ρ₁ w₁) (.mrg ρ₂ w₂) :=
        ⟨HasType.tmergev hvρ.1 hvw.1 htρ.1 htw.1 hd₂
            (disjoint_consistent hvρ.1 hvw.1 htρ.1 htw.1 hd₂),
          HasType.tmergev hvρ.2 hvw.2 htρ.2 htw.2 hd₂
            (disjoint_consistent hvρ.2 hvw.2 htρ.2 htw.2 hd₂),
          _, _, _, _, rfl, rfl, hρ, hB⟩
      obtain ⟨s₁, s₂, rs₁, rs₂, hs⟩ := ih₂ hfe₂ hρ'
      have hvs := lr_value hs
      refine ⟨s₁, s₂, ?_, ?_, hs⟩
      · refine mstep_trans (mstep_case hvρ.1 rr₁) ?_
        refine MStep.step (Step.scaser hvρ.1 hvw.1) ?_
        refine mstep_trans (mstep_boxr hvρ.1 (Value.vmrg hvρ.1 hvw.1) rs₁) ?_
        exact mstep_one (Step.sboxv hvρ.1 (Value.vmrg hvρ.1 hvw.1) hvs.1)
      · refine mstep_trans (mstep_case hvρ.2 rr₂) ?_
        refine MStep.step (Step.scaser hvρ.2 hvw.2) ?_
        refine mstep_trans (mstep_boxr hvρ.2 (Value.vmrg hvρ.2 hvw.2) rs₂) ?_
        exact mstep_one (Step.sboxv hvρ.2 (Value.vmrg hvρ.2 hvw.2) hvs.2)
  -- Clients cannot brand, seal or unseal: these rules need a known representation.
  | twrap hΔ _ _ _ => nomatch hΔ
  | tseal hΔ _ _ _ _ => nomatch hΔ
  | tunseal hΔ _ _ _ _ _ => nomatch hΔ
  -- Fixpoints and iso-recursive folds are outside the normalizing fragment.
  | tflam _ _ _ _ => nomatch hfin
  | tfclos _ _ _ _ _ _ _ _ _ _ => nomatch hfin
  -- Generic terms sit outside the normalizing fragment (no blam/bclos/bapp in
  -- Finitary); the relational ∀-clause is milestone 4.
  | tblam _ _ _ => nomatch hfin
  | tbclos _ _ _ _ _ _ => nomatch hfin
  | tbapp _ _ _ _ => nomatch hfin
  | tfold _ _ _ => nomatch hfin
  | tunfold _ _ _ _ => nomatch hfin

-- ── Corollaries ──────────────────────────────────────────────────────────────────────

-- Strong normalization of well-typed λE^≤ programs (λE Theorem 4.16 for the extended
-- calculus; genuinely new for a TDOS merge calculus).
theorem normalization {e : Exp} {A : Typ} (ht : HasType noBrands .top e A)
    (hfin : Finitary e) : ∃ v, Value v ∧ MStep .unit e v := by
  obtain ⟨w₁, _, r₁, _, hlr⟩ :=
    fundamental (Δ₁ := noBrands) (Δ₂ := noBrands) (η := fun _ _ _ => False) ht hfin lr_top_unit
  exact ⟨w₁, (lr_value hlr).1, r₁⟩

-- THE SEALING THEOREM.  A client typed against the seal A and observing at Int cannot
-- distinguish two sealed values that are related at A: both runs produce the same
-- literal.  Equality holds at base observations; at higher types agreement is the
-- logical relation (extensional at arrows), not syntactic equality.
theorem sealing {A : Typ} {p₁' p₂' : Exp} (hagree : LR Δ₁ Δ₂ η A p₁' p₂')
    {e : Exp} (hcl : HasType noBrands A e .int) (hfin : Finitary e)
    : ∃ i, MStep p₁' e (.lit i) ∧ MStep p₂' e (.lit i) := by
  obtain ⟨w₁, w₂, r₁, r₂, hlr⟩ := fundamental hcl hfin hagree
  obtain ⟨i, e₁, e₂⟩ := hlr
  subst e₁; subst e₂
  exact ⟨i, r₁, r₂⟩

-- The full narrative form: two providers p₁, p₂ (of possibly different types B₁, B₂ below
-- the seal), sealed by casting at A; if the sealed views agree at A, then a client typed
-- against A, run against either sealed provider via a box, computes the same integer.
theorem sealing_providers {B₁ B₂ A : Typ} {p₁ p₂ p₁' p₂' : Exp}
    (hv₁ : Value p₁) (hv₂ : Value p₂)
    (_ht₁ : HasType Δ₁ .top p₁ B₁) (_ht₂ : HasType Δ₂ .top p₂ B₂)
    (hc₁ : Cast p₁ A p₁') (hc₂ : Cast p₂ A p₂')
    (hagree : LR Δ₁ Δ₂ η A p₁' p₂')
    {e : Exp} (hcl : HasType noBrands A e .int) (hfin : Finitary e)
    {ρ₁ ρ₂ : Exp} (hρ₁ : Value ρ₁) (hρ₂ : Value ρ₂)
    : ∃ i, MStep ρ₁ (.box p₁' e) (.lit i) ∧ MStep ρ₂ (.box p₂' e) (.lit i) := by
  obtain ⟨i, r₁, r₂⟩ := sealing hagree hcl hfin
  have hvp₁ : Value p₁' := cast_value hv₁ hc₁
  have hvp₂ : Value p₂' := cast_value hv₂ hc₂
  refine ⟨i, ?_, ?_⟩
  · exact mstep_trans (mstep_boxr hρ₁ hvp₁ r₁)
      (mstep_one (Step.sboxv hρ₁ hvp₁ Value.vint))
  · exact mstep_trans (mstep_boxr hρ₂ hvp₂ r₂)
      (mstep_one (Step.sboxv hρ₂ hvp₂ Value.vint))

end Seal
