import LeanSce.Seal.Typing

-- Small-step semantics of λE^≤: the ternary environment-passing relation of the Core
-- mechanization (per-construct congruence rules, no frames).  New relative to λE: the
-- sanno/sannov rules for the sealing primitive, and the cast premise + result reseal in
-- sbeta (both ported from Eᵢ).  New for type abstraction: `seal`/`unseal` on values step
-- in one shot through the value-level coercion relations SealV/UnsealV below (mirroring
-- how `anno` steps through Cast), plus congruences for wrap/seal/unseal.
namespace Seal

-- The proxy `seal`/`unseal` build at an arrow: the underlying closure `c` is stored in the
-- environment under the reserved label; the body unseals the argument (`?.0`), applies
-- `c` (`?.1.#f`), and seals the result — or the mirror image.  Storing `c` under a record
-- label rather than bare is what keeps the environment type disjoint from the input type
-- (tclos demands `Disj Γ₁ A`; a bare closure environment would COST-collide with any
-- signature arrow of matching codomain).
def proxyEnv (c : Exp) : Exp := .mrg .unit (.lrec reservedLabel c)

def proxyFun : Exp := .rproj (.proj .query 1) reservedLabel

-- SealV n R S v w: the value-level coercion S[n:=R] ⇒ S, structural on S.  Wraps at α_n,
-- identity at other leaves, componentwise on merges/records, proxy at arrows.
inductive SealV (n : Nat) (R : Typ) : Typ → Exp → Exp → Prop where
  | brand_eq {v}
    : SealV n R (.brand n) v (.wrap n v)
  | brand_ne {m v}
    : m ≠ n
    → SealV n R (.brand m) v v
  | int {i}
    : SealV n R .int (.lit i) (.lit i)
  | top {v}
    : SealV n R .top v .unit
  | and {A B v₁ v₂ w₁ w₂}
    : SealV n R A v₁ w₁
    → SealV n R B v₂ w₂
    → SealV n R (.and A B) (.mrg v₁ v₂) (.mrg w₁ w₂)
  | rcd {l A v w}
    : SealV n R A v w
    → SealV n R (.rcd l A) (.lrec l v) (.lrec l w)
  | arr {A B c}
    : SealV n R (.arr A B) c
        (.clos (proxyEnv c) A B
          (.seal n R B (.app proxyFun (.unseal n R A (.proj .query 0)))))
  | inl {A B v w}
    : SealV n R A v w
    → SealV n R (.or A B) (.inl (substBrand n R B) v) (.inl B w)
  | inr {A B v w}
    : SealV n R B v w
    → SealV n R (.or A B) (.inr (substBrand n R A) v) (.inr A w)
  -- μ (and stray variables) are opaque to sealing: the coercion is the identity.  WfSig
  -- only admits brand-free μ, which is what makes this type-correct.
  | var {m v}
    : SealV n R (.var m) v v
  | mu {T v}
    : SealV n R (.mu T) v v
  -- Brand variables and ∀ are opaque to sealing, exactly like var/μ: WfSig admits
  -- ∀-signatures only brand-free (and never a bvar leaf), so identity is type-correct.
  | bvar {i v}
    : SealV n R (.bvar i) v v
  | allb {A v}
    : SealV n R (.allb A) v v

-- UnsealV n R S v w: the converse coercion S ⇒ S[n:=R].
inductive UnsealV (n : Nat) (R : Typ) : Typ → Exp → Exp → Prop where
  | brand_eq {v}
    : UnsealV n R (.brand n) (.wrap n v) v
  | brand_ne {m v}
    : m ≠ n
    → UnsealV n R (.brand m) v v
  | int {i}
    : UnsealV n R .int (.lit i) (.lit i)
  | top {v}
    : UnsealV n R .top v .unit
  | and {A B v₁ v₂ w₁ w₂}
    : UnsealV n R A v₁ w₁
    → UnsealV n R B v₂ w₂
    → UnsealV n R (.and A B) (.mrg v₁ v₂) (.mrg w₁ w₂)
  | rcd {l A v w}
    : UnsealV n R A v w
    → UnsealV n R (.rcd l A) (.lrec l v) (.lrec l w)
  | arr {A B c}
    : UnsealV n R (.arr A B) c
        (.clos (proxyEnv c) (substBrand n R A) (substBrand n R B)
          (.unseal n R B (.app proxyFun (.seal n R A (.proj .query 0)))))
  | inl {A B v w}
    : UnsealV n R A v w
    → UnsealV n R (.or A B) (.inl B v) (.inl (substBrand n R B) w)
  | inr {A B v w}
    : UnsealV n R B v w
    → UnsealV n R (.or A B) (.inr A v) (.inr (substBrand n R A) w)
  | var {m v}
    : UnsealV n R (.var m) v v
  | mu {T v}
    : UnsealV n R (.mu T) v v
  | bvar {i v}
    : UnsealV n R (.bvar i) v v
  | allb {A v}
    : UnsealV n R (.allb A) v v

inductive Step : Exp → Exp → Exp → Prop where
  | squery {v}
    : Value v
    → Step v .query v
  | sappl {v e₁ e₁' e₂}
    : Value v
    → Step v e₁ e₁'
    → Step v (.app e₁ e₂) (.app e₁' e₂)
  | sappr {v v₁ e₂ e₂'}
    : Value v
    → Value v₁
    → Step v e₂ e₂'
    → Step v (.app v₁ e₂) (.app v₁ e₂')
  | sbeta {v v₁ A B e v₂ v₂'}
    : Value v
    → Value v₁
    → Value v₂
    → Cast v₂ A v₂'
    → Step v (.app (.clos v₁ A B e) v₂) (.box (.mrg v₁ v₂') (.anno e B))
  | sclos {v A B e}
    : Value v
    → Step v (.lam A B e) (.clos v A B e)
  | sinl {v e e' B}
    : Value v
    → Step v e e'
    → Step v (.inl B e) (.inl B e')
  | sinr {v e e' A}
    : Value v
    → Step v e e'
    → Step v (.inr A e) (.inr A e')
  | scase {v e e' e₁ e₂}
    : Value v
    → Step v e e'
    → Step v (.case e e₁ e₂) (.case e' e₁ e₂)
  | scasel {v v₁ B e₁ e₂}
    : Value v
    → Value v₁
    → Step v (.case (.inl B v₁) e₁ e₂) (.box (.mrg v v₁) e₁)
  | scaser {v v₁ A e₁ e₂}
    : Value v
    → Value v₁
    → Step v (.case (.inr A v₁) e₁ e₂) (.box (.mrg v v₁) e₂)
  | sfold {v e e' T}
    : Value v
    → Step v e e'
    → Step v (.fold T e) (.fold T e')
  | sunfold {v e e'}
    : Value v
    → Step v e e'
    → Step v (.unfold e) (.unfold e')
  | sunfoldv {v v₁ T}
    : Value v
    → Value v₁
    → Step v (.unfold (.fold T v₁)) v₁
  | sflam {v A B e}
    : Value v
    → Step v (.flam A B e) (.fclos v A B B e)
  -- Brand abstraction captures the ambient environment (the lam→clos pattern);
  -- instantiation pushes the concrete brand into the body's annotations and runs it
  -- under the captured environment.  No argument cast: brands are static.
  | sblam {v A e}
    : Value v
    → Step v (.blam A e) (.bclos v A e)
  | sbappl {v e e' n}
    : Value v
    → Step v e e'
    → Step v (.bapp e n) (.bapp e' n)
  | sbappbeta {v ρ A e n}
    : Value v
    → Value ρ
    → Step v (.bapp (.bclos ρ A e) n) (.box ρ (bsubstExp 0 n e))
  -- Fixpoint beta: cast the argument at the stored domain (as sbeta does), reinstall the
  -- self-reference with the external codomain RESET to the internal one (the body's
  -- context expects (A → B) at slot 1), and reseal the result at the external codomain —
  -- the client-facing type this closure was cast to.
  | sfbeta {v v₁ A B Bx e v₂ v₂'}
    : Value v
    → Value v₁
    → Value v₂
    → Cast v₂ A v₂'
    → Step v (.app (.fclos v₁ A B Bx e) v₂)
             (.box (.mrg (.mrg v₁ (.fclos v₁ A B B e)) v₂') (.anno e Bx))
  | sboxl {v e₁ e₁' e₂}
    : Value v
    → Step v e₁ e₁'
    → Step v (.box e₁ e₂) (.box e₁' e₂)
  | sboxr {v v₁ e₂ e₂'}
    : Value v
    → Value v₁
    → Step v₁ e₂ e₂'
    → Step v (.box v₁ e₂) (.box v₁ e₂')
  | sboxv {v v₁ v₂}
    : Value v
    → Value v₁
    → Value v₂
    → Step v (.box v₁ v₂) v₂
  | smrgl {v e₁ e₁' e₂}
    : Value v
    → Step v e₁ e₁'
    → Step v (.mrg e₁ e₂) (.mrg e₁' e₂)
  | smrgr {v v₁ e₂ e₂'}
    : Value v
    → Value v₁
    → Step (.mrg v v₁) e₂ e₂'
    → Step v (.mrg v₁ e₂) (.mrg v₁ e₂')
  | sproj {v e e' n}
    : Value v
    → Step v e e'
    → Step v (.proj e n) (.proj e' n)
  | sprojv {v v₁ v' n}
    : Value v
    → Value v₁
    → LookupV v₁ n v'
    → Step v (.proj v₁ n) v'
  | slrec {v e e' l}
    : Value v
    → Step v e e'
    → Step v (.lrec l e) (.lrec l e')
  | srproj {v e e' l}
    : Value v
    → Step v e e'
    → Step v (.rproj e l) (.rproj e' l)
  | srprojv {v v₁ v' l}
    : Value v
    → Value v₁
    → RLookupV v₁ l v'
    → Step v (.rproj v₁ l) v'
  | sanno {v e e' A}
    : Value v
    → Step v e e'
    → Step v (.anno e A) (.anno e' A)
  | sannov {v v₁ v' A}
    : Value v
    → Value v₁
    → Cast v₁ A v'
    → Step v (.anno v₁ A) v'
  | swrap {v e e' n}
    : Value v
    → Step v e e'
    → Step v (.wrap n e) (.wrap n e')
  | sseal {v e e' n R S}
    : Value v
    → Step v e e'
    → Step v (.seal n R S e) (.seal n R S e')
  | ssealv {v v₁ w n R S}
    : Value v
    → Value v₁
    → SealV n R S v₁ w
    → Step v (.seal n R S v₁) w
  | sunseal {v e e' n R S}
    : Value v
    → Step v e e'
    → Step v (.unseal n R S e) (.unseal n R S e')
  | sunsealv {v v₁ w n R S}
    : Value v
    → Value v₁
    → UnsealV n R S v₁ w
    → Step v (.unseal n R S v₁) w

inductive MStep : Exp → Exp → Exp → Prop where
  | refl {v e}
    : MStep v e e
  | step {v e₁ e₂ e₃}
    : Step v e₁ e₂
    → MStep v e₂ e₃
    → MStep v e₁ e₃

theorem mstep_trans {v e₁ e₂ e₃ : Exp} (h₁ : MStep v e₁ e₂) (h₂ : MStep v e₂ e₃)
    : MStep v e₁ e₃ := by
  induction h₁ with
  | refl => exact h₂
  | step hs _ ih => exact MStep.step hs (ih h₂)

theorem mstep_one {v e₁ e₂ : Exp} (h : Step v e₁ e₂) : MStep v e₁ e₂ :=
  MStep.step h MStep.refl

-- Values do not step (in any environment — the merge congruence changes the environment,
-- so the quantifier must stay inside the induction).
theorem value_not_step {e : Exp} (hv : Value e) : ∀ {v e' : Exp}, Step v e e' → False := by
  induction hv with
  | vint => intro _ _ h; nomatch h
  | vunit => intro _ _ h; nomatch h
  | vclos _ => intro _ _ h; nomatch h
  | vrcd _ ih => intro _ _ h; cases h with | slrec _ hs => exact ih hs
  | vmrg _ _ ih₁ ih₂ =>
    intro _ _ h
    cases h with
    | smrgl _ hs => exact ih₁ hs
    | smrgr _ _ hs => exact ih₂ hs
  | vwrap _ ih => intro _ _ h; cases h with | swrap _ hs => exact ih hs
  | vinl _ ih => intro _ _ h; cases h with | sinl _ hs => exact ih hs
  | vinr _ ih => intro _ _ h; cases h with | sinr _ hs => exact ih hs
  | vfold _ ih => intro _ _ h; cases h with | sfold _ hs => exact ih hs
  | vfclos _ => intro _ _ h; nomatch h
  | vbclos _ => intro _ _ h; nomatch h

-- The coercions produce values from values.
theorem sealv_value {n : Nat} {R S : Typ} {v w : Exp} (hv : Value v) (h : SealV n R S v w)
    : Value w := by
  induction h with
  | brand_eq => exact Value.vwrap hv
  | brand_ne _ => exact hv
  | int => exact Value.vint
  | top => exact Value.vunit
  | and _ _ ih₁ ih₂ => cases hv with | vmrg h₁ h₂ => exact Value.vmrg (ih₁ h₁) (ih₂ h₂)
  | rcd _ ih => cases hv with | vrcd h' => exact Value.vrcd (ih h')
  | arr => exact Value.vclos (Value.vmrg Value.vunit (Value.vrcd hv))
  | inl _ ih => cases hv with | vinl h' => exact Value.vinl (ih h')
  | inr _ ih => cases hv with | vinr h' => exact Value.vinr (ih h')
  | var => exact hv
  | mu => exact hv
  | bvar => exact hv
  | allb => exact hv

theorem unsealv_value {n : Nat} {R S : Typ} {v w : Exp} (hv : Value v) (h : UnsealV n R S v w)
    : Value w := by
  induction h with
  | brand_eq => cases hv with | vwrap h' => exact h'
  | brand_ne _ => exact hv
  | int => exact Value.vint
  | top => exact Value.vunit
  | and _ _ ih₁ ih₂ => cases hv with | vmrg h₁ h₂ => exact Value.vmrg (ih₁ h₁) (ih₂ h₂)
  | rcd _ ih => cases hv with | vrcd h' => exact Value.vrcd (ih h')
  | arr => exact Value.vclos (Value.vmrg Value.vunit (Value.vrcd hv))
  | inl _ ih => cases hv with | vinl h' => exact Value.vinl (ih h')
  | inr _ ih => cases hv with | vinr h' => exact Value.vinr (ih h')
  | var => exact hv
  | mu => exact hv
  | bvar => exact hv
  | allb => exact hv

-- The coercions are deterministic as relations (no typing needed: the shape of the
-- source type picks the rule).
theorem sealv_det {n : Nat} {R S : Typ} {v w₁ : Exp} (h₁ : SealV n R S v w₁)
    : ∀ {w₂ : Exp}, SealV n R S v w₂ → w₁ = w₂ := by
  induction h₁ with
  | brand_eq => intro _ h₂; cases h₂ with | brand_eq => rfl | brand_ne hne => exact absurd rfl hne
  | brand_ne hne => intro _ h₂; cases h₂ with | brand_eq => exact absurd rfl hne | brand_ne _ => rfl
  | int => intro _ h₂; cases h₂; rfl
  | top => intro _ h₂; cases h₂; rfl
  | and _ _ ih₁ ih₂ => intro _ h₂; cases h₂ with | and a b => rw [ih₁ a, ih₂ b]
  | rcd _ ih => intro _ h₂; cases h₂ with | rcd a => rw [ih a]
  | arr => intro _ h₂; cases h₂; rfl
  | inl _ ih => intro _ h₂; cases h₂ with | inl a => rw [ih a]
  | inr _ ih => intro _ h₂; cases h₂ with | inr a => rw [ih a]
  | var => intro _ h₂; cases h₂; rfl
  | mu => intro _ h₂; cases h₂; rfl
  | bvar => intro _ h₂; cases h₂; rfl
  | allb => intro _ h₂; cases h₂; rfl

theorem unsealv_det {n : Nat} {R S : Typ} {v w₁ : Exp} (h₁ : UnsealV n R S v w₁)
    : ∀ {w₂ : Exp}, UnsealV n R S v w₂ → w₁ = w₂ := by
  induction h₁ with
  | brand_eq => intro _ h₂; cases h₂ with | brand_eq => rfl | brand_ne hne => exact absurd rfl hne
  | brand_ne hne => intro _ h₂; cases h₂ with | brand_eq => exact absurd rfl hne | brand_ne _ => rfl
  | int => intro _ h₂; cases h₂; rfl
  | top => intro _ h₂; cases h₂; rfl
  | and _ _ ih₁ ih₂ => intro _ h₂; cases h₂ with | and a b => rw [ih₁ a, ih₂ b]
  | rcd _ ih => intro _ h₂; cases h₂ with | rcd a => rw [ih a]
  | arr => intro _ h₂; cases h₂; rfl
  | inl _ ih => intro _ h₂; cases h₂ with | inl a => rw [ih a]
  | inr _ ih => intro _ h₂; cases h₂ with | inr a => rw [ih a]
  | var => intro _ h₂; cases h₂; rfl
  | mu => intro _ h₂; cases h₂; rfl
  | bvar => intro _ h₂; cases h₂; rfl
  | allb => intro _ h₂; cases h₂; rfl

theorem mstep_value_eq {v e e' : Exp} (hv : Value e) (h : MStep v e e') : e = e' := by
  cases h with
  | refl => rfl
  | step hs _ => exact absurd hs (fun hs' => value_not_step hv hs')

end Seal
