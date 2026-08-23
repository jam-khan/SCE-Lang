import LeanSce.Seal.Disjointness

-- The casting relation v ↪_A v' (Eᵢ Figure 3), adapted to de Bruijn closures.  Casting is
-- deliberately typing-free: its premises mention only the closure's own annotations, never
-- a typing derivation — Consistent is defined from casting and consumed by typing, so a
-- typed cast would collapse that stratification.
namespace Seal

inductive Cast : Exp → Typ → Exp → Prop where
  | cint {i}
    : Cast (.lit i) .int (.lit i)
  | ctop {v}
    : Cast v .top .unit
  | carrow {v A B e C D}
    : ¬ TopLike D
    → Sub C A
    → Sub B D
    → Cast (.clos v A B e) (.arr C D) (.clos v A D e)
  | carrowtl {v A B e C D}
    : TopLike D
    → Sub C A
    → Sub B D
    → Cast (.clos v A B e) (.arr C D) (.clos .unit C D (genVal D))
  | cmrgl {v₁ v₂ A v₁'}
    : Ordinary A
    → Cast v₁ A v₁'
    → Cast (.mrg v₁ v₂) A v₁'
  | cmrgr {v₁ v₂ A v₂'}
    : Ordinary A
    → Cast v₂ A v₂'
    → Cast (.mrg v₁ v₂) A v₂'
  | cand {v A B v₁ v₂}
    : Cast v A v₁
    → Cast v B v₂
    → Cast v (.and A B) (.mrg v₁ v₂)
  | crcd {v A v' l}
    : Cast v A v'
    → Cast (.lrec l v) (.rcd l A) (.lrec l v')
  -- The one new rule for type abstraction: casting at a brand is the identity on values
  -- already branded at it, and undefined on everything else.  Casting must NOT be able to
  -- *produce* a brand from an arbitrary value (`v ↪_{α_n} ⟨n⟩v`): then every value would
  -- cast at α_n, `disjoint_consistent` would fail (5 and {l = 3} are typed at disjoint
  -- types yet would cast at α_n to different values), and with it `tmergev` and
  -- preservation.  Branding is therefore installed by `seal`, never by a cast.
  | cwrap {n v}
    : Cast (.wrap n v) (.brand n) (.wrap n v)
  -- Unions: casting follows the tag; the payload is cast at the corresponding component
  -- and the OTHER component's annotation is rewritten to the target's.
  | cinl {v A' v' B B'}
    : Cast v A' v'
    → Cast (.inl B v) (.or A' B') (.inl B' v')
  | cinr {v B' v' A A'}
    : Cast v B' v'
    → Cast (.inr A v) (.or A' B') (.inr A' v')
  -- Casting at a μ-type is the identity on folds of the SAME body (the brand pattern):
  -- μ is opaque, subtyping at μ is reflexive only, and the payload is untouched.
  | cfold {T v}
    : Cast (.fold T v) (.mu T) (.fold T v)
  -- Casting a fixpoint closure rewrites only the EXTERNAL codomain Bx; the internal B is
  -- pinned because the body's context mentions (A → B) and beta reinstalls the
  -- self-reference at it.  The Sub premise is on Bx (the value's visible codomain) so the
  -- lemma layer treats fclos exactly as it treats clos.
  | cfarrow {v A B Bx e C D}
    : ¬ TopLike D
    → Sub C A
    → Sub Bx D
    → Cast (.fclos v A B Bx e) (.arr C D) (.fclos v A B D e)
  | cfarrowtl {v A B Bx e C D}
    : TopLike D
    → Sub C A
    → Sub Bx D
    → Cast (.fclos v A B Bx e) (.arr C D) (.clos .unit C D (genVal D))
  -- Casting at a ∀-type is the identity on brand closures (the cwrap/cfold pattern):
  -- ∀ is opaque, subtyping at it is reflexive only, and the closure is untouched.
  | cbclos {ρ A e}
    : Cast (.bclos ρ A e) (.allb A) (.bclos ρ A e)

-- Eᵢ Definition 3.
def Consistent (v₁ v₂ : Exp) : Prop :=
  ∀ {A w₁ w₂}, Cast v₁ A w₁ → Cast v₂ A w₂ → w₁ = w₂

theorem cast_value {v : Exp} {A : Typ} {w : Exp} (hv : Value v) (h : Cast v A w) : Value w := by
  induction h with
  | cint => exact Value.vint
  | ctop => exact Value.vunit
  | carrow _ _ _ => cases hv with | vclos hv' => exact Value.vclos hv'
  | carrowtl _ _ _ => exact Value.vclos Value.vunit
  | cmrgl _ _ ih => cases hv with | vmrg hv₁ _ => exact ih hv₁
  | cmrgr _ _ ih => cases hv with | vmrg _ hv₂ => exact ih hv₂
  | cand _ _ ih₁ ih₂ => exact Value.vmrg (ih₁ hv) (ih₂ hv)
  | crcd _ ih => cases hv with | vrcd hv' => exact Value.vrcd (ih hv')
  | cwrap => exact hv
  | cinl _ ih => cases hv with | vinl hv' => exact Value.vinl (ih hv')
  | cinr _ ih => cases hv with | vinr hv' => exact Value.vinr (ih hv')
  | cfold => exact hv
  | cfarrow _ _ _ => cases hv with | vfclos hv' => exact Value.vfclos hv'
  | cfarrowtl _ _ _ => exact Value.vclos Value.vunit
  | cbclos => exact hv

-- Casting at a top-like type always yields the canonical generated value — the collapse
-- that keeps casting deterministic at top-like targets (Eᵢ's Casting-arrowtl rationale).
theorem cast_toplike_gen {v : Exp} {A : Typ} {w : Exp} (htl : TopLike A) (h : Cast v A w)
    : w = genVal A := by
  induction h with
  | cint => nomatch htl
  | ctop => rfl
  | carrow hntl _ _ => cases htl with | tlarr hD => exact absurd hD hntl
  | carrowtl _ _ _ => rfl
  | cmrgl _ _ ih => exact ih htl
  | cmrgr _ _ ih => exact ih htl
  | cand _ _ ih₁ ih₂ =>
    cases htl with
    | tland h₁ h₂ => rw [ih₁ h₁, ih₂ h₂]; rfl
  | crcd _ ih =>
    cases htl with
    | tlrcd h' => rw [ih h']; rfl
  | cwrap => nomatch htl
  | cinl _ _ => nomatch htl
  | cinr _ _ => nomatch htl
  | cfold => nomatch htl
  | cfarrow hntl _ _ => cases htl with | tlarr hD => exact absurd hD hntl
  | cfarrowtl _ _ _ => rfl
  | cbclos => nomatch htl

end Seal
