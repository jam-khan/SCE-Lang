import LeanSce.Seal.Syntax

-- Subtyping for λE^≤, ported verbatim from Eᵢ Figure 1 (ε plays Top).
namespace Seal

inductive Sub : Typ → Typ → Prop where
  | sint : Sub .int .int
  | stop {A} : Sub A .top
  | sarr {A₁ A₂ B₁ B₂}
    : Sub B₁ A₁
    → Sub A₂ B₂
    → Sub (.arr A₁ A₂) (.arr B₁ B₂)
  | sandl {A₁ A₂ A₃}
    : Sub A₁ A₃
    → Sub (.and A₁ A₂) A₃
  | sandr {A₁ A₂ A₃}
    : Sub A₂ A₃
    → Sub (.and A₁ A₂) A₃
  | sand {A₁ A₂ A₃}
    : Sub A₁ A₂
    → Sub A₁ A₃
    → Sub A₁ (.and A₂ A₃)
  | srcd {l A B}
    : Sub A B
    → Sub (.rcd l A) (.rcd l B)
  -- A brand is a subtype only of itself (and ε, via stop): abstract types are opaque in
  -- both directions.  In particular `brand n <: R` for its representation R is NOT
  -- derivable — that would make α_n translucent and kill representation independence.
  | sbrand {n} : Sub (.brand n) (.brand n)
  -- Unions: component-wise only.  There is deliberately no injection subtyping
  -- (A <: A ∨ B): with it, casting an untagged value at a union would have to invent a
  -- tag, and determinism of casting would be lost.
  | sor {A₁ A₂ B₁ B₂}
    : Sub A₁ B₁
    → Sub A₂ B₂
    → Sub (.or A₁ A₂) (.or B₁ B₂)
  -- μ-types and their variables are opaque: subtypes only of themselves (and ε).
  | svar {n} : Sub (.var n) (.var n)
  | smu {T} : Sub (.mu T) (.mu T)
  -- Brand variables and ∀-types: opaque, reflexive-only (the brand pattern) — a bvar
  -- stands for an unknown concrete brand, and ∀-bodies admit no width/depth variance.
  | sbvar {i} : Sub (.bvar i) (.bvar i)
  | sallb {A} : Sub (.allb A) (.allb A)

theorem sub_refl : (A : Typ) → Sub A A
  | .int => Sub.sint
  | .top => Sub.stop
  | .arr A B => Sub.sarr (sub_refl A) (sub_refl B)
  | .and A B => Sub.sand (Sub.sandl (sub_refl A)) (Sub.sandr (sub_refl B))
  | .rcd _ A => Sub.srcd (sub_refl A)
  | .brand _ => Sub.sbrand
  | .or A B => Sub.sor (sub_refl A) (sub_refl B)
  | .var _ => Sub.svar
  | .mu _ => Sub.smu
  | .bvar _ => Sub.sbvar
  | .allb _ => Sub.sallb

theorem sub_and_inv_l : {A B C : Typ} → Sub A (.and B C) → Sub A B
  | _, _, _, .sandl h => .sandl (sub_and_inv_l h)
  | _, _, _, .sandr h => .sandr (sub_and_inv_l h)
  | _, _, _, .sand h₁ _ => h₁

theorem sub_and_inv_r : {A B C : Typ} → Sub A (.and B C) → Sub A C
  | _, _, _, .sandl h => .sandl (sub_and_inv_r h)
  | _, _, _, .sandr h => .sandr (sub_and_inv_r h)
  | _, _, _, .sand _ h₂ => h₂

-- Everything is below anything above ε.
theorem top_sub : {C : Typ} → Sub .top C → ∀ A, Sub A C
  | _, .stop, _ => .stop
  | _, .sand h₁ h₂, A => .sand (top_sub h₁ A) (top_sub h₂ A)

-- Top-likeness is upward closed along subtyping.
theorem sub_toplike {A B : Typ} (htl : TopLike A) (h : Sub A B) : TopLike B := by
  induction h with
  | sint => exact htl
  | stop => exact TopLike.tltop
  | sarr _ _ _ ih₂ => cases htl with | tlarr hB => exact TopLike.tlarr (ih₂ hB)
  | sandl _ ih => cases htl with | tland h₁ _ => exact ih h₁
  | sandr _ ih => cases htl with | tland _ h₂ => exact ih h₂
  | sand _ _ ih₁ ih₂ => exact TopLike.tland (ih₁ htl) (ih₂ htl)
  | srcd _ ih => cases htl with | tlrcd hB => exact TopLike.tlrcd (ih hB)
  | sbrand => exact htl
  | sor _ _ _ _ => nomatch htl
  | svar => exact htl
  | smu => exact htl
  | sbvar => exact htl
  | sallb => exact htl

-- Peel the sandl/sandr chain of a derivation whose target is an arrow, handing the
-- arrow-vs-arrow leaf to a continuation.
theorem sub_arr_peel : {A B₁ B₂ : Typ} → {P : Typ → Prop} → Sub A (.arr B₁ B₂)
    → (∀ {A₁ A₂}, Sub B₁ A₁ → Sub A₂ B₂ → P (.arr A₁ A₂))
    → (∀ {X Y}, P X → P (.and X Y))
    → (∀ {X Y}, P Y → P (.and X Y))
    → P A
  | _, _, _, _, .sarr r s, k, _, _ => k r s
  | _, _, _, _, .sandl t, k, kl, kr => kl (sub_arr_peel t k kl kr)
  | _, _, _, _, .sandr t, k, kl, kr => kr (sub_arr_peel t k kl kr)

-- Same, for a union target.
theorem sub_or_peel : {A B₁ B₂ : Typ} → {P : Typ → Prop} → Sub A (.or B₁ B₂)
    → (∀ {A₁ A₂}, Sub A₁ B₁ → Sub A₂ B₂ → P (.or A₁ A₂))
    → (∀ {X Y}, P X → P (.and X Y))
    → (∀ {X Y}, P Y → P (.and X Y))
    → P A
  | _, _, _, _, .sor r s, k, _, _ => k r s
  | _, _, _, _, .sandl t, k, kl, kr => kl (sub_or_peel t k kl kr)
  | _, _, _, _, .sandr t, k, kl, kr => kr (sub_or_peel t k kl kr)

-- Same, for a record target.
theorem sub_rcd_peel : {A : Typ} → {l : String} → {B' : Typ} → {P : Typ → Prop}
    → Sub A (.rcd l B')
    → (∀ {A'}, Sub A' B' → P (.rcd l A'))
    → (∀ {X Y}, P X → P (.and X Y))
    → (∀ {X Y}, P Y → P (.and X Y))
    → P A
  | _, _, _, _, .srcd r, k, _, _ => k r
  | _, _, _, _, .sandl t, k, kl, kr => kl (sub_rcd_peel t k kl kr)
  | _, _, _, _, .sandr t, k, kl, kr => kr (sub_rcd_peel t k kl kr)

-- Transitivity.  Outer induction on the middle type; & and ε targets are handled by the
-- inversion lemmas before any case analysis on the second derivation, so the remaining
-- (ordinary-target) cases are pure structural peeling.
theorem sub_trans : {B A C : Typ} → Sub A B → Sub B C → Sub A C := by
  intro B
  induction B with
  | top =>
    intro A C h₁ h₂
    exact top_sub h₂ A
  | int =>
    intro A C
    induction C with
    | int => intro h₁ _; exact h₁
    | top => intro _ _; exact Sub.stop
    | arr C₁ C₂ _ _ => intro _ h₂; nomatch h₂
    | rcd l C' _ => intro _ h₂; nomatch h₂
    | brand _ => intro _ h₂; nomatch h₂
    | or C₁ C₂ _ _ => intro _ h₂; nomatch h₂
    | var _ => intro _ h₂; nomatch h₂
    | mu _ _ => intro _ h₂; nomatch h₂
    | bvar _ => intro _ h₂; nomatch h₂
    | allb _ _ => intro _ h₂; nomatch h₂
    | and C₁ C₂ ihC₁ ihC₂ =>
      intro h₁ h₂
      exact Sub.sand (ihC₁ h₁ (sub_and_inv_l h₂)) (ihC₂ h₁ (sub_and_inv_r h₂))
  | brand n =>
    intro A C
    induction C with
    | brand _ => intro h₁ h₂; cases h₂; exact h₁
    | top => intro _ _; exact Sub.stop
    | int => intro _ h₂; nomatch h₂
    | arr C₁ C₂ _ _ => intro _ h₂; nomatch h₂
    | rcd l C' _ => intro _ h₂; nomatch h₂
    | or C₁ C₂ _ _ => intro _ h₂; nomatch h₂
    | var _ => intro _ h₂; nomatch h₂
    | mu _ _ => intro _ h₂; nomatch h₂
    | bvar _ => intro _ h₂; nomatch h₂
    | allb _ _ => intro _ h₂; nomatch h₂
    | and C₁ C₂ ihC₁ ihC₂ =>
      intro h₁ h₂
      exact Sub.sand (ihC₁ h₁ (sub_and_inv_l h₂)) (ihC₂ h₁ (sub_and_inv_r h₂))
  | var m =>
    intro A C
    induction C with
    | var _ => intro h₁ h₂; cases h₂; exact h₁
    | top => intro _ _; exact Sub.stop
    | int => intro _ h₂; nomatch h₂
    | arr C₁ C₂ _ _ => intro _ h₂; nomatch h₂
    | rcd l C' _ => intro _ h₂; nomatch h₂
    | brand _ => intro _ h₂; nomatch h₂
    | or C₁ C₂ _ _ => intro _ h₂; nomatch h₂
    | mu _ _ => intro _ h₂; nomatch h₂
    | bvar _ => intro _ h₂; nomatch h₂
    | allb _ _ => intro _ h₂; nomatch h₂
    | and C₁ C₂ ihC₁ ihC₂ =>
      intro h₁ h₂
      exact Sub.sand (ihC₁ h₁ (sub_and_inv_l h₂)) (ihC₂ h₁ (sub_and_inv_r h₂))
  | mu T _ =>
    intro A C
    induction C with
    | mu _ _ => intro h₁ h₂; cases h₂; exact h₁
    | bvar _ => intro _ h₂; nomatch h₂
    | allb _ _ => intro _ h₂; nomatch h₂
    | top => intro _ _; exact Sub.stop
    | int => intro _ h₂; nomatch h₂
    | arr C₁ C₂ _ _ => intro _ h₂; nomatch h₂
    | rcd l C' _ => intro _ h₂; nomatch h₂
    | brand _ => intro _ h₂; nomatch h₂
    | or C₁ C₂ _ _ => intro _ h₂; nomatch h₂
    | var _ => intro _ h₂; nomatch h₂
    | and C₁ C₂ ihC₁ ihC₂ =>
      intro h₁ h₂
      exact Sub.sand (ihC₁ h₁ (sub_and_inv_l h₂)) (ihC₂ h₁ (sub_and_inv_r h₂))
  | bvar i =>
    intro A C
    induction C with
    | bvar _ => intro h₁ h₂; cases h₂; exact h₁
    | top => intro _ _; exact Sub.stop
    | int => intro _ h₂; nomatch h₂
    | arr C₁ C₂ _ _ => intro _ h₂; nomatch h₂
    | rcd l C' _ => intro _ h₂; nomatch h₂
    | brand _ => intro _ h₂; nomatch h₂
    | or C₁ C₂ _ _ => intro _ h₂; nomatch h₂
    | var _ => intro _ h₂; nomatch h₂
    | mu _ _ => intro _ h₂; nomatch h₂
    | allb _ _ => intro _ h₂; nomatch h₂
    | and C₁ C₂ ihC₁ ihC₂ =>
      intro h₁ h₂
      exact Sub.sand (ihC₁ h₁ (sub_and_inv_l h₂)) (ihC₂ h₁ (sub_and_inv_r h₂))
  | allb B' _ =>
    intro A C
    induction C with
    | allb _ _ => intro h₁ h₂; cases h₂; exact h₁
    | top => intro _ _; exact Sub.stop
    | int => intro _ h₂; nomatch h₂
    | arr C₁ C₂ _ _ => intro _ h₂; nomatch h₂
    | rcd l C' _ => intro _ h₂; nomatch h₂
    | brand _ => intro _ h₂; nomatch h₂
    | or C₁ C₂ _ _ => intro _ h₂; nomatch h₂
    | var _ => intro _ h₂; nomatch h₂
    | mu _ _ => intro _ h₂; nomatch h₂
    | bvar _ => intro _ h₂; nomatch h₂
    | and C₁ C₂ ihC₁ ihC₂ =>
      intro h₁ h₂
      exact Sub.sand (ihC₁ h₁ (sub_and_inv_l h₂)) (ihC₂ h₁ (sub_and_inv_r h₂))
  | and B₁ B₂ ihB₁ ihB₂ =>
    intro A C
    induction C with
    | top => intro _ _; exact Sub.stop
    | and C₁ C₂ ihC₁ ihC₂ =>
      intro h₁ h₂
      exact Sub.sand (ihC₁ h₁ (sub_and_inv_l h₂)) (ihC₂ h₁ (sub_and_inv_r h₂))
    | int =>
      intro h₁ h₂
      cases h₂ with
      | sandl hp => exact ihB₁ (sub_and_inv_l h₁) hp
      | sandr hp => exact ihB₂ (sub_and_inv_r h₁) hp
    | brand _ =>
      intro h₁ h₂
      cases h₂ with
      | sandl hp => exact ihB₁ (sub_and_inv_l h₁) hp
      | sandr hp => exact ihB₂ (sub_and_inv_r h₁) hp
    | arr C₁ C₂ _ _ =>
      intro h₁ h₂
      cases h₂ with
      | sandl hp => exact ihB₁ (sub_and_inv_l h₁) hp
      | sandr hp => exact ihB₂ (sub_and_inv_r h₁) hp
    | rcd l C' _ =>
      intro h₁ h₂
      cases h₂ with
      | sandl hp => exact ihB₁ (sub_and_inv_l h₁) hp
      | sandr hp => exact ihB₂ (sub_and_inv_r h₁) hp
    | or C₁ C₂ _ _ =>
      intro h₁ h₂
      cases h₂ with
      | sandl hp => exact ihB₁ (sub_and_inv_l h₁) hp
      | sandr hp => exact ihB₂ (sub_and_inv_r h₁) hp
    | var _ =>
      intro h₁ h₂
      cases h₂ with
      | sandl hp => exact ihB₁ (sub_and_inv_l h₁) hp
      | sandr hp => exact ihB₂ (sub_and_inv_r h₁) hp
    | mu _ _ =>
      intro h₁ h₂
      cases h₂ with
      | sandl hp => exact ihB₁ (sub_and_inv_l h₁) hp
      | sandr hp => exact ihB₂ (sub_and_inv_r h₁) hp
    | bvar _ =>
      intro h₁ h₂
      cases h₂ with
      | sandl hp => exact ihB₁ (sub_and_inv_l h₁) hp
      | sandr hp => exact ihB₂ (sub_and_inv_r h₁) hp
    | allb _ _ =>
      intro h₁ h₂
      cases h₂ with
      | sandl hp => exact ihB₁ (sub_and_inv_l h₁) hp
      | sandr hp => exact ihB₂ (sub_and_inv_r h₁) hp
  | arr B₁ B₂ ihB₁ ihB₂ =>
    intro A C
    induction C with
    | top => intro _ _; exact Sub.stop
    | and C₁ C₂ ihC₁ ihC₂ =>
      intro h₁ h₂
      exact Sub.sand (ihC₁ h₁ (sub_and_inv_l h₂)) (ihC₂ h₁ (sub_and_inv_r h₂))
    | int => intro _ h₂; nomatch h₂
    | brand _ => intro _ h₂; nomatch h₂
    | rcd l C' _ => intro _ h₂; nomatch h₂
    | or C₁ C₂ _ _ => intro _ h₂; nomatch h₂
    | var _ => intro _ h₂; nomatch h₂
    | mu _ _ => intro _ h₂; nomatch h₂
    | bvar _ => intro _ h₂; nomatch h₂
    | allb _ _ => intro _ h₂; nomatch h₂
    | arr C₁ C₂ _ _ =>
      intro h₁ h₂
      cases h₂ with
      | sarr hp hq =>
        exact sub_arr_peel (P := fun X => Sub X (.arr C₁ C₂)) h₁
          (fun r s => Sub.sarr (ihB₁ hp r) (ihB₂ s hq))
          (fun t => Sub.sandl t) (fun t => Sub.sandr t)
  | rcd l B' ihB' =>
    intro A C
    induction C with
    | top => intro _ _; exact Sub.stop
    | and C₁ C₂ ihC₁ ihC₂ =>
      intro h₁ h₂
      exact Sub.sand (ihC₁ h₁ (sub_and_inv_l h₂)) (ihC₂ h₁ (sub_and_inv_r h₂))
    | int => intro _ h₂; nomatch h₂
    | brand _ => intro _ h₂; nomatch h₂
    | arr C₁ C₂ _ _ => intro _ h₂; nomatch h₂
    | or C₁ C₂ _ _ => intro _ h₂; nomatch h₂
    | var _ => intro _ h₂; nomatch h₂
    | mu _ _ => intro _ h₂; nomatch h₂
    | bvar _ => intro _ h₂; nomatch h₂
    | allb _ _ => intro _ h₂; nomatch h₂
    | rcd l' C' _ =>
      intro h₁ h₂
      cases h₂ with
      | srcd hq =>
        exact sub_rcd_peel (P := fun X => Sub X (.rcd l C')) h₁
          (fun r => Sub.srcd (ihB' r hq))
          (fun t => Sub.sandl t) (fun t => Sub.sandr t)
  | or B₁ B₂ ihB₁ ihB₂ =>
    intro A C
    induction C with
    | top => intro _ _; exact Sub.stop
    | and C₁ C₂ ihC₁ ihC₂ =>
      intro h₁ h₂
      exact Sub.sand (ihC₁ h₁ (sub_and_inv_l h₂)) (ihC₂ h₁ (sub_and_inv_r h₂))
    | int => intro _ h₂; nomatch h₂
    | brand _ => intro _ h₂; nomatch h₂
    | arr C₁ C₂ _ _ => intro _ h₂; nomatch h₂
    | rcd l C' _ => intro _ h₂; nomatch h₂
    | var _ => intro _ h₂; nomatch h₂
    | mu _ _ => intro _ h₂; nomatch h₂
    | bvar _ => intro _ h₂; nomatch h₂
    | allb _ _ => intro _ h₂; nomatch h₂
    | or C₁ C₂ _ _ =>
      intro h₁ h₂
      cases h₂ with
      | sor hp hq =>
        exact sub_or_peel (P := fun X => Sub X (.or C₁ C₂)) h₁
          (fun r s => Sub.sor (ihB₁ r hp) (ihB₂ s hq))
          (fun t => Sub.sandl t) (fun t => Sub.sandr t)

end Seal
