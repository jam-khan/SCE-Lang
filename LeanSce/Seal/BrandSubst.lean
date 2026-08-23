import LeanSce.Seal.CastingLemmas

-- The ∀β-instantiation substitution suite (HANDOFF §3.5, items 1–6): everything the
-- typing substitution lemma `hastype_bsubst` needs, bottom-up.  The two load-bearing
-- facts are `disj_bsubst` (disjointness is UNCONDITIONALLY stable under instantiation —
-- what the conservative COST rules at brand variables buy) and `cast_bsubst` (casting
-- commutes with instantiation — what lets tmergevc's common-origin consistency be
-- rebuilt semantically after substitution).
namespace Seal

-- ── HasBVar toolkit ──────────────────────────────────────────────────────────────────

theorem hasbvar_dec : (T : Typ) → HasBVar T ∨ ¬ HasBVar T
  | .int => Or.inr (fun h => nomatch h)
  | .top => Or.inr (fun h => nomatch h)
  | .brand _ => Or.inr (fun h => nomatch h)
  | .var _ => Or.inr (fun h => nomatch h)
  | .bvar _ => Or.inl HasBVar.bvar
  | .arr A B =>
    match hasbvar_dec A, hasbvar_dec B with
    | Or.inl h, _ => Or.inl (HasBVar.arrl h)
    | _, Or.inl h => Or.inl (HasBVar.arrr h)
    | Or.inr h₁, Or.inr h₂ => Or.inr (fun h => by
        cases h with
        | arrl h' => exact h₁ h'
        | arrr h' => exact h₂ h')
  | .and A B =>
    match hasbvar_dec A, hasbvar_dec B with
    | Or.inl h, _ => Or.inl (HasBVar.andl h)
    | _, Or.inl h => Or.inl (HasBVar.andr h)
    | Or.inr h₁, Or.inr h₂ => Or.inr (fun h => by
        cases h with
        | andl h' => exact h₁ h'
        | andr h' => exact h₂ h')
  | .or A B =>
    match hasbvar_dec A, hasbvar_dec B with
    | Or.inl h, _ => Or.inl (HasBVar.orl h)
    | _, Or.inl h => Or.inl (HasBVar.orr h)
    | Or.inr h₁, Or.inr h₂ => Or.inr (fun h => by
        cases h with
        | orl h' => exact h₁ h'
        | orr h' => exact h₂ h')
  | .rcd _ A =>
    match hasbvar_dec A with
    | Or.inl h => Or.inl (HasBVar.rcd h)
    | Or.inr h₁ => Or.inr (fun h => by cases h with | rcd h' => exact h₁ h')
  | .mu T =>
    match hasbvar_dec T with
    | Or.inl h => Or.inl (HasBVar.mu h)
    | Or.inr h₁ => Or.inr (fun h => by cases h with | mu h' => exact h₁ h')
  | .allb A =>
    match hasbvar_dec A with
    | Or.inl h => Or.inl (HasBVar.allb h)
    | Or.inr h₁ => Or.inr (fun h => by cases h with | allb h' => exact h₁ h')

-- Instantiation is the identity on bvar-free types.
theorem bsubst_notin {n : Nat} : {d : Nat} → {T : Typ} → ¬ HasBVar T → bsubst d n T = T
  | _, .int, _ => rfl
  | _, .top, _ => rfl
  | _, .brand _, _ => rfl
  | _, .var _, _ => rfl
  | _, .bvar _, h => absurd HasBVar.bvar h
  | _, .arr A B, h => by
    simp only [bsubst, bsubst_notin (fun h' => h (HasBVar.arrl h')),
      bsubst_notin (fun h' => h (HasBVar.arrr h'))]
  | _, .and A B, h => by
    simp only [bsubst, bsubst_notin (fun h' => h (HasBVar.andl h')),
      bsubst_notin (fun h' => h (HasBVar.andr h'))]
  | _, .rcd l A, h => by
    simp only [bsubst, bsubst_notin (fun h' => h (HasBVar.rcd h'))]
  | _, .or A B, h => by
    simp only [bsubst, bsubst_notin (fun h' => h (HasBVar.orl h')),
      bsubst_notin (fun h' => h (HasBVar.orr h'))]
  | _, .mu T, h => by
    simp only [bsubst, bsubst_notin (fun h' => h (HasBVar.mu h'))]
  | _, .allb A, h => by
    simp only [bsubst, bsubst_notin (fun h' => h (HasBVar.allb h'))]

-- Instantiation never creates brand variables.
theorem hasbvar_bsubst_inv {n : Nat} : {d : Nat} → {T : Typ} → HasBVar (bsubst d n T)
    → HasBVar T
  | _, .int, h => nomatch h
  | _, .top, h => nomatch h
  | _, .brand _, h => nomatch h
  | _, .var _, h => nomatch h
  | _, .bvar _, _ => HasBVar.bvar
  | _, .arr A B, h => by
    simp only [bsubst] at h
    cases h with
    | arrl h' => exact HasBVar.arrl (hasbvar_bsubst_inv h')
    | arrr h' => exact HasBVar.arrr (hasbvar_bsubst_inv h')
  | _, .and A B, h => by
    simp only [bsubst] at h
    cases h with
    | andl h' => exact HasBVar.andl (hasbvar_bsubst_inv h')
    | andr h' => exact HasBVar.andr (hasbvar_bsubst_inv h')
  | _, .rcd l A, h => by
    simp only [bsubst] at h
    cases h with
    | rcd h' => exact HasBVar.rcd (hasbvar_bsubst_inv h')
  | _, .or A B, h => by
    simp only [bsubst] at h
    cases h with
    | orl h' => exact HasBVar.orl (hasbvar_bsubst_inv h')
    | orr h' => exact HasBVar.orr (hasbvar_bsubst_inv h')
  | _, .mu T, h => by
    simp only [bsubst] at h
    cases h with
    | mu h' => exact HasBVar.mu (hasbvar_bsubst_inv h')
  | _, .allb A, h => by
    simp only [bsubst] at h
    cases h with
    | allb h' => exact HasBVar.allb (hasbvar_bsubst_inv h')

-- ── Shape inversions for bsubst images ───────────────────────────────────────────────
-- bsubst preserves every head constructor except bvar (which may become a brand); these
-- ten lemmas let cost_bsubst_inv read the pre-image's shape off the image's.

theorem bsubst_eq_int {d n : Nat} : {A : Typ} → bsubst d n A = .int → A = .int
  | .int, _ => rfl
  | .top, h => nomatch h
  | .arr _ _, h => nomatch h
  | .and _ _, h => nomatch h
  | .rcd _ _, h => nomatch h
  | .brand _, h => nomatch h
  | .or _ _, h => nomatch h
  | .var _, h => nomatch h
  | .mu _, h => nomatch h
  | .allb _, h => nomatch h
  | .bvar _, h => by simp only [bsubst] at h; split at h <;> nomatch h

theorem bsubst_eq_var {d n : Nat} : {A : Typ} → {m : Nat} → bsubst d n A = .var m
    → A = .var m
  | .var _, _, h => h
  | .int, _, h => nomatch h
  | .top, _, h => nomatch h
  | .arr _ _, _, h => nomatch h
  | .and _ _, _, h => nomatch h
  | .rcd _ _, _, h => nomatch h
  | .brand _, _, h => nomatch h
  | .or _ _, _, h => nomatch h
  | .mu _, _, h => nomatch h
  | .allb _, _, h => nomatch h
  | .bvar _, _, h => by simp only [bsubst] at h; split at h <;> nomatch h

theorem bsubst_eq_bvar {d n : Nat} : {A : Typ} → {i : Nat} → bsubst d n A = .bvar i
    → A = .bvar i
  | .bvar _, _, h => by
    simp only [bsubst] at h
    split at h
    · nomatch h
    · exact h
  | .int, _, h => nomatch h
  | .top, _, h => nomatch h
  | .arr _ _, _, h => nomatch h
  | .and _ _, _, h => nomatch h
  | .rcd _ _, _, h => nomatch h
  | .brand _, _, h => nomatch h
  | .or _ _, _, h => nomatch h
  | .var _, _, h => nomatch h
  | .mu _, _, h => nomatch h
  | .allb _, _, h => nomatch h

theorem bsubst_eq_brand {d n : Nat} : {A : Typ} → {m : Nat} → bsubst d n A = .brand m
    → A = .brand m ∨ (A = .bvar d ∧ m = n)
  | .brand _, _, h => Or.inl h
  | .bvar i, _, h => by
    simp only [bsubst] at h
    split at h
    · next hi => exact Or.inr ⟨by rw [hi], by injection h with h'; exact h'.symm⟩
    · nomatch h
  | .int, _, h => nomatch h
  | .top, _, h => nomatch h
  | .arr _ _, _, h => nomatch h
  | .and _ _, _, h => nomatch h
  | .rcd _ _, _, h => nomatch h
  | .or _ _, _, h => nomatch h
  | .var _, _, h => nomatch h
  | .mu _, _, h => nomatch h
  | .allb _, _, h => nomatch h

theorem bsubst_eq_and {d n : Nat} : {A X Y : Typ} → bsubst d n A = .and X Y
    → ∃ A₁ A₂, A = .and A₁ A₂ ∧ bsubst d n A₁ = X ∧ bsubst d n A₂ = Y
  | .and A₁ A₂, _, _, h => by
    simp only [bsubst] at h
    injection h with h₁ h₂
    exact ⟨A₁, A₂, rfl, h₁, h₂⟩
  | .int, _, _, h => nomatch h
  | .top, _, _, h => nomatch h
  | .arr _ _, _, _, h => nomatch h
  | .rcd _ _, _, _, h => nomatch h
  | .brand _, _, _, h => nomatch h
  | .or _ _, _, _, h => nomatch h
  | .var _, _, _, h => nomatch h
  | .mu _, _, _, h => nomatch h
  | .allb _, _, _, h => nomatch h
  | .bvar _, _, _, h => by simp only [bsubst] at h; split at h <;> nomatch h

theorem bsubst_eq_arr {d n : Nat} : {A X Y : Typ} → bsubst d n A = .arr X Y
    → ∃ A₁ A₂, A = .arr A₁ A₂ ∧ bsubst d n A₁ = X ∧ bsubst d n A₂ = Y
  | .arr A₁ A₂, _, _, h => by
    simp only [bsubst] at h
    injection h with h₁ h₂
    exact ⟨A₁, A₂, rfl, h₁, h₂⟩
  | .int, _, _, h => nomatch h
  | .top, _, _, h => nomatch h
  | .and _ _, _, _, h => nomatch h
  | .rcd _ _, _, _, h => nomatch h
  | .brand _, _, _, h => nomatch h
  | .or _ _, _, _, h => nomatch h
  | .var _, _, _, h => nomatch h
  | .mu _, _, _, h => nomatch h
  | .allb _, _, _, h => nomatch h
  | .bvar _, _, _, h => by simp only [bsubst] at h; split at h <;> nomatch h

theorem bsubst_eq_or {d n : Nat} : {A X Y : Typ} → bsubst d n A = .or X Y
    → ∃ A₁ A₂, A = .or A₁ A₂ ∧ bsubst d n A₁ = X ∧ bsubst d n A₂ = Y
  | .or A₁ A₂, _, _, h => by
    simp only [bsubst] at h
    injection h with h₁ h₂
    exact ⟨A₁, A₂, rfl, h₁, h₂⟩
  | .int, _, _, h => nomatch h
  | .top, _, _, h => nomatch h
  | .arr _ _, _, _, h => nomatch h
  | .and _ _, _, _, h => nomatch h
  | .rcd _ _, _, _, h => nomatch h
  | .brand _, _, _, h => nomatch h
  | .var _, _, _, h => nomatch h
  | .mu _, _, _, h => nomatch h
  | .allb _, _, _, h => nomatch h
  | .bvar _, _, _, h => by simp only [bsubst] at h; split at h <;> nomatch h

theorem bsubst_eq_rcd {d n : Nat} : {A : Typ} → {l : String} → {X : Typ}
    → bsubst d n A = .rcd l X → ∃ A', A = .rcd l A' ∧ bsubst d n A' = X
  | .rcd l' A', _, _, h => by
    simp only [bsubst] at h
    injection h with h₁ h₂
    exact ⟨A', by rw [h₁], h₂⟩
  | .int, _, _, h => nomatch h
  | .top, _, _, h => nomatch h
  | .arr _ _, _, _, h => nomatch h
  | .and _ _, _, _, h => nomatch h
  | .brand _, _, _, h => nomatch h
  | .or _ _, _, _, h => nomatch h
  | .var _, _, _, h => nomatch h
  | .mu _, _, _, h => nomatch h
  | .allb _, _, _, h => nomatch h
  | .bvar _, _, _, h => by simp only [bsubst] at h; split at h <;> nomatch h

theorem bsubst_eq_mu {d n : Nat} : {A T : Typ} → bsubst d n A = .mu T
    → ∃ T', A = .mu T' ∧ bsubst d n T' = T
  | .mu T', _, h => by
    simp only [bsubst] at h
    injection h with h₁
    exact ⟨T', rfl, h₁⟩
  | .int, _, h => nomatch h
  | .top, _, h => nomatch h
  | .arr _ _, _, h => nomatch h
  | .and _ _, _, h => nomatch h
  | .rcd _ _, _, h => nomatch h
  | .brand _, _, h => nomatch h
  | .or _ _, _, h => nomatch h
  | .var _, _, h => nomatch h
  | .allb _, _, h => nomatch h
  | .bvar _, _, h => by simp only [bsubst] at h; split at h <;> nomatch h

theorem bsubst_eq_allb {d n : Nat} : {A X : Typ} → bsubst d n A = .allb X
    → ∃ A', A = .allb A' ∧ bsubst (d + 1) n A' = X
  | .allb A', _, h => by
    simp only [bsubst] at h
    injection h with h₁
    exact ⟨A', rfl, h₁⟩
  | .int, _, h => nomatch h
  | .top, _, h => nomatch h
  | .arr _ _, _, h => nomatch h
  | .and _ _, _, h => nomatch h
  | .rcd _ _, _, h => nomatch h
  | .brand _, _, h => nomatch h
  | .or _ _, _, h => nomatch h
  | .var _, _, h => nomatch h
  | .mu _, _, h => nomatch h
  | .bvar _, _, h => by simp only [bsubst] at h; split at h <;> nomatch h

-- ── The gain-analysis: COST is only lost, never gained, under instantiation ──────────

theorem cost_bsubst_inv {n : Nat} {d : Nat} {A B : Typ}
    (hc : Cost (bsubst d n A) (bsubst d n B)) : Cost A B := by
  revert hc
  generalize hA : bsubst d n A = A'
  generalize hB : bsubst d n B = B'
  intro hc
  induction hc generalizing d A B with
  | cint =>
    rw [bsubst_eq_int hA, bsubst_eq_int hB]
    exact Cost.cint
  | candl _ ih =>
    obtain ⟨A₁, A₂, rfl, h₁, _⟩ := bsubst_eq_and hA
    exact Cost.candl (ih h₁ hB)
  | candr _ ih =>
    obtain ⟨A₁, A₂, rfl, _, h₂⟩ := bsubst_eq_and hA
    exact Cost.candr (ih h₂ hB)
  | crandl _ ih =>
    obtain ⟨B₁, B₂, rfl, h₁, _⟩ := bsubst_eq_and hB
    exact Cost.crandl (ih hA h₁)
  | crandr _ ih =>
    obtain ⟨B₁, B₂, rfl, _, h₂⟩ := bsubst_eq_and hB
    exact Cost.crandr (ih hA h₂)
  | carr _ ih =>
    obtain ⟨A₁, A₂, rfl, _, h₂⟩ := bsubst_eq_arr hA
    obtain ⟨B₁, B₂, rfl, _, h₂'⟩ := bsubst_eq_arr hB
    exact Cost.carr (ih h₂ h₂')
  | crcd _ ih =>
    obtain ⟨A', rfl, h₁⟩ := bsubst_eq_rcd hA
    obtain ⟨B', rfl, h₂⟩ := bsubst_eq_rcd hB
    exact Cost.crcd (ih h₁ h₂)
  | cbrand =>
    cases bsubst_eq_brand hA with
    | inl h₁ =>
      cases bsubst_eq_brand hB with
      | inl h₂ => rw [h₁, h₂]; exact Cost.cbrand
      | inr h₂ => rw [h₁, h₂.1]; exact Cost.cbrandbvar
    | inr h₁ =>
      cases bsubst_eq_brand hB with
      | inl h₂ => rw [h₁.1, h₂]; exact Cost.cbvarbrand
      | inr h₂ => rw [h₁.1, h₂.1]; exact Cost.cbvar
  | coror =>
    obtain ⟨A₁, A₂, rfl, _, _⟩ := bsubst_eq_or hA
    obtain ⟨B₁, B₂, rfl, _, _⟩ := bsubst_eq_or hB
    exact Cost.coror
  | cvar =>
    rw [bsubst_eq_var hA, bsubst_eq_var hB]
    exact Cost.cvar
  | cmu =>
    obtain ⟨T₁, rfl, h₁⟩ := bsubst_eq_mu hA
    obtain ⟨T₂, rfl, h₂⟩ := bsubst_eq_mu hB
    cases hasbvar_dec T₁ with
    | inl hb => exact Cost.cmubv (Or.inl hb)
    | inr hb₁ =>
      cases hasbvar_dec T₂ with
      | inl hb => exact Cost.cmubv (Or.inr hb)
      | inr hb₂ =>
        have heq : T₁ = T₂ := by rw [← bsubst_notin (d := d) (n := n) hb₁, h₁, ← h₂,
          bsubst_notin hb₂]
        rw [heq]
        exact Cost.cmu
  | cbvar =>
    rw [bsubst_eq_bvar hA, bsubst_eq_bvar hB]
    exact Cost.cbvar
  | cbvarbrand =>
    rw [bsubst_eq_bvar hA]
    cases bsubst_eq_brand hB with
    | inl h₂ => rw [h₂]; exact Cost.cbvarbrand
    | inr h₂ => rw [h₂.1]; exact Cost.cbvar
  | cbrandbvar =>
    rw [bsubst_eq_bvar hB]
    cases bsubst_eq_brand hA with
    | inl h₁ => rw [h₁]; exact Cost.cbrandbvar
    | inr h₁ => rw [h₁.1]; exact Cost.cbvar
  | callb =>
    obtain ⟨A₁, rfl, h₁⟩ := bsubst_eq_allb hA
    obtain ⟨A₂, rfl, h₂⟩ := bsubst_eq_allb hB
    cases hasbvar_dec A₁ with
    | inl hb => exact Cost.callbbv (Or.inl hb)
    | inr hb₁ =>
      cases hasbvar_dec A₂ with
      | inl hb => exact Cost.callbbv (Or.inr hb)
      | inr hb₂ =>
        have heq : A₁ = A₂ := by rw [← bsubst_notin (d := d + 1) (n := n) hb₁, h₁, ← h₂,
          bsubst_notin hb₂]
        rw [heq]
        exact Cost.callb
  | callbbv h =>
    obtain ⟨A₁, rfl, h₁⟩ := bsubst_eq_allb hA
    obtain ⟨A₂, rfl, h₂⟩ := bsubst_eq_allb hB
    cases h with
    | inl hx =>
      rw [← h₁] at hx
      exact Cost.callbbv (Or.inl (hasbvar_bsubst_inv hx))
    | inr hy =>
      rw [← h₂] at hy
      exact Cost.callbbv (Or.inr (hasbvar_bsubst_inv hy))
  | cmubv h =>
    obtain ⟨T₁, rfl, h₁⟩ := bsubst_eq_mu hA
    obtain ⟨T₂, rfl, h₂⟩ := bsubst_eq_mu hB
    cases h with
    | inl hx =>
      rw [← h₁] at hx
      exact Cost.cmubv (Or.inl (hasbvar_bsubst_inv hx))
    | inr hy =>
      rw [← h₂] at hy
      exact Cost.cmubv (Or.inr (hasbvar_bsubst_inv hy))

-- Disjointness is UNCONDITIONALLY stable under ∀β-instantiation.
theorem disj_bsubst {d n : Nat} {A B : Typ} (hd : Disj A B)
    : Disj (bsubst d n A) (bsubst d n B) :=
  fun hc => hd (cost_bsubst_inv hc)

-- ── Structural stability under bsubst ────────────────────────────────────────────────

theorem sub_bsubst {d n : Nat} {A B : Typ} (h : Sub A B)
    : Sub (bsubst d n A) (bsubst d n B) := by
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

theorem lookup_bsubst {d n : Nat} {B : Typ} {k : Nat} {A : Typ} (h : Lookup B k A)
    : Lookup (bsubst d n B) k (bsubst d n A) := by
  induction h with
  | zero => exact Lookup.zero
  | succ _ ih => exact Lookup.succ ih

theorem lin_bsubst_inv {n : Nat} : {d : Nat} → {l : String} → {B : Typ}
    → Lin l (bsubst d n B) → Lin l B
  | _, _, .rcd _ _, h => by
    simp only [bsubst] at h
    cases h
    exact Lin.rcd
  | _, _, .and _ _, h => by
    simp only [bsubst] at h
    cases h with
    | andl h' => exact Lin.andl (lin_bsubst_inv h')
    | andr h' => exact Lin.andr (lin_bsubst_inv h')
  | _, _, .bvar _, h => by simp only [bsubst] at h; split at h <;> nomatch h
  | _, _, .int, h => nomatch h
  | _, _, .top, h => nomatch h
  | _, _, .arr _ _, h => nomatch h
  | _, _, .brand _, h => nomatch h
  | _, _, .or _ _, h => nomatch h
  | _, _, .var _, h => nomatch h
  | _, _, .mu _, h => nomatch h
  | _, _, .allb _, h => nomatch h

theorem rlookup_bsubst {d n : Nat} {B : Typ} {l : String} {A : Typ} (h : RLookup B l A)
    : RLookup (bsubst d n B) l (bsubst d n A) := by
  induction h with
  | zero => exact RLookup.zero
  | landl _ hnl ih => exact RLookup.landl ih (fun h' => hnl (lin_bsubst_inv h'))
  | landr _ hnl ih => exact RLookup.landr ih (fun h' => hnl (lin_bsubst_inv h'))

theorem toplike_bsubst {d n : Nat} {A : Typ} (h : TopLike A) : TopLike (bsubst d n A) := by
  induction h with
  | tltop => exact TopLike.tltop
  | tland _ _ ih₁ ih₂ => exact TopLike.tland ih₁ ih₂
  | tlarr _ ih => exact TopLike.tlarr ih
  | tlrcd _ ih => exact TopLike.tlrcd ih

theorem toplike_bsubst_inv {n : Nat} : {d : Nat} → {A : Typ} → TopLike (bsubst d n A)
    → TopLike A
  | _, .top, _ => TopLike.tltop
  | _, .and _ _, h => by
    simp only [bsubst] at h
    cases h with
    | tland h₁ h₂ => exact TopLike.tland (toplike_bsubst_inv h₁) (toplike_bsubst_inv h₂)
  | _, .arr _ _, h => by
    simp only [bsubst] at h
    cases h with
    | tlarr h' => exact TopLike.tlarr (toplike_bsubst_inv h')
  | _, .rcd _ _, h => by
    simp only [bsubst] at h
    cases h with
    | tlrcd h' => exact TopLike.tlrcd (toplike_bsubst_inv h')
  | _, .bvar _, h => by simp only [bsubst] at h; split at h <;> nomatch h
  | _, .int, h => nomatch h
  | _, .brand _, h => nomatch h
  | _, .or _ _, h => nomatch h
  | _, .var _, h => nomatch h
  | _, .mu _, h => nomatch h
  | _, .allb _, h => nomatch h

theorem ordinary_bsubst {d n : Nat} {A : Typ} (h : Ordinary A)
    : Ordinary (bsubst d n A) := by
  cases h with
  | oint => exact Ordinary.oint
  | oarr => exact Ordinary.oarr
  | orcd => exact Ordinary.orcd
  | obrand => exact Ordinary.obrand
  | oor => exact Ordinary.oor
  | ovar => exact Ordinary.ovar
  | omu => exact Ordinary.omu
  | oallb => exact Ordinary.oallb
  | obvar =>
    simp only [bsubst]
    split
    · exact Ordinary.obrand
    · exact Ordinary.obvar

theorem nores_bsubst {d n : Nat} {A : Typ} (h : NoRes A) : NoRes (bsubst d n A) := by
  induction h generalizing d with
  | int => exact NoRes.int
  | top => exact NoRes.top
  | brand => exact NoRes.brand
  | arr _ _ ih₁ ih₂ => exact NoRes.arr ih₁ ih₂
  | rcd hne _ ih => exact NoRes.rcd hne ih
  | and _ _ ih₁ ih₂ => exact NoRes.and ih₁ ih₂
  | or _ _ ih₁ ih₂ => exact NoRes.or ih₁ ih₂
  | var => exact NoRes.var
  | mu _ ih => exact NoRes.mu ih
  | allb _ ih => exact NoRes.allb ih
  | bvar =>
    simp only [bsubst]
    split
    · exact NoRes.brand
    · exact NoRes.bvar

-- ── Expression-level substitution ────────────────────────────────────────────────────

theorem bsubstExp_value {n : Nat} : {d : Nat} → {v : Exp} → Value v
    → Value (bsubstExp d n v)
  | _, _, .vint => Value.vint
  | _, _, .vunit => Value.vunit
  | _, _, .vclos h => Value.vclos (bsubstExp_value h)
  | _, _, .vrcd h => Value.vrcd (bsubstExp_value h)
  | _, _, .vmrg h₁ h₂ => Value.vmrg (bsubstExp_value h₁) (bsubstExp_value h₂)
  | _, _, .vwrap h => Value.vwrap (bsubstExp_value h)
  | _, _, .vinl h => Value.vinl (bsubstExp_value h)
  | _, _, .vinr h => Value.vinr (bsubstExp_value h)
  | _, _, .vfold h => Value.vfold (bsubstExp_value h)
  | _, _, .vfclos h => Value.vfclos (bsubstExp_value h)
  | _, _, .vbclos h => Value.vbclos (bsubstExp_value h)

-- Generators commute with instantiation (both sides collapse to .unit at brand-variable
-- leaves, so the bvar ↦ brand replacement is invisible).
theorem bsubstExp_genVal {n : Nat} : (d : Nat) → (A : Typ)
    → bsubstExp d n (genVal A) = genVal (bsubst d n A)
  | _, .int => rfl
  | _, .top => rfl
  | d, .arr A B => by
    simp only [genVal, bsubstExp, bsubst, bsubstExp_genVal d B]
  | d, .and A B => by
    simp only [genVal, bsubstExp, bsubst, bsubstExp_genVal d A, bsubstExp_genVal d B]
  | d, .rcd l A => by
    simp only [genVal, bsubstExp, bsubst, bsubstExp_genVal d A]
  | _, .brand _ => rfl
  | _, .or _ _ => rfl
  | _, .var _ => rfl
  | _, .mu _ => rfl
  | _, .allb _ => rfl
  | d, .bvar i => by
    simp only [genVal, bsubstExp, bsubst]
    split <;> rfl

-- Casting commutes with instantiation.
theorem cast_bsubst {n : Nat} : {d : Nat} → {v : Exp} → {A : Typ} → {w : Exp}
    → Cast v A w → Cast (bsubstExp d n v) (bsubst d n A) (bsubstExp d n w)
  | _, _, _, _, .cint => Cast.cint
  | _, _, _, _, .ctop => Cast.ctop
  | _, _, _, _, .carrow hntl hsC hsB =>
    Cast.carrow (fun htl => hntl (toplike_bsubst_inv htl)) (sub_bsubst hsC) (sub_bsubst hsB)
  | d, _, _, _, .carrowtl htl hsC hsB => by
    simp only [bsubstExp, bsubst, bsubstExp_genVal]
    exact Cast.carrowtl (toplike_bsubst htl) (sub_bsubst hsC) (sub_bsubst hsB)
  | _, _, _, _, .cmrgl hord hc => Cast.cmrgl (ordinary_bsubst hord) (cast_bsubst hc)
  | _, _, _, _, .cmrgr hord hc => Cast.cmrgr (ordinary_bsubst hord) (cast_bsubst hc)
  | _, _, _, _, .cand h₁ h₂ => Cast.cand (cast_bsubst h₁) (cast_bsubst h₂)
  | _, _, _, _, .crcd h => Cast.crcd (cast_bsubst h)
  | _, _, _, _, .cwrap => Cast.cwrap
  | _, _, _, _, .cinl h => Cast.cinl (cast_bsubst h)
  | _, _, _, _, .cinr h => Cast.cinr (cast_bsubst h)
  | _, _, _, _, .cfold => Cast.cfold
  | _, _, _, _, .cfarrow hntl hsC hsB =>
    Cast.cfarrow (fun htl => hntl (toplike_bsubst_inv htl)) (sub_bsubst hsC) (sub_bsubst hsB)
  | d, _, _, _, .cfarrowtl htl hsC hsB => by
    simp only [bsubstExp, bsubst, bsubstExp_genVal]
    exact Cast.cfarrowtl (toplike_bsubst htl) (sub_bsubst hsC) (sub_bsubst hsB)
  | _, _, _, _, .cbclos => Cast.cbclos

-- ── The sealing/μ/∀ commutation toolkit ──────────────────────────────────────────────

-- substBrand of bvar-free arguments is bvar-free.
theorem hasbvar_substBrand {n : Nat} {R : Typ} : {S : Typ} → ¬ HasBVar R → ¬ HasBVar S
    → ¬ HasBVar (substBrand n R S)
  | .int, _, _ => fun h => nomatch h
  | .top, _, _ => fun h => nomatch h
  | .var _, _, _ => fun h => nomatch h
  | .bvar _, _, hS => absurd HasBVar.bvar hS
  | .brand m, hR, _ => by
    simp only [substBrand]
    split
    · exact hR
    · exact fun h => nomatch h
  | .arr A B, hR, hS => fun h => by
    simp only [substBrand] at h
    cases h with
    | arrl h' => exact hasbvar_substBrand hR (fun x => hS (HasBVar.arrl x)) h'
    | arrr h' => exact hasbvar_substBrand hR (fun x => hS (HasBVar.arrr x)) h'
  | .and A B, hR, hS => fun h => by
    simp only [substBrand] at h
    cases h with
    | andl h' => exact hasbvar_substBrand hR (fun x => hS (HasBVar.andl x)) h'
    | andr h' => exact hasbvar_substBrand hR (fun x => hS (HasBVar.andr x)) h'
  | .rcd l A, hR, hS => fun h => by
    simp only [substBrand] at h
    cases h with
    | rcd h' => exact hasbvar_substBrand hR (fun x => hS (HasBVar.rcd x)) h'
  | .or A B, hR, hS => fun h => by
    simp only [substBrand] at h
    cases h with
    | orl h' => exact hasbvar_substBrand hR (fun x => hS (HasBVar.orl x)) h'
    | orr h' => exact hasbvar_substBrand hR (fun x => hS (HasBVar.orr x)) h'
  | .mu T, hR, hS => fun h => by
    simp only [substBrand] at h
    cases h with
    | mu h' => exact hasbvar_substBrand hR (fun x => hS (HasBVar.mu x)) h'
  | .allb A, hR, hS => fun h => by
    simp only [substBrand] at h
    cases h with
    | allb h' => exact hasbvar_substBrand hR (fun x => hS (HasBVar.allb x)) h'

-- Instantiation never creates ∀-types.
theorem allbin_bsubst_inv {n : Nat} : {d : Nat} → {T : Typ} → AllbIn (bsubst d n T)
    → AllbIn T
  | _, .allb _, _ => AllbIn.self
  | _, .int, h => nomatch h
  | _, .top, h => nomatch h
  | _, .brand _, h => nomatch h
  | _, .var _, h => nomatch h
  | _, .bvar _, h => by simp only [bsubst] at h; split at h <;> nomatch h
  | _, .arr A B, h => by
    simp only [bsubst] at h
    cases h with
    | arrl h' => exact AllbIn.arrl (allbin_bsubst_inv h')
    | arrr h' => exact AllbIn.arrr (allbin_bsubst_inv h')
  | _, .and A B, h => by
    simp only [bsubst] at h
    cases h with
    | andl h' => exact AllbIn.andl (allbin_bsubst_inv h')
    | andr h' => exact AllbIn.andr (allbin_bsubst_inv h')
  | _, .rcd l A, h => by
    simp only [bsubst] at h
    cases h with
    | rcd h' => exact AllbIn.rcd (allbin_bsubst_inv h')
  | _, .or A B, h => by
    simp only [bsubst] at h
    cases h with
    | orl h' => exact AllbIn.orl (allbin_bsubst_inv h')
    | orr h' => exact AllbIn.orr (allbin_bsubst_inv h')
  | _, .mu T, h => by
    simp only [bsubst] at h
    cases h with
    | mu h' => exact AllbIn.mu (allbin_bsubst_inv h')

-- Under the ¬AllbIn fence, bsubst never crosses a ∀ inside T, so the μ-unfolding
-- substitution and instantiation commute at a single depth.
theorem bsubst_substTyp_comm {d n : Nat} : {k : Nat} → {S T : Typ} → ¬ AllbIn T
    → bsubst d n (substTyp k S T) = substTyp k (bsubst d n S) (bsubst d n T)
  | _, _, .int, _ => rfl
  | _, _, .top, _ => rfl
  | _, _, .brand _, _ => rfl
  | k, S, .var m, _ => by
    by_cases h : m = k
    · simp only [substTyp, bsubst, h, if_true]
    · simp only [substTyp, bsubst, h, if_false]
  | k, S, .bvar i, _ => by
    simp only [substTyp, bsubst]
    split <;> rfl
  | k, S, .arr A B, hna => by
    simp only [substTyp, bsubst,
      bsubst_substTyp_comm (fun h => hna (AllbIn.arrl h)),
      bsubst_substTyp_comm (fun h => hna (AllbIn.arrr h))]
  | k, S, .and A B, hna => by
    simp only [substTyp, bsubst,
      bsubst_substTyp_comm (fun h => hna (AllbIn.andl h)),
      bsubst_substTyp_comm (fun h => hna (AllbIn.andr h))]
  | k, S, .rcd l A, hna => by
    simp only [substTyp, bsubst, bsubst_substTyp_comm (fun h => hna (AllbIn.rcd h))]
  | k, S, .or A B, hna => by
    simp only [substTyp, bsubst,
      bsubst_substTyp_comm (fun h => hna (AllbIn.orl h)),
      bsubst_substTyp_comm (fun h => hna (AllbIn.orr h))]
  | k, S, .mu T, hna => by
    simp only [substTyp, bsubst, bsubst_substTyp_comm (fun h => hna (AllbIn.mu h))]
  | _, _, .allb _, hna => absurd AllbIn.self hna

-- Properly-bound types are invariant under substitution at or above the cutoff.
theorem bclosed_bsubst {n : Nat} : {c d : Nat} → {A : Typ} → BClosed c A → c ≤ d
    → bsubst d n A = A
  | _, _, _, .int, _ => rfl
  | _, _, _, .top, _ => rfl
  | _, _, _, .brand, _ => rfl
  | _, _, _, .var, _ => rfl
  | _, _, _, .bvar hi, hcd => by
    simp only [bsubst]
    split
    · next h => exact absurd (h ▸ hi) (Nat.not_lt.mpr (Nat.le_of_lt_succ (Nat.lt_succ_of_le hcd)))
    · rfl
  | _, _, _, .arr h₁ h₂, hcd => by
    simp only [bsubst, bclosed_bsubst h₁ hcd, bclosed_bsubst h₂ hcd]
  | _, _, _, .and h₁ h₂, hcd => by
    simp only [bsubst, bclosed_bsubst h₁ hcd, bclosed_bsubst h₂ hcd]
  | _, _, _, .rcd h, hcd => by
    simp only [bsubst, bclosed_bsubst h hcd]
  | _, _, _, .or h₁ h₂, hcd => by
    simp only [bsubst, bclosed_bsubst h₁ hcd, bclosed_bsubst h₂ hcd]
  | _, _, _, .mu h, hcd => by
    simp only [bsubst, bclosed_bsubst h hcd]
  | _, _, _, .allb h, hcd => by
    simp only [bsubst, bclosed_bsubst h (Nat.succ_le_succ hcd)]

-- Instantiating the top allowed index lowers the cutoff.
theorem bclosed_bsubst_lower {n : Nat} : {c : Nat} → {A : Typ} → BClosed (c + 1) A
    → BClosed c (bsubst c n A)
  | _, _, .int => BClosed.int
  | _, _, .top => BClosed.top
  | _, _, .brand => BClosed.brand
  | _, _, .var => BClosed.var
  | c, _, .bvar hi => by
    simp only [bsubst]
    split
    · exact BClosed.brand
    · next hne => exact BClosed.bvar (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi) hne)
  | _, _, .arr h₁ h₂ => BClosed.arr (bclosed_bsubst_lower h₁) (bclosed_bsubst_lower h₂)
  | _, _, .and h₁ h₂ => BClosed.and (bclosed_bsubst_lower h₁) (bclosed_bsubst_lower h₂)
  | _, _, .rcd h => BClosed.rcd (bclosed_bsubst_lower h)
  | _, _, .or h₁ h₂ => BClosed.or (bclosed_bsubst_lower h₁) (bclosed_bsubst_lower h₂)
  | _, _, .mu h => BClosed.mu (bclosed_bsubst_lower h)
  | _, _, .allb h => BClosed.allb (bclosed_bsubst_lower h)

-- ── Simultaneous instantiation environments (milestone 4 infrastructure) ─────────────

-- Insert an entry into a de Bruijn environment at position p (indices below p keep
-- their entries, p reads the new one, the rest shift up).
def bvInsert {α : Sort _} (p : Nat) (x : α) (σ : Nat → α) : Nat → α :=
  fun i => if i < p then σ i else if i = p then x else σ (i - 1)

theorem bsubstEnv_notin {σ : Nat → Nat} : {d : Nat} → {T : Typ} → ¬ HasBVar T
    → bsubstEnv σ d T = T
  | _, .int, _ => rfl
  | _, .top, _ => rfl
  | _, .brand _, _ => rfl
  | _, .var _, _ => rfl
  | _, .bvar _, h => absurd HasBVar.bvar h
  | _, .arr A B, h => by
    simp only [bsubstEnv, bsubstEnv_notin (fun h' => h (HasBVar.arrl h')),
      bsubstEnv_notin (fun h' => h (HasBVar.arrr h'))]
  | _, .and A B, h => by
    simp only [bsubstEnv, bsubstEnv_notin (fun h' => h (HasBVar.andl h')),
      bsubstEnv_notin (fun h' => h (HasBVar.andr h'))]
  | _, .rcd l A, h => by
    simp only [bsubstEnv, bsubstEnv_notin (fun h' => h (HasBVar.rcd h'))]
  | _, .or A B, h => by
    simp only [bsubstEnv, bsubstEnv_notin (fun h' => h (HasBVar.orl h')),
      bsubstEnv_notin (fun h' => h (HasBVar.orr h'))]
  | _, .mu T, h => by
    simp only [bsubstEnv, bsubstEnv_notin (fun h' => h (HasBVar.mu h'))]
  | _, .allb A, h => by
    simp only [bsubstEnv, bsubstEnv_notin (fun h' => h (HasBVar.allb h'))]

-- Properly-bound types below the cutoff are environment-invariant.
theorem bclosed_bsubstEnv {σ : Nat → Nat} : {c d : Nat} → {T : Typ} → BClosed c T
    → c ≤ d → bsubstEnv σ d T = T
  | _, _, _, .int, _ => rfl
  | _, _, _, .top, _ => rfl
  | _, _, _, .brand, _ => rfl
  | _, _, _, .var, _ => rfl
  | _, _, _, .bvar hi, hcd => by
    simp only [bsubstEnv, if_pos (Nat.lt_of_lt_of_le hi hcd)]
  | _, _, _, .arr h₁ h₂, hcd => by
    simp only [bsubstEnv, bclosed_bsubstEnv h₁ hcd, bclosed_bsubstEnv h₂ hcd]
  | _, _, _, .and h₁ h₂, hcd => by
    simp only [bsubstEnv, bclosed_bsubstEnv h₁ hcd, bclosed_bsubstEnv h₂ hcd]
  | _, _, _, .rcd h, hcd => by
    simp only [bsubstEnv, bclosed_bsubstEnv h hcd]
  | _, _, _, .or h₁ h₂, hcd => by
    simp only [bsubstEnv, bclosed_bsubstEnv h₁ hcd, bclosed_bsubstEnv h₂ hcd]
  | _, _, _, .mu h, hcd => by
    simp only [bsubstEnv, bclosed_bsubstEnv h hcd]
  | _, _, _, .allb h, hcd => by
    simp only [bsubstEnv, bclosed_bsubstEnv h (Nat.succ_le_succ hcd)]

-- THE environment/single-point compatibility equation: inserting brand m at position p
-- of the environment is the same as first instantiating the (p+d)-th binder at m.  The
-- properly-bound hypothesis rules out the indices the shift-free bsubst would misalign.
theorem bsubstEnv_insert {m : Nat} {σ : Nat → Nat} : {p d : Nat} → {T : Typ}
    → BClosed (p + 1 + d) T
    → bsubstEnv (bvInsert p m σ) d T = bsubstEnv σ d (bsubst (p + d) m T)
  | _, _, _, .int => rfl
  | _, _, _, .top => rfl
  | _, _, _, .brand => rfl
  | _, _, _, .var => rfl
  | p, d, _, .bvar hi => by
    rename_i i
    simp only [bsubst, bsubstEnv]
    by_cases hid : i < d
    · rw [if_pos hid, if_neg (by omega : ¬ i = p + d)]
      simp only [bsubstEnv, if_pos hid]
    · rw [if_neg hid]
      by_cases hip : i = p + d
      · rw [if_pos hip, bvInsert, if_neg (by omega : ¬ i - d < p), if_pos (by omega)]
        rfl
      · rw [if_neg hip]
        simp only [bsubstEnv, if_neg hid]
        rw [bvInsert, if_pos (by omega : i - d < p)]
  | p, d, _, .arr h₁ h₂ => by
    simp only [bsubst, bsubstEnv, bsubstEnv_insert h₁, bsubstEnv_insert h₂]
  | p, d, _, .and h₁ h₂ => by
    simp only [bsubst, bsubstEnv, bsubstEnv_insert h₁, bsubstEnv_insert h₂]
  | p, d, _, .rcd h => by
    simp only [bsubst, bsubstEnv, bsubstEnv_insert h]
  | p, d, _, .or h₁ h₂ => by
    simp only [bsubst, bsubstEnv, bsubstEnv_insert h₁, bsubstEnv_insert h₂]
  | p, d, _, .mu h => by
    simp only [bsubst, bsubstEnv, bsubstEnv_insert h]
  | p, d, _, .allb h => by
    simp only [bsubst, bsubstEnv, bsubstEnv_insert (p := p) (d := d + 1) h]
    rfl

-- Subtyping is stable under simultaneous instantiation (refl leaves stay refl).
theorem sub_bsubstEnv {σ : Nat → Nat} {d : Nat} {A B : Typ} (h : Sub A B)
    : Sub (bsubstEnv σ d A) (bsubstEnv σ d B) := by
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

-- ── THE substitution lemma ───────────────────────────────────────────────────────────

-- ∀β-instantiation preserves typing.  The tmergev case survives via disj_bsubst (the
-- whole point of the conservative COST rules); the tmergevc case rebuilds its
-- consistency SEMANTICALLY: the substituted components are casts (cast_bsubst) of the
-- substituted origin, so consistent_after_cast applies.  Sealing/wrapping annotations
-- are invariant (bvar-free by the tseal/twrap discipline); μ commutes under the
-- ¬AllbIn fence; the ∀ rules recurse one binder deeper on bvar-free contexts.
theorem hastype_bsubst {Δ : BrandStore} {n : Nat} {Γ : Typ} {e : Exp} {A : Typ}
    (ht : HasType Δ Γ e A) : ∀ {d : Nat},
    HasType Δ (bsubst d n Γ) (bsubstExp d n e) (bsubst d n A) := by
  induction ht with
  | tquery => intro d; exact HasType.tquery
  | tint => intro d; exact HasType.tint
  | tunit => intro d; exact HasType.tunit
  | tapp _ _ ih₁ ih₂ => intro d; exact HasType.tapp ih₁ ih₂
  | tbox _ _ ih₁ ih₂ => intro d; exact HasType.tbox ih₁ ih₂
  | tproj _ hl ih => intro d; exact HasType.tproj ih (lookup_bsubst hl)
  | trcd _ ih => intro d; exact HasType.trcd ih
  | trproj _ hl ih => intro d; exact HasType.trproj ih (rlookup_bsubst hl)
  | tmrg _ _ hd₁ hd₂ ih₁ ih₂ =>
    intro d
    exact HasType.tmrg ih₁ ih₂ (disj_bsubst hd₁) (disj_bsubst hd₂)
  | tmergev hv₁ hv₂ _ _ hd _ ih₁ ih₂ =>
    intro d
    exact HasType.tmergev (bsubstExp_value hv₁) (bsubstExp_value hv₂) ih₁ ih₂
      (disj_bsubst hd)
      (disjoint_consistent (bsubstExp_value hv₁) (bsubstExp_value hv₂) ih₁ ih₂
        (disj_bsubst hd))
  | tmergevc hv₁ hv₂ _ _ hv _ hc₁ hc₂ _ ih₁ ih₂ ih =>
    intro d
    exact HasType.tmergevc (bsubstExp_value hv₁) (bsubstExp_value hv₂) ih₁ ih₂
      (bsubstExp_value hv) ih (cast_bsubst hc₁) (cast_bsubst hc₂)
      (consistent_after_cast (bsubstExp_value hv) ih (cast_bsubst hc₁) (cast_bsubst hc₂))
  | tlam hd _ ih => intro d; exact HasType.tlam (disj_bsubst hd) ih
  | tclos hv _ hd _ hs₁ hs₂ ih₁ ih₂ =>
    intro d
    exact HasType.tclos (bsubstExp_value hv) ih₁ (disj_bsubst hd) ih₂
      (sub_bsubst hs₁) (sub_bsubst hs₂)
  | tanno _ hs ih => intro d; exact HasType.tanno ih (sub_bsubst hs)
  | twrap hΔ hnb hv _ ih =>
    intro d
    have ih' := ih (d := d)
    rw [bsubst_notin hnb] at ih'
    exact HasType.twrap hΔ hnb (bsubstExp_value hv) ih'
  | tseal hΔ hnr hnb hwf _ ih =>
    intro d
    have hS := wfsig_no_hasbvar hwf
    have ih' := ih (d := d)
    rw [bsubst_notin (hasbvar_substBrand hnb hS)] at ih'
    simp only [bsubstExp]
    rw [bsubst_notin hnb, bsubst_notin hS]
    exact HasType.tseal hΔ hnr hnb hwf ih'
  | tunseal hΔ hnr hnb hwf _ heq ih =>
    intro d
    have hS := wfsig_no_hasbvar hwf
    subst heq
    have ih' := ih (d := d)
    rw [bsubst_notin hS] at ih'
    simp only [bsubstExp]
    rw [bsubst_notin hnb, bsubst_notin hS]
    exact HasType.tunseal hΔ hnr hnb hwf ih'
      (bsubst_notin (hasbvar_substBrand hnb hS))
  | tinl _ ih => intro d; exact HasType.tinl ih
  | tinr _ ih => intro d; exact HasType.tinr ih
  | tcase _ hd₁ hd₂ _ _ ih ih₁ ih₂ =>
    intro d
    exact HasType.tcase ih (disj_bsubst hd₁) (disj_bsubst hd₂) ih₁ ih₂
  | tfold hna _ ih =>
    intro d
    have ih' := ih (d := d)
    rw [bsubst_substTyp_comm hna] at ih'
    exact HasType.tfold (fun h => hna (allbin_bsubst_inv h)) ih'
  | tunfold hna _ heq ih =>
    intro d
    subst heq
    exact HasType.tunfold (fun h => hna (allbin_bsubst_inv h)) ih
      (bsubst_substTyp_comm hna)
  | tflam hd₁ hd₂ _ ih =>
    intro d
    exact HasType.tflam (disj_bsubst hd₁) (disj_bsubst hd₂) ih
  | tfclos hv _ hd₁ hd₂ _ hs₁ hs₂ hs₃ ih₁ ih₂ =>
    intro d
    exact HasType.tfclos (bsubstExp_value hv) ih₁ (disj_bsubst hd₁) (disj_bsubst hd₂) ih₂
      (sub_bsubst hs₁) (sub_bsubst hs₂) (sub_bsubst hs₃)
  | tblam hnb _ ih =>
    intro d
    simp only [bsubstExp]
    rw [bsubst_notin (T := _) hnb]
    refine HasType.tblam hnb ?_
    have ih' := ih (d := d + 1)
    rwa [bsubst_notin hnb] at ih'
  | tbclos hv _ hnb _ ih₁ ih₂ =>
    intro d
    simp only [bsubstExp]
    refine HasType.tbclos (bsubstExp_value hv) ?_ hnb ?_
    · have ih' := ih₁ (d := d)
      rwa [bsubst_notin hnb] at ih'
    · have ih' := ih₂ (d := d + 1)
      rwa [bsubst_notin hnb] at ih'
  | tbapp _ hbc heq ih =>
    intro d
    subst heq
    -- BClosed 1 A: the outer substitution misses both A and its instantiation.
    rw [bclosed_bsubst (bclosed_bsubst_lower hbc) (Nat.zero_le d)]
    refine HasType.tbapp (A := bsubst (d + 1) n _) ih ?_ ?_
    · rw [bclosed_bsubst hbc (Nat.succ_le_succ (Nat.zero_le d))]
      exact hbc
    · rw [bclosed_bsubst hbc (Nat.succ_le_succ (Nat.zero_le d))]

end Seal
