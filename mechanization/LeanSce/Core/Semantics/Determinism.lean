import LeanSce.Core.Syntax
import LeanSce.Core.Typing.Typing
import LeanSce.Core.Semantics.SmallStep
import LeanSce.Core.Properties

/-!
Determinism of the Core small-step semantics for well-typed terms.

Typing is needed only for record selection: on an ill-typed merge carrying the
same label on both sides, `RLookupV` may pick either side.  The disjointness
built into `RLookup` (via `notin_false`) rules that out.
-/

open Core

/-- Core values do not step. -/
theorem core_value_no_step {v : Exp} (hv : Value v) :
    ∀ {ρ e : Exp}, ¬ Step ρ v e := by
  induction hv with
  | vint => intro _ _ hs; nomatch hs
  | vunit => intro _ _ hs; nomatch hs
  | vclos _ => intro _ _ hs; nomatch hs
  | vrcd _ ih => intro _ _ hs; cases hs with | slrec _ h => exact ih h
  | vmrg _ _ ih1 ih2 =>
    intro _ _ hs
    cases hs with
    | smrgl _ h => exact ih1 h
    | smrgr _ _ h => exact ih2 h
  | vinl _ ih => intro _ _ hs; cases hs with | sinl _ h => exact ih h
  | vinr _ ih => intro _ _ hs; cases hs with | sinr _ h => exact ih h
  | vfclos _ => intro _ _ hs; nomatch hs
  | vfold _ ih => intro _ _ hs; cases hs with | sfold _ h => exact ih h

theorem core_lookupv_det {v v1 v2 : Exp} {n : Nat}
    (h1 : LookupV v n v1) (h2 : LookupV v n v2) : v1 = v2 := by
  induction h1 generalizing v2 with
  | lvzero => cases h2; rfl
  | lvsucc _ ih => cases h2 with | lvsucc h2' => exact ih h2'

theorem core_rlookupv_det {E v A l B v1 v2}
    (ht : HasType E v A) (hrl : RLookup A l B)
    (h1 : RLookupV v l v1) (h2 : RLookupV v l v2) : v1 = v2 := by
  induction h1 generalizing E A B v2 with
  | rvlzero => cases h2; rfl
  | vlandl h ih =>
    cases ht with
    | tmrg t1 t2 =>
      cases h2 with
      | vlandl h' =>
        cases hrl with
        | landl hrl' _ => exact ih t1 hrl' h'
        | landr _ hnl => exact (notin_false t1 _ _ h hnl).elim
      | vlandr h' =>
        cases hrl with
        | landl _ hnl => exact (notin_false t2 _ _ h' hnl).elim
        | landr _ hnl => exact (notin_false t1 _ _ h hnl).elim
  | vlandr h ih =>
    cases ht with
    | tmrg t1 t2 =>
      cases h2 with
      | vlandr h' =>
        cases hrl with
        | landr hrl' _ => exact ih t2 hrl' h'
        | landl _ hnl => exact (notin_false t2 _ _ h hnl).elim
      | vlandl h' =>
        cases hrl with
        | landl _ hnl => exact (notin_false t2 _ _ h hnl).elim
        | landr _ hnl => exact (notin_false t1 _ _ h' hnl).elim

/-- **Determinism of Core small steps** for well-typed terms in a well-typed
environment. -/
theorem core_step_deterministic {ρ e e1 : Exp} (hs : Step ρ e e1) :
    ∀ {e2 : Exp} {E A : Typ}, Step ρ e e2 → HasType E e A → HasType .top ρ E → e1 = e2 := by
  induction hs with
  | squery _ => intro _ _ _ hs2 _ _; cases hs2; rfl
  | sappl _ h ih =>
    intro _ _ _ hs2 ht hρ
    cases ht with
    | tapp t1 _ =>
      cases hs2 with
      | sappl _ h' => rw [ih h' t1 hρ]
      | sappr _ hv1 _ => exact absurd h (core_value_no_step hv1)
      | sbeta _ _ hv2 => exact absurd h (core_value_no_step (Value.vclos hv2))
      | sfbeta _ _ hv2 => exact absurd h (core_value_no_step (Value.vfclos hv2))
  | sboxl _ h ih =>
    intro _ _ _ hs2 ht hρ
    cases ht with
    | tbox t1 _ =>
      cases hs2 with
      | sboxl _ h' => rw [ih h' t1 hρ]
      | sboxr _ hv1 _ => exact absurd h (core_value_no_step hv1)
      | sboxv _ hv1 _ => exact absurd h (core_value_no_step hv1)
  | smrgl _ h ih =>
    intro _ _ _ hs2 ht hρ
    cases ht with
    | tmrg t1 _ =>
      cases hs2 with
      | smrgl _ h' => rw [ih h' t1 hρ]
      | smrgr _ hv1 _ => exact absurd h (core_value_no_step hv1)
  | sappr _ hv1 h ih =>
    intro _ _ _ hs2 ht hρ
    cases ht with
    | tapp _ t2 =>
      cases hs2 with
      | sappl _ h' => exact absurd h' (core_value_no_step hv1)
      | sappr _ _ h' => rw [ih h' t2 hρ]
      | sbeta _ hv1' _ => exact absurd h (core_value_no_step hv1')
      | sfbeta _ hv1' _ => exact absurd h (core_value_no_step hv1')
  | sboxr _ hv1 h ih =>
    intro _ _ _ hs2 ht _
    cases ht with
    | tbox t1 t2 =>
      cases hs2 with
      | sboxl _ h' => exact absurd h' (core_value_no_step hv1)
      | sboxr _ _ h' => rw [ih h' t2 (value_weaken t1 hv1)]
      | sboxv _ _ hv2 => exact absurd h (core_value_no_step hv2)
  | smrgr _ hv1 h ih =>
    intro _ _ _ hs2 ht hρ
    cases ht with
    | tmrg t1 t2 =>
      cases hs2 with
      | smrgl _ h' => exact absurd h' (core_value_no_step hv1)
      | smrgr _ _ h' => rw [ih h' t2 (HasType.tmrg hρ (value_weaken t1 hv1))]
  | sclos _ => intro _ _ _ hs2 _ _; cases hs2; rfl
  | sbeta _ hv1 hv2 =>
    intro _ _ _ hs2 _ _
    cases hs2 with
    | sappl _ h' => exact absurd h' (core_value_no_step (Value.vclos hv2))
    | sappr _ _ h' => exact absurd h' (core_value_no_step hv1)
    | sbeta => rfl
  | sboxv _ hv1 hv2 =>
    intro _ _ _ hs2 _ _
    cases hs2 with
    | sboxl _ h' => exact absurd h' (core_value_no_step hv1)
    | sboxr _ _ h' => exact absurd h' (core_value_no_step hv2)
    | sboxv => rfl
  | sproj _ h ih =>
    intro _ _ _ hs2 ht hρ
    cases ht with
    | tproj t1 _ =>
      cases hs2 with
      | sproj _ h' => rw [ih h' t1 hρ]
      | sprojv _ hv1 _ => exact absurd h (core_value_no_step hv1)
  | sprojv _ hv1 hl =>
    intro _ _ _ hs2 _ _
    cases hs2 with
    | sproj _ h' => exact absurd h' (core_value_no_step hv1)
    | sprojv _ _ hl' => exact core_lookupv_det hl hl'
  | slrec _ h ih =>
    intro _ _ _ hs2 ht hρ
    cases ht with
    | trcd t1 =>
      cases hs2 with
      | slrec _ h' => rw [ih h' t1 hρ]
  | srproj _ h ih =>
    intro _ _ _ hs2 ht hρ
    cases ht with
    | trproj t1 _ =>
      cases hs2 with
      | srproj _ h' => rw [ih h' t1 hρ]
      | srprojv _ hv1 _ => exact absurd h (core_value_no_step hv1)
  | srprojv _ hv1 hrl =>
    intro _ _ _ hs2 ht _
    cases ht with
    | trproj t1 hrlk =>
      cases hs2 with
      | srproj _ h' => exact absurd h' (core_value_no_step hv1)
      | srprojv _ _ hrl' => exact core_rlookupv_det t1 hrlk hrl hrl'
  | sinl _ h ih =>
    intro _ _ _ hs2 ht hρ
    cases ht with
    | tinl t1 =>
      cases hs2 with
      | sinl _ h' => rw [ih h' t1 hρ]
  | sinr _ h ih =>
    intro _ _ _ hs2 ht hρ
    cases ht with
    | tinr t1 =>
      cases hs2 with
      | sinr _ h' => rw [ih h' t1 hρ]
  | scase _ h ih =>
    intro _ _ _ hs2 ht hρ
    cases ht with
    | tcase t1 _ _ =>
      cases hs2 with
      | scase _ h' => rw [ih h' t1 hρ]
      | scasel _ hv1 => exact absurd h (core_value_no_step (Value.vinl hv1))
      | scaser _ hv1 => exact absurd h (core_value_no_step (Value.vinr hv1))
  | scasel _ hv1 =>
    intro _ _ _ hs2 _ _
    cases hs2 with
    | scase _ h' => exact absurd h' (core_value_no_step (Value.vinl hv1))
    | scasel => rfl
  | scaser _ hv1 =>
    intro _ _ _ hs2 _ _
    cases hs2 with
    | scase _ h' => exact absurd h' (core_value_no_step (Value.vinr hv1))
    | scaser => rfl
  | sfclos _ => intro _ _ _ hs2 _ _; cases hs2; rfl
  | sfbeta _ hv1 hv2 =>
    intro _ _ _ hs2 _ _
    cases hs2 with
    | sappl _ h' => exact absurd h' (core_value_no_step (Value.vfclos hv2))
    | sappr _ _ h' => exact absurd h' (core_value_no_step hv1)
    | sfbeta => rfl
  | sfold _ h ih =>
    intro _ _ _ hs2 ht hρ
    cases ht with
    | tfold t1 =>
      cases hs2 with
      | sfold _ h' => rw [ih h' t1 hρ]
  | sunfold _ h ih =>
    intro _ _ _ hs2 ht hρ
    cases ht with
    | tunfold t1 _ =>
      cases hs2 with
      | sunfold _ h' => rw [ih h' t1 hρ]
      | sunfoldv _ hv1 => exact absurd h (core_value_no_step (Value.vfold hv1))
  | sunfoldv _ hv1 =>
    intro _ _ _ hs2 _ _
    cases hs2 with
    | sunfold _ h' => exact absurd h' (core_value_no_step (Value.vfold hv1))
    | sunfoldv => rfl
