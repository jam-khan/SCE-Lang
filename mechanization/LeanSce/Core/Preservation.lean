import LeanSce.Core.Syntax
import LeanSce.Core.Typing.Typing
import LeanSce.Core.Semantics.SmallStep
import LeanSce.Core.Properties

open Core

@[simp]
theorem gpreservation
  {e e' v : Exp}
  (hstep : Step v e e') :
  ∀ {E A : Typ},
  HasType E e A
  → HasType .top v E
  → HasType E e' A
  := by
  induction hstep with
  | squery heval =>
    rename_i v
    intro E A htype henv
    cases htype
    apply value_weaken; try assumption
    assumption
  | sappl hv hstep ih1 =>
    rename_i v v' e1 e2
    intro E A htype henv
    cases htype with
    | tapp ht1 ht2 =>
      apply HasType.tapp
      · exact ih1 ht1 henv
      · assumption
  | sboxl hv hstep ih1 =>
    rename_i v1 v2 v3 v4
    intro E A htype henv
    cases htype with
    | tbox ih2 ih3 =>
      rename_i Γ₁
      apply HasType.tbox <;> try assumption
      apply ih1
      repeat assumption
  | smrgl hv hstep ih1 =>
    rename_i v1 v2 v3 v4
    intro E A htype henv
    cases htype with
    | tmrg ih2 ih3 =>
        rename_i A B
        apply HasType.tmrg <;> try apply ih1
        repeat assumption
  | sappr hv hv1 hstep ih1 =>
    rename_i v1 v2 v3 v4
    intro E A htype henv
    cases htype with
    | tapp ht1 ht2 =>
      apply HasType.tapp
      · assumption
      · apply ih1<;> assumption
  | sboxr hv hstep ih1 ih2 =>
    rename_i v1 v2 v3 v4
    intro E A htype henv
    cases htype with
    | tbox ih3 ih4 =>
      rename_i Γ₁
      apply HasType.tbox <;> try assumption
      apply ih2
      repeat assumption
      apply value_weaken <;> try assumption
  | smrgr hv1 hv2 hstep ih1 =>
    rename_i v1 v2 v3 v4
    intro E A htype henv
    cases htype with
    | tmrg ih2 ih3 =>
        rename_i A B
        apply HasType.tmrg
        · assumption
        · apply ih1
          · assumption
          · apply HasType.tmrg
            · assumption
            · exact value_weaken ih2 hv2
  | sclos hv =>
    rename_i v1 v2 A
    intro E A htype henv
    rename_i e2
    cases htype with
    | tlam ih =>
      rename_i B
      apply HasType.tclos <;> try assumption
  | sbeta hv hv1 hv2 =>
    intro E A htype henv
    rename_i v1 v2 v3 B e1
    cases htype with
    | tapp ih1 ih2 =>
      cases ih1 with
      | tclos hv' ht' hb =>
        rename_i Γ₁
        apply HasType.tbox <;> try assumption
        apply HasType.tmrg
        · exact value_weaken ht' hv2
        · exact value_weaken ih2 hv1
  | sboxv hv1 hv2 hv3 =>
    intro E A htype henv
    rename_i v1 v2 v3
    cases htype with
    | tbox ih1 ih2 =>
      rename_i Γ₁
      apply value_weaken ih2 hv3
  | sproj hv hstep ih =>
    rename_i v1 e1 e2 n
    intro E A htype henv
    cases htype with
    | tproj ht hl =>
      exact HasType.tproj (ih ht henv) hl
  | sprojv hv1 hv2 hlook =>
    rename_i v1 v2 v3 v4
    intro E A htype henv
    cases htype with
    | tproj ht hl =>
      rename_i A'
      obtain h1 := lookupv_value hlook
      obtain h2 := h1 hv2
      exact value_weaken (lookup_pres hl v2 v4 hlook hv2 (value_weaken ht hv2)) h2
  | slrec hv hstep ih1 =>
    rename_i v e1 e2 l
    intro E A htype henv
    cases htype
    rename_i A ih2
    apply HasType.trcd
    apply ih1
    repeat assumption
  | srproj hv hstep ih =>
    rename_i v1 e1 e2 l
    intro E A htype henv
    cases htype
    rename_i B ih2 hlook
    apply HasType.trproj <;> try assumption
    apply ih
    repeat assumption
  | srprojv hv hv1 hlook =>
    rename_i v' v1 l v2
    intro E A htype henv
    cases htype
    rename_i B ih2 hlook'
    exact value_weaken (rlookup_pres hlook' hlook hv1 (value_weaken ih2 hv1)) (rlookupv_value hlook hv1)
  | sinl hv hstep ih =>
    intro E A htype henv
    cases htype with
    | tinl ht => exact HasType.tinl (ih ht henv)
  | sinr hv hstep ih =>
    intro E A htype henv
    cases htype with
    | tinr ht => exact HasType.tinr (ih ht henv)
  | scase hv hstep ih =>
    intro E A htype henv
    cases htype with
    | tcase ht h1 h2 => exact HasType.tcase (ih ht henv) h1 h2
  | scasel hv hv1 =>
    intro E A htype henv
    cases htype with
    | tcase hinl h1 h2 =>
      cases hinl with
      | tinl ht1 =>
        exact HasType.tbox (HasType.tmrg (value_weaken henv hv) (value_weaken ht1 hv1)) h1
  | scaser hv hv1 =>
    intro E A htype henv
    cases htype with
    | tcase hinr h1 h2 =>
      cases hinr with
      | tinr ht1 =>
        exact HasType.tbox (HasType.tmrg (value_weaken henv hv) (value_weaken ht1 hv1)) h2
  | sfclos hv =>
    intro E A htype henv
    cases htype with
    | tflam h => exact HasType.tfclos hv henv h
  | sfbeta hv hv1 hv2 =>
    intro E A htype henv
    cases htype with
    | tapp ih1 ih2 =>
      cases ih1 with
      | tfclos hv' ht' hb =>
        exact HasType.tbox
          (HasType.tmrg
            (HasType.tmrg (value_weaken ht' hv2) (HasType.tfclos hv' ht' hb))
            (value_weaken ih2 hv1))
          hb
  | sfold hv hstep ih =>
    intro E A htype henv
    cases htype with
    | tfold ht => exact HasType.tfold (ih ht henv)
  | sunfold hv hstep ih =>
    intro E A htype henv
    cases htype with
    | tunfold ht heq => exact HasType.tunfold (ih ht henv) heq
  | sunfoldv hv hv1 =>
    intro E A htype henv
    cases htype with
    | tunfold ht heq =>
      subst heq
      cases ht with
      | tfold ht1 => exact ht1

theorem preservation {e e' A}
  : HasType .top e A
  → Step .unit e e'
  → HasType .top e' A := by
  intros htyp hstep
  apply gpreservation <;> try assumption
  exact HasType.tunit
