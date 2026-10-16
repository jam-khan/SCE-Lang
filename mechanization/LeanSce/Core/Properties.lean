import LeanSce.Core.Syntax
import LeanSce.Core.Typing.Typing

/-!
Properties of typing and lookup shared by preservation and progress: value
weakening, and preservation/progress of positional and record lookup.
-/

open Core

@[simp]
theorem value_weaken
  {E A : Typ} { v : Exp} :
  HasType E v A →
  ∀ {E' : Typ},
    Value v
    → HasType E' v A := by
  intro htype
  induction htype with
  | tint          => intro _ _; exact .tint
  | tunit         => intro _ _; exact .tunit
  | trcd ht ih    => intro _ hv; cases hv; exact .trcd (ih ‹_›)
  | tlam _        => intro _ hv; cases hv
  | tquery        => intro _ hv; cases hv
  | tapp _ _      => intro _ hv; cases hv
  | tbox _ _      => intro _ hv; cases hv
  | tproj _ _     => intro _ hv; cases hv
  | trproj _ _    => intro _ hv; cases hv
  | tinl ht ih    => intro _ hv; cases hv; exact .tinl (ih ‹_›)
  | tinr ht ih    => intro _ hv; cases hv; exact .tinr (ih ‹_›)
  | tcase _ _ _   => intro _ hv; cases hv
  | tflam _       => intro _ hv; cases hv
  | tfclos hv' ht' hb ih1 ih2 =>
    intro E' hv
    apply HasType.tfclos <;> assumption
  | tfold ht ih   => intro _ hv; cases hv; exact .tfold (ih ‹_›)
  | tunfold _     => intro _ hv; cases hv
  | tmrg h1 h2 ih1 ih2 =>
    intro _ hv
    cases hv with
    | vmrg hv1 hv2 => exact .tmrg (ih1 hv1) (ih2 hv2)
  | tclos hv' ht' hb ih1 ih2 =>
    rename_i Γ₁ Γ₂ A' B' v₀ e₀
    intro E' hv
    apply HasType.tclos <;> assumption

@[simp]
theorem lookupv_value:
  ∀ {v v' : Exp} {n : Nat},
    LookupV v n v'
    → Value v
    → Value v' := by
  intro v v' n hlook hval
  induction hlook with
  | lvzero =>
    cases hval <;> try assumption
  | lvsucc =>
    cases hval with
    | vmrg hv1 _ =>
      rename_i v1 v2 v3 n ih11 ih12 hv2
      apply ih12
      assumption

@[simp]
theorem lookup_pres_ctx {E n A}:
  Lookup E n A
  → ∀ v v',
    LookupV v n v'
    → Value v
    → HasType .top v E
    → HasType E v' A := by
  intro hl
  induction hl with
  | zero =>
    intro v v' hlv hv ht
    cases hlv
    cases ht with
    | tmrg h1 h2 =>
      cases hv with
      | vmrg hv1 hv2 =>
        exact value_weaken h2 hv2
  | succ hl' ih =>
    intro v v' hlv hv ht
    cases hlv with
    | lvsucc hlv' =>
      cases ht with
      | tmrg h1 h2 =>
        cases hv with
        | vmrg hv1 hv2 =>
          rename_i v1 v2
          have h := ih v1 _ hlv' hv1 (value_weaken h1 hv1)
          exact value_weaken h (lookupv_value hlv' hv1)

@[simp]
theorem lookup_pres {E n A} :
  Lookup E n A
  → ∀ v v',
    LookupV v n v'
    → Value v
    → HasType .top v E
    → HasType .top v' A := by
  intro hl v v' hlv hv ht
  have h := lookup_pres_ctx hl v v' hlv hv ht
  exact value_weaken h (lookupv_value hlv hv)

@[simp]
theorem rlookupv_value {v l v'} :
  RLookupV v l v'
  → Value v
  → Value v' := by
  intro hl hv
  induction hl with
  | rvlzero => cases hv; assumption
  | vlandl _ ih => cases hv with
    | vmrg hv1 hv2 => exact ih hv1
  | vlandr _ ih => cases hv with
    | vmrg hv1 hv2 => exact ih hv2

@[simp]
theorem rcd_shape {E v l B} :
  HasType E v (.rcd l B)
  → Value v
  → ∃ v', v = .lrec l v' := by
  intro ht hv
  cases ht with
  | trcd => exact ⟨_, rfl⟩
  | tquery => cases hv
  | tapp _ _ => cases hv
  | tbox _ _ => cases hv
  | tproj _ _ => cases hv
  | trproj _ _ => cases hv
  | tcase _ _ _ => cases hv
  | tunfold _ => cases hv

@[simp]
theorem notin_false {E v A} :
  HasType E v A
  → ∀ l v',
      RLookupV v l v'
      → ¬ Lin l A
      → False := by
  intro ht
  induction ht with
  | tint => intro l v' hr; cases hr
  | tunit => intro l v' hr; cases hr
  | tquery => intro l v' hr; cases hr
  | tlam _ => intro l v' hr; cases hr
  | tapp _ _ => intro l v' hr; cases hr
  | tbox _ _ => intro l v' hr; cases hr
  | tproj _ _ => intro l v' hr; cases hr
  | trproj _ _ => intro l v' hr; cases hr
  | tinl _ _ => intro l v' hr; cases hr
  | tinr _ _ => intro l v' hr; cases hr
  | tcase _ _ _ => intro l v' hr; cases hr
  | tflam _ => intro l v' hr; cases hr
  | tfclos _ _ _ => intro l v' hr; cases hr
  | tfold _ _ => intro l v' hr; cases hr
  | tunfold _ _ => intro l v' hr; cases hr
  | trcd ht ih =>
    intro l v' hr hnl
    cases hr with
    | rvlzero => exact hnl .rcd
  | tmrg h1 h2 ih1 ih2 =>
    intro l v' hr hnl
    cases hr with
    | vlandl hr' =>
      exact ih1 l _ hr' (fun hlin => hnl (.andl hlin))
    | vlandr hr' =>
      exact ih2 l _ hr' (fun hlin => hnl (.andr hlin))
  | tclos _ _ _ => intro l v' hr; cases hr

@[simp]
theorem rlookup_pres_aux {E l A} :
    RLookup E l A
    → ∀ {v v'},
      RLookupV v l v'
      → Value v
      → HasType .top v E
      → HasType E v' A := by
  intro hl
  induction hl with
  | zero =>
    intro v v' hlv hv ht
    cases ht with
    | tapp _ _ => cases hv
    | tbox _ _ => cases hv
    | tproj _ _ => cases hv
    | trproj _ _ => cases hv
    | tcase _ _ _ => cases hv
    | tunfold _ => cases hv
    | trcd ht' =>
      cases hlv with
      | rvlzero =>
        cases hv with
        | vrcd hv' =>
          exact value_weaken ht' hv'
  | landl hrl hnl ih =>
    intro v v' hlv hv ht
    cases hlv with
    | vlandl hlv' =>
      cases ht with
      | tmrg h1 h2 =>
        cases hv with
        | vmrg hv1 hv2 =>
          have h := ih hlv' hv1 (value_weaken h1 hv1)
          exact value_weaken h (rlookupv_value hlv' hv1)
    | vlandr hlv' =>
      cases ht with
      | tmrg h1 h2 =>
        cases hv with
        | vmrg hv1 hv2 =>
          have : False := notin_false h2 _ _ hlv' hnl
          contradiction
    | rvlzero =>
      cases ht
  | landr hrl hnla ih =>
    intro v v' hlv hv ht
    cases hlv with
    | vlandl hlv' =>
      cases ht with
      | tmrg h1 h2 =>
        cases hv with
        | vmrg hv1 hv2 =>
          have : False := notin_false h1 _ _ hlv' hnla
          contradiction
    | vlandr hlv' =>
      cases ht with
      | tmrg h1 h2 =>
        cases hv with
        | vmrg hv1 hv2 =>
          have h := ih hlv' hv2 (value_weaken h2 hv2)
          exact value_weaken h (rlookupv_value hlv' hv2)
    | rvlzero =>
      cases ht

@[simp]
theorem rlookup_pres {E l A} :
  RLookup E l A
  → ∀ {v v'},
      RLookupV v l v'
      → Value v
      → HasType .top v E
      → HasType .top v' A := by
  intro hl v v' hlv hv ht
  have h := rlookup_pres_aux hl hlv hv ht
  exact value_weaken h (rlookupv_value hlv hv)

@[simp]
theorem lookup_prog {n A B} :
  Lookup A n B
  → ∀ {v}, HasType .top v A → Value v
  → ∃ e', LookupV v n e' := by
  intro hl
  induction hl with
  | zero =>
    intro v ht hv
    cases ht <;> cases hv
    · rename_i v1 v2 h1 h2 hv1 hv2
      exact ⟨_, LookupV.lvzero⟩
  | succ _ ih =>
    intro v ht hv
    cases ht <;> cases hv
    · rename_i v1 v2 h1 h2 hv1 hv2
      have ⟨e', he⟩ := ih (value_weaken h1 hv1) hv1
      exact ⟨_, LookupV.lvsucc he⟩

@[simp]
theorem rlookup_prog {l A B} :
  RLookup A l B
  → ∀ {v}, HasType .top v A → Value v
  → ∃ e', RLookupV v l e' := by
  intro hl
  induction hl with
  | zero =>
    intro v ht hv
    cases ht <;> cases hv
    · exact ⟨_, RLookupV.rvlzero⟩
  | landl _ _ ih =>
    intro v ht hv
    cases ht <;> cases hv
    · rename_i v1 v2 h1 h2 hv1 hv2
      have ⟨e', he⟩ := ih (value_weaken h1 hv1) hv1
      exact ⟨_, RLookupV.vlandl he⟩
  | landr _ _ ih =>
    intro v ht hv
    cases ht <;> cases hv
    · rename_i v1 v2 h1 h2 hv1 hv2
      have ⟨e', he⟩ := ih (value_weaken h2 hv2) hv2
      exact ⟨_, RLookupV.vlandr he⟩
