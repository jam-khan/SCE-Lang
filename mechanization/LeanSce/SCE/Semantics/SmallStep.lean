import LeanSce.SCE.Syntax
import LeanSce.SCE.Semantics.BigStep

open SCE S_Sem

inductive SStep : Exp → Exp → Exp → Prop where
  | ssquery {v}
    : Value v
    -> SStep v .query v
  | ssappl {v e1 e1' e2}
    : Value v
    → SStep v e1 e1'
    → SStep v (.app e1 e2) (.app e1' e2)
  | ssboxl {v e1 e1' e2}
    : Value v
    → SStep v e1 e1'
    → SStep v (.box e1 e2) (.box e1' e2)
  | ssmrgl {v e1 e1' e2}
    : Value v
    → SStep v e1 e1'
    → SStep v (.mrg e1 e2) (.mrg e1' e2)
  | ssappr {v v1 e2 e2'}
    : Value v
    → Value v1
    → SStep v e2 e2'
    → SStep v (.app v1 e2) (.app v1 e2')
  | ssboxr
    : Value v
    → Value v1
    → SStep v1 e2 e2'
    → SStep v (.box v1 e2) (.box v1 e2')
  | ssmrgr {v v1 e2 e2'}
    : Value v
    → Value v1
    → SStep (.mrg v v1) e2 e2'
    → SStep v (.mrg v1 e2) (.mrg v1 e2')
  | ssclos {v A e}
    : Value v
    → SStep v (.lam A e) (.clos v A e)
  | ssbeta {v v1 v2 A e}
    : Value v
    → Value v1
    → Value v2
    → SStep v (.app (.clos v2 A e) v1) (.box (.mrg v2 v1) e)
  | ssboxv {v v1 v2}
    : Value v
    → Value v1
    → Value v2
    → SStep v (.box v1 v2) v2
  | ssproj {v e1 e2 n}
    : Value v
    → SStep v e1 e2
    → SStep v (.proj e1 n) (.proj e2 n)
  | ssprojv {v v1 n v2}
    : Value v
    → Value v1
    → LookupV v1 n v2
    → SStep v (.proj v1 n) v2
  | sslrec {v e1 e2 l}
    : Value v
    → SStep v e1 e2
    → SStep v (.lrec l e1) (.lrec l e2)
  | ssrproj
    : Value v
    → SStep v e1 e2
    → SStep v (.rproj e1 l) (.rproj e2 l)
  | ssrprojv {v v1 l v2}
    : Value v
    → Value v1
    → Sel v1 l v2
    → SStep v (.rproj v1 l) v2
  | ssmstruct {v e e'}
    : Value v
    → SStep v e e'
    → SStep v (.mstruct e) (.mstruct e')
  | ssmfunctor_sandboxed {v : Exp} {A : Typ} {e : Exp}
    : Value v
    → SStep v (.mfunctor .sandboxed A e) (.mclos .unit A e)
  | ssmfunctor_open {v : Exp} {A : Typ} {e : Exp}
    : Value v
    → SStep v (.mfunctor .open_ A e) (.mclos v A e)
  | ssmappl {v e1 e1' e2}
    : Value v
    → SStep v e1 e1'
    → SStep v (.mapp e1 e2) (.mapp e1' e2)
  | ssmappr {v v1 e2 e2'}
    : Value v
    → Value v1
    → SStep v e2 e2'
    → SStep v (.mapp v1 e2) (.mapp v1 e2')
  | ssmbeta {v v1 v2 A e}
    : Value v
    → Value v1
    → Value v2
    → SStep v (.mapp (.mclos v2 A e) v1) (.box (.mrg v2 v1) e)
  | ssnmrgl {v e1 e1' e2}
    : Value v
    → SStep v e1 e1'
    → SStep v (.nmrg e1 e2) (.nmrg e1' e2)
  | ssnmrgr {v v1 e2 e2'}
    : Value v
    → Value v1
    → SStep v e2 e2'
    → SStep v (.nmrg v1 e2) (.nmrg v1 e2')
  | ssnmrgv {v v1 v2}
    : Value v
    → Value v1
    → Value v2
    → SStep v (.nmrg v1 v2) (.mrg v1 v2)
  | ssletbl {v e1 e1' e2}
    : Value v
    → SStep v e1 e1'
    → SStep v (.letb e1 e2) (.letb e1' e2)
  | ssletbv {v v1 e2}
    : Value v
    → Value v1
    → SStep v (.letb v1 e2) (.box (.mrg v v1) e2)
  | ssmlinkl {v e1 e1' e2}
    : Value v
    → SStep v e1 e1'
    → SStep v (.mlink e1 e2) (.mlink e1' e2)
  | ssmlinkr {v v1 e2 e2'}
    : Value v
    → Value v1
    → SStep v e2 e2'
    → SStep v (.mlink v1 e2) (.mlink v1 e2')
  | ssmlinkbeta {v v1 v2 vl A body l}
    : Value v
    → Value v1
    → Value v2
    → Sel v1 l vl
    → SStep v (.mlink v1 (.mclos v2 (.rcd l A) body))
              (.mrg v1 (.box (.mrg v2 (.lrec l vl)) body))
  | ssopenml {v e1 e1' e2}
    : Value v
    → SStep v e1 e1'
    → SStep v (.openm e1 e2) (.openm e1' e2)
  | ssopenm {v v' e2 l}
    : Value v
    → Value v'
    → SStep v (.openm (.lrec l v') e2) (.box (.mrg v v') e2)
  | ssinl {v e1 e2 B}
    : Value v
    → SStep v e1 e2
    → SStep v (.inl B e1) (.inl B e2)
  | ssinr {v e1 e2 A}
    : Value v
    → SStep v e1 e2
    → SStep v (.inr A e1) (.inr A e2)
  | sscase {v e e' e1 e2}
    : Value v
    → SStep v e e'
    → SStep v (.case e e1 e2) (.case e' e1 e2)
  | sscasel {v v1 B e1 e2}
    : Value v
    → Value v1
    → SStep v (.case (.inl B v1) e1 e2) (.box (.mrg v v1) e1)
  | sscaser {v v1 A e1 e2}
    : Value v
    → Value v1
    → SStep v (.case (.inr A v1) e1 e2) (.box (.mrg v v1) e2)
  | ssfclos {v A B e}
    : Value v
    → SStep v (.flam A B e) (.fclos v A B e)
  | ssfbeta {v v1 v2 A B e}
    : Value v
    → Value v1
    → Value v2
    → SStep v (.app (.fclos v2 A B e) v1)
              (.box (.mrg (.mrg v2 (.fclos v2 A B e)) v1) e)
  | ssfold {v e1 e2 T}
    : Value v
    → SStep v e1 e2
    → SStep v (.fold T e1) (.fold T e2)
  | ssunfold {v e1 e2}
    : Value v
    → SStep v e1 e2
    → SStep v (.unfold e1) (.unfold e2)
  | ssunfoldv {v v1 T}
    : Value v
    → Value v1
    → SStep v (.unfold (.fold T v1)) v1
  | ssmlinknl {v e1 e1' e2}
    : Value v
    → SStep v e1 e1'
    → SStep v (.mlinkn e1 e2) (.mlinkn e1' e2)
  | ssmlinknr {v v1 e2 e2'}
    : Value v
    → Value v1
    → SStep v e2 e2'
    → SStep v (.mlinkn v1 e2) (.mlinkn v1 e2')
  | ssmlinknbeta {v v1 v2 pkg : Exp} {D : Typ} {body : Exp}
    : Value v
    → Value v1
    → Value v2
    → SelPkg v1 D pkg
    → SStep v (.mlinkn v1 (.mclos v2 D body))
              (.mrg v1 (.box (.mrg v2 pkg) body))

-- Values are normal forms: no value takes a step under any environment
theorem value_no_step {v : Exp} (hv : Value v) : ∀ {ρ e : Exp}, ¬ SStep ρ v e := by
  induction hv with
  | vint => intro _ _ hs; nomatch hs
  | vunit => intro _ _ hs; nomatch hs
  | vclos _ => intro _ _ hs; nomatch hs
  | vmclos _ => intro _ _ hs; nomatch hs
  | vmstruct _ ih =>
    intro _ _ hs
    cases hs with
    | ssmstruct _ h => exact ih h
  | vmrg _ _ ih1 ih2 =>
    intro _ _ hs
    cases hs with
    | ssmrgl _ h => exact ih1 h
    | ssmrgr _ _ h => exact ih2 h
  | vlrec _ ih =>
    intro _ _ hs
    cases hs with
    | sslrec _ h => exact ih h
  | vinl _ ih =>
    intro _ _ hs
    cases hs with
    | ssinl _ h => exact ih h
  | vinr _ ih =>
    intro _ _ hs
    cases hs with
    | ssinr _ h => exact ih h
  | vfclos _ => intro _ _ hs; nomatch hs
  | vfold _ ih =>
    intro _ _ hs
    cases hs with
    | ssfold _ h => exact ih h
