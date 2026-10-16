import LeanSce.Core.Syntax

open Core

inductive Step : Exp → Exp → Exp → Prop where
  | squery {v}
    : Value v
    -> Step v .query v
  | sappl {v e1 e1' e2}
    : Value v
    → Step v e1 e1'
    → Step v (.app e1 e2) (.app e1' e2)
  | sboxl {v e1 e1' e2}
    : Value v
    → Step v e1 e1'
    → Step v (.box e1 e2) (.box e1' e2)
  | smrgl {v e1 e1' e2}
    : Value v
    → Step v e1 e1'
    → Step v (.mrg e1 e2) (.mrg e1' e2)
  | sappr {v v1 e2 e2'}
    : Value v
    → Value v1
    → Step v e2 e2'
    → Step v (.app v1 e2) (.app v1 e2')
  | sboxr
    : Value v
    → Value v1
    → Step v1 e2 e2'
    → Step v (.box v1 e2) (.box v1 e2')
  | smrgr {v v1 e2 e2'}
    : Value v
    → Value v1
    → Step (.mrg v v1) e2 e2'
    → Step v (.mrg v1 e2) (.mrg v1 e2')
  | sclos {v A e}
    : Value v
    → Step v (.lam A e) (.clos v A e)
  | sbeta {v v1 v2 A e}
    : Value v
    → Value v1
    → Value v2
    → Step v (.app (.clos v2 A e) v1) (.box (.mrg v2 v1) e)
  | sboxv {v v1 v2}
    : Value v
    → Value v1
    → Value v2
    → Step v (.box v1 v2) v2
  | sproj {v e1 e2 n}
    : Value v
    → Step v e1 e2
    → Step v (.proj e1 n) (.proj e2 n)
  | sprojv {v v1 n v2}
    : Value v
    → Value v1
    → LookupV v1 n v2
    → Step v (.proj v1 n) v2
  | slrec {v e1 e2 l}
    : Value v
    → Step v e1 e2
    → Step v (.lrec l e1) (.lrec l e2)
  | srproj
    : Value v
    → Step v e1 e2
    → Step v (.rproj e1 l) (.rproj e2 l)
  | srprojv {v v1 l v2}
    : Value v
    → Value v1
    → RLookupV v1 l v2
    → Step v (.rproj v1 l) v2
  | sinl {v e1 e2 B}
    : Value v
    → Step v e1 e2
    → Step v (.inl B e1) (.inl B e2)
  | sinr {v e1 e2 A}
    : Value v
    → Step v e1 e2
    → Step v (.inr A e1) (.inr A e2)
  | scase {v e e' e1 e2}
    : Value v
    → Step v e e'
    → Step v (.case e e1 e2) (.case e' e1 e2)
  | scasel {v v1 B e1 e2}
    : Value v
    → Value v1
    → Step v (.case (.inl B v1) e1 e2) (.box (.mrg v v1) e1)
  | scaser {v v1 A e1 e2}
    : Value v
    → Value v1
    → Step v (.case (.inr A v1) e1 e2) (.box (.mrg v v1) e2)
  | sfclos {v A B e}
    : Value v
    → Step v (.flam A B e) (.fclos v A B e)
  | sfbeta {v v1 v2 A B e}
    : Value v
    → Value v1
    → Value v2
    → Step v (.app (.fclos v2 A B e) v1)
             (.box (.mrg (.mrg v2 (.fclos v2 A B e)) v1) e)
  | sfold {v e1 e2 T}
    : Value v
    → Step v e1 e2
    → Step v (.fold T e1) (.fold T e2)
  | sunfold {v e1 e2}
    : Value v
    → Step v e1 e2
    → Step v (.unfold e1) (.unfold e2)
  | sunfoldv {v v1 T}
    : Value v
    → Value v1
    → Step v (.unfold (.fold T v1)) v1

inductive MStep : Exp → Exp → Exp → Prop where
  | refl :
    ∀ {v e},
      Value v
    → MStep v e e
  | step :
    ∀ {v e e' e''},
      Step v e e'
    → MStep v e' e''
    → MStep v e e''
