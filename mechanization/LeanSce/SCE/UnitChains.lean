import LeanSce.SCE.Sepcomp

/-!
Correctness of finite chains of independently compiled units. An import-free
unit is compiled under the empty context and joined by non-dependent merge.
An importing unit is a sandboxed functor, also compiled under the empty context,
whose imports are supplied by the preceding chain. No unit is re-elaborated
under the accumulated exports.
-/

open SCE Core

/-- A nonempty chain of `n` units, with source composition `S`, accumulated
exports `I`, and assembled core term `L`, using ordinary single-import linking.
Only imports must be unambiguous; unrelated duplicate exports are permitted.
The exports of an import-free unit may themselves include functors. -/
inductive UnitChain : Nat → SCE.Exp → SCE.Typ → Core.Exp → Prop where
  | start {e : SCE.Exp} {E : SCE.Typ} {c : Core.Exp}
      (helab : elabExp .top e E c) :
      UnitChain 1 e E c
  | independent {n : Nat} {S e : SCE.Exp} {I E : SCE.Typ} {L c : Core.Exp}
      (hchain : UnitChain n S I L)
      (helab : elabExp .top e E c) :
      UnitChain (n + 1) (.nmrg S e) (.and I E) (nmrgCore L c)
  | importing {n : Nat} {S body : SCE.Exp} {I A E : SCE.Typ}
      {l : String} {L c : Core.Exp}
      (hchain : UnitChain n S I L)
      (helab : elabExp .top (.mfunctor .sandboxed (.rcd l A) body)
        (.marr (.rcd l A) E) c)
      (hlookup : SRLookup I l A) :
      UnitChain (n + 1) (.mlink S (.mfunctor .sandboxed (.rcd l A) body))
        (.and I E) (linkedCore (elabTyp I) (elabTyp (.rcd l A)) (elabTyp E) L c)

/-- Assembling independently compiled units gives exactly the elaboration of
their source composition. -/
theorem unit_chain_elaboration
    {n : Nat} {S : SCE.Exp} {I : SCE.Typ} {L : Core.Exp}
    (hchain : UnitChain n S I L) : elabExp .top S I L := by
  induction hchain with
  | start helab => exact helab
  | independent _ helab ih =>
    exact elabExp.enmrg _ _ _ _ _ _ _ ih helab
  | importing _ helab hlookup ih =>
    exact elabExp.mlink _ _ _ _ _ _ _ _ _ ih helab hlookup

/-- The assembled chain is well typed at its accumulated export type. -/
theorem unit_chain_typed
    {n : Nat} {S : SCE.Exp} {I : SCE.Typ} {L : Core.Exp}
    (hchain : UnitChain n S I L) : HasType .top L (elabTyp I) := by
  exact type_preservation (unit_chain_elaboration hchain)

/-- Evaluation correctness for the whole chain, including import-free steps. -/
theorem unit_chain_correctness
    {n : Nat} {S v : SCE.Exp} {I : SCE.Typ} {L : Core.Exp}
    (hchain : UnitChain n S I L)
    (heval : S_Sem.BStep .unit S v) :
    ∃ u, EBig .unit L u ∧ elabExp .top v I u := by
  exact whole_program_correctness (unit_chain_elaboration hchain) heval

/-- The corresponding chain construction with `linkall`: an importing unit
declares an interface `D` satisfied by the accumulated exports. -/
inductive UnitChainN : Nat → SCE.Exp → SCE.Typ → Core.Exp → Prop where
  | start {e : SCE.Exp} {E : SCE.Typ} {c : Core.Exp}
      (helab : elabExp .top e E c) :
      UnitChainN 1 e E c
  | independent {n : Nat} {S e : SCE.Exp} {I E : SCE.Typ} {L c : Core.Exp}
      (hchain : UnitChainN n S I L)
      (helab : elabExp .top e E c) :
      UnitChainN (n + 1) (.nmrg S e) (.and I E) (nmrgCore L c)
  | importing {n : Nat} {S body : SCE.Exp} {I D E : SCE.Typ}
      {L c : Core.Exp}
      (hchain : UnitChainN n S I L)
      (helab : elabExp .top (.mfunctor .sandboxed D body) (.marr D E) c)
      (hok : LinkOk I D) :
      UnitChainN (n + 1) (.mlinkn S (.mfunctor .sandboxed D body))
        (.and I E) (linkedCore (elabTyp I) (elabTyp D) (elabTyp E) L c)

/-- The multi-import assembly is exactly the elaboration of its source chain. -/
theorem unit_chain_n_elaboration
    {n : Nat} {S : SCE.Exp} {I : SCE.Typ} {L : Core.Exp}
    (hchain : UnitChainN n S I L) : elabExp .top S I L := by
  induction hchain with
  | start helab => exact helab
  | independent _ helab ih =>
    exact elabExp.enmrg _ _ _ _ _ _ _ ih helab
  | importing _ helab hok ih =>
    exact elabExp.mlinkn _ _ _ _ _ _ _ _ ih helab hok

/-- The assembled multi-import chain has its accumulated export type. -/
theorem unit_chain_n_typed
    {n : Nat} {S : SCE.Exp} {I : SCE.Typ} {L : Core.Exp}
    (hchain : UnitChainN n S I L) : HasType .top L (elabTyp I) := by
  exact type_preservation (unit_chain_n_elaboration hchain)

/-- Evaluation correctness for the whole multi-import chain. -/
theorem unit_chain_n_correctness
    {n : Nat} {S v : SCE.Exp} {I : SCE.Typ} {L : Core.Exp}
    (hchain : UnitChainN n S I L)
    (heval : S_Sem.BStep .unit S v) :
    ∃ u, EBig .unit L u ∧ elabExp .top v I u := by
  exact whole_program_correctness (unit_chain_n_elaboration hchain) heval
