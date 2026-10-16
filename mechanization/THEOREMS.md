# Paper-to-Lean theorem map

Numbers follow *Linking as Evaluation*. Links point to the corresponding
declarations; grouped rows list them in paper order.

## Main results

| Paper result | Lean declaration(s) |
| --- | --- |
| 3.1 Inference uniqueness | [inference_uniqueness](LeanSce/SCE/Elaboration/Uniqueness.lean#L219) |
| 3.2 Value weakening | [svalue_weaken](LeanSce/SCE/Preservation.lean#L62) |
| 3.3–3.4 Lookup/selection progress | [slookup_progress](LeanSce/SCE/Preservation.lean#L256), [sselection_progress](LeanSce/SCE/Preservation.lean#L267); returned-entry typing uses [elab_lookup_pres](LeanSce/SCE/Preservation.lean#L81), [elab_rlookup_pres](LeanSce/SCE/Preservation.lean#L161), and value weakening. |
| 3.5–3.6 Progress/preservation | [sgprogress](LeanSce/SCE/Progress.lean#L9), [sgpreservation](LeanSce/SCE/Preservation.lean#L323) |
| 3.7 Type safety | Follows from [sprogress](LeanSce/SCE/Progress.lean#L280) and [spreservation](LeanSce/SCE/Preservation.lean#L654); no separately named corollary. |
| §4.1 Target type safety | [gprogress](LeanSce/Core/Progress.lean#L8), [gpreservation](LeanSce/Core/Preservation.lean#L9) |
| 4.1 Context independence | [sandboxed_functor_elab_context_independent](LeanSce/SCE/Elaboration/Elaboration.lean#L192) |
| 4.2–4.3 Type preservation/elaboration uniqueness | [type_preservation](LeanSce/SCE/Elaboration/Preservation.lean#L200), [elaboration_uniqueness](LeanSce/SCE/Elaboration/Uniqueness.lean#L228) |
| 4.4 Big-step/small-step equivalence | [sstep_sbig_eq](LeanSce/SCE/Semantics/Equivalence.lean#L702) |
| 4.5–4.7 Value elaboration, lookup/selection preservation | [elab_value](LeanSce/SCE/Elaboration/Preservation.lean#L90), [lookup_preservation](LeanSce/SCE/SemanticsPreservation.lean#L46), [sel_preservation](LeanSce/SCE/SemanticsPreservation.lean#L68) |
| 4.8 Semantics preservation | [semantic_preservation](LeanSce/SCE/SemanticsPreservation.lean#L247) |
| 4.9 Behavior preservation | [elab_behaviour_equiv](LeanSce/SCE/Divergence.lean#L289) |
| 4.10 Whole-program correctness | [whole_program_behaviour](LeanSce/SCE/BehaviourLaws.lean#L124) |
| 4.11 Link typing | [core_link_typed](LeanSce/SCE/Sepcomp.lean#L35) |
| 4.12–4.13 Dynamic/static separate compilation | [separate_compilation_behaviour](LeanSce/SCE/Divergence.lean#L303), [separate_compilation_closed_behaviour](LeanSce/SCE/Divergence.lean#L337) |
| 4.14 Interface abstraction | [S_Sem.interface_abstraction_behaviour](LeanSce/SCE/BehaviourLaws.lean#L180) |
| 4.15 Determinism | [bigstep_deterministic_gen](LeanSce/SCE/Semantics/Determinism.lean#L105) |
| 4.16 Sandbox confinement | [sandboxed_functor_confinement](LeanSce/SCE/Confinement.lean#L23) (results), [sandboxed_functor_confinement_diverges](LeanSce/SCE/BehaviourLaws.lean#L298) (divergence) |
| 4.17 Link confinement | [sandboxed_link_confinement_behaviour](LeanSce/SCE/BehaviourLaws.lean#L368) |

## Appendix results

| Paper result | Lean declaration(s) |
| --- | --- |
| A.1–A.3 Big-step soundness, completeness, and values | [sbig_sound](LeanSce/SCE/Semantics/Equivalence.lean#L263), [sbig_complete](LeanSce/SCE/Semantics/Equivalence.lean#L694), [sbig_produces_value](LeanSce/SCE/Semantics/Equivalence.lean#L18) |
| B.1–B.2 Translation/substitution and wire typing | [elab_substTyp](LeanSce/SCE/Elaboration/Elaboration.lean#L42), [wire_typed](LeanSce/SCE/Elaboration/Preservation.lean#L141) |
| B.3 Multi-import link typing | [core_linkn_typed](LeanSce/SCE/Sepcomp.lean#L113) |
| B.4 Multi-import static separate compilation | [separate_compilation_n_sandboxed_behaviour](LeanSce/SCE/Divergence.lean#L367) |
| B.5 Multi-import interface replacement | [S_Sem.link_respects_interface](LeanSce/SCE/LinkingLaws.lean#L22), [S_Sem.link_interface_determined](LeanSce/SCE/LinkingLaws.lean#L46) |
| B.6 Multi-import interface abstraction | [S_Sem.interface_abstraction_n_behaviour](LeanSce/SCE/BehaviourLaws.lean#L258) |
| C.1 Unit-chain correctness | [unit_chain_elaboration](LeanSce/SCE/UnitChains.lean#L36), [unit_chain_behaviour](LeanSce/SCE/BehaviourLaws.lean#L133) |
| C.2 Multi-import unit-chain correctness | [unit_chain_n_elaboration](LeanSce/SCE/UnitChains.lean#L79), [unit_chain_n_behaviour](LeanSce/SCE/BehaviourLaws.lean#L139) |

[SameBehaviour](LeanSce/SCE/Divergence.lean#L283) includes terminating results
in both directions and divergence equivalence. The map selects these stronger
results where the paper requires them. The supporting forward simulation is
[elab_forward_simulation](LeanSce/SCE/Simulation.lean#L1178).
