# Lean mechanization

Definitions and proofs for λSCE, its elaboration into λE, and separate
compilation. See the [paper-to-Lean theorem map](THEOREMS.md) for individual results.

## Build

Install `elan`, then run from this directory:

```sh
lake build
```

The toolchain is pinned in `lean-toolchain`. The proofs have no external
Lean dependencies; [LeanSce.lean](LeanSce.lean) imports the full development.

## Reading order

1. [Core/](LeanSce/Core/): λE syntax, typing, evaluation, and type safety.
2. [SCE/](LeanSce/SCE/): source syntax, elaboration, evaluation, and type safety.
3. [SemanticsPreservation](LeanSce/SCE/SemanticsPreservation.lean),
   [Simulation](LeanSce/SCE/Simulation.lean), and [Divergence](LeanSce/SCE/Divergence.lean).
4. [Sepcomp](LeanSce/SCE/Sepcomp.lean), [UnitChains](LeanSce/SCE/UnitChains.lean),
   and [BehaviourLaws](LeanSce/SCE/BehaviourLaws.lean).

From the repository root, `make docs-lean` generates searchable HTML;
`make web` serves it alongside the playground. Documentation dependencies
are pinned separately in `docbuild/`. The proofs cover the calculi and
elaboration, not the OCaml compiler or WebAssembly backend.
