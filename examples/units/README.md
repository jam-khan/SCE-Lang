# Separate-compilation case studies

Each directory is a set of units plus `whole.sce`, the same program written as
one file. `test/test_commute.ml` drives every set through every path the
toolchain offers and requires one answer from all of them:

1. `whole.sce`, interpreted
2. `whole.sce`, compiled to wasm and run under node
3. units linked at the core level, evaluated — one-shot, *incrementally*
   (a linked artifact is itself a leaf unit), and in a permuted order where
   the dependencies allow one
4. the core-linked term compiled to wasm
5. units compiled to separate wasm modules and linked at the wasm level

| set | what it exercises |
|---|---|
| [hello/](hello/) | two independent providers and a consumer; link-order permutation |
| [geometry/](geometry/) | a functor exported by one unit and applied in another — under wasm linking, a closure built by one instance is `call_ref`'d from another |
| [peano/](peano/) | iso-recursive `mu` values crossing units; the consumer redeclares the type and structural equality makes it compatible |
| [textlib/](textlib/) | strings and recursion; a unit whose body uses first-class `linkall` while the toolchain links the unit itself — both linking levels in one program |

Each README shows the exact CLI session for its set.
