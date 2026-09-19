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
| [shop/](shop/) | the paper's running example: a provider, a client compiled against its `.scei` alone, and a second client that needs both — `whole.sce` is the same program with the links written as expressions |
| [peano/](peano/) | a recursive ADT crossing units; the consumer redeclares the type with its own constructor names and structural equality makes it compatible |

Each README shows the exact CLI session for its set.
