# linkrec

Recursive linking, with no new machinery. `Parity` is a functor whose import
interface — `{ even : Int -> Bool }` — is satisfied by its *own* export: an
ordinary `let rec` ties the knot, so the module's export flows back in as its
import. Mutual recursion (`even`/`odd`) closes through a single function-typed
import, which is exactly the shape the mechanization proves sound: `linkrec`
is a *derived form* (`mrec_elab` in RecLinking.lean), inheriting progress,
preservation, correctness of elaboration, and determinism (its one-line
corollaries) rather than needing its own metatheory. The reading is
generative — each recursive call re-applies the functor to a fresh package —
so a functor that performed effects at construction would repeat them per
call; tie the knot with effect-free construction.

```console
$ main parity.sce
- : {even10 : Bool} & {odd10 : Bool} & {even7 : Bool} = { even10 = true; odd10 = false; even7 = false }
```

The toolchain's linker deliberately stays acyclic — every unit's imports must
be satisfied by units linked before it — so *cross-unit* recursion is out of
scope, matching the calculus: recursion through linking is available exactly
where the theory covers it, as a self-referential functor.
