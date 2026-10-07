# linkrec

Recursive linking, with no new primitive. `linkrec F` closes a functor `F`
whose import interface `{ l : A1 -> A2 }` is satisfied by its *own* export
`l`. The label and the function type are read off `F`'s type, and the
desugarer expands the construct into the mechanization's derived form
(`mrec_elab` in RecLinking.lean):

```
let F' = F in
let rec w (a : A1) : A2 = ((F' { l = w }).l) a in
F' { l = w }
```

It therefore inherits progress, preservation, correctness of elaboration, and
determinism rather than needing its own metatheory. The reading is
generative — each call through `w` re-applies the functor to a fresh package —
so a functor that performed effects at construction would repeat them per
call; tie the knot with effect-free construction.

- `parity.sce` — mutual recursion (`even`/`odd`) closed through a single
  function-typed import.
- `pricing.sce` — the paper's example: `Items` and `Packs` depend on each
  other, and `linkrec Pricing` closes the cycle.

```console
$ main parity.sce
- : {even10 : Bool} & {odd10 : Bool} & {even7 : Bool} = { even10 = true, odd10 = false, even7 = false }
$ main pricing.sce
- : Int = 171
```

The toolchain's linker deliberately stays acyclic — every unit's imports must
be satisfied by units linked before it — so *cross-unit* recursion is out of
scope, matching the calculus: recursion through linking is available exactly
where the theory covers it, as a self-referential functor.
