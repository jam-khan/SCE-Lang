# linker

The link step, written in the language it links. `link P with f` means:
extend the world with the provider, wire its exports into the functor's
import record, keep both halves. That sentence is a one-line program —

```
let byhand = P ,,, f({ Seed = P.Seed })
```

— and because the builtin construct elaborates to exactly this shape, the two
must agree. `host.sce` checks that at run time, on the *same* functor loaded
from disk: `byhand` and `link P with f` are compared field by field on both
halves — the provider's `Seed.start` and the client's `bump` — which at these
types is whole-value agreement (`=` is primitive-only).

```console
$ main -c step.sce -o step.sceo
$ main -c host.sce -o host.sceo
$ main --link loader host.sceo -o prog.sceo
$ main --run prog.sceo
- : String = "hand-written link = builtin link, both halves kept"
```

This is the paper's separate-compilation story made executable: there is no
linker formalism to trust, because the linker's composition term is an
ordinary term of the calculus — one the program itself can write, even for
components that arrive at run time.
