# linker

The link step, written in the language it links. `link Prov with F` means:
extend the world with the provider, wire its exports into the functor's
import record, keep both halves. That sentence is a one-line program —

```
let linked = Prov ,,, f({ Seed = { start = Prov.start } })
```

— and because the builtin construct elaborates to exactly this shape, the two
must agree. `host.sce` checks that at run time, against a functor loaded from
disk: the hand-written link of `step.sceo` produces the same `bump` as the
builtin `link`, with the provider's own exports still reachable in the result.

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
