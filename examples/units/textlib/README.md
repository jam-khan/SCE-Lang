# textlib

Strings, recursion, and both linking levels at once. `show.sce` renders
decimals with recursion over `/` and `mod` (the core has no int-to-string
primitive); `csv.sce` sits in the middle of the chain; `summary.sce` is
linked by the toolchain while its own body uses the language's first-class
`linkall` — the toolchain's linker and the calculus's linker are the same
mechanism, so they compose in one program.

```console
$ main -c show.sce -o show.sceo
$ main -c csv.sce -o csv.sceo
$ main -c summary.sce -o summary.sceo
$ main --link show.sceo csv.sceo summary.sceo -o prog.sceo
$ main --run prog.sceo
- : String = "35,70,-35"
```
