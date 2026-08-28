# boot

Construction-time effects meet the linker. The provider prints *while its
exports are being built* — not inside any function a caller might invoke
later — and the consumer imports **two** labels from it, so the linker's wire
projects the provider twice.

```console
$ main -c provider.sce -o provider.sceo    # writes A1.scei, A2.scei
$ main -c consumer.sce -o consumer.sceo
$ main --link sys provider.sceo consumer.sceo -o prog.sceo
$ main --run prog.sceo
loading provider
- : Int = 3
```

One line, not three. This pins the property the linearized elaboration
exists for: every operand of a merge or link is bound exactly once, so a
unit's effects fire exactly once, in link-line order, no matter how many
imports are wired out of it. A composition term that spliced the provider
into the wire — re-evaluating it once per import, plus once for the merge —
would print `loading provider` three times here. The in-language counterpart
(a `linkall` whose provider prints) is pinned in the same suite; this
directory is the toolchain-level version, and it also runs through the wasm
trace differential.

A corollary worth knowing: link *order* commutes for values but not for
traces. Linking `provider` earlier or later never changes what the program
computes, but it moves when `loading provider` appears — which is why the
permutation tests compare values while trace tests fix the link line.
