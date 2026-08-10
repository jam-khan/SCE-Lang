# diamond

A diamond dependency: `left` and `right` both import `Lib`, and `top` imports
both sides. The linker installs **one** copy of `Lib`, and both importers'
interface checks resolve against it — there is no double inclusion, no
conflict, and no coordination beyond the shared `Lib.scei`. The sides are
independent, so they may be linked in either order.

```console
$ main -c lib.sce -o lib.sceo
$ main -c left.sce -o left.sceo
$ main -c right.sce -o right.sceo
$ main -c top.sce -o top.sceo
$ main --link lib.sceo left.sceo right.sceo top.sceo -o all.sceo
$ main --run all.sceo
- : Int = 31
$ main --link lib.sceo right.sceo left.sceo top.sceo -o alt.sceo
$ main --run alt.sceo
- : Int = 31
```

What would be a special case elsewhere is the default here: a provider's
exports satisfy *every* downstream import structurally, so sharing is simply
what happens when one unit is linked before two importers. The dual policy —
two providers exporting the *same* label — is rejected at link time as an
ambiguity; see [examples/versions/](../../versions/) for that story.
