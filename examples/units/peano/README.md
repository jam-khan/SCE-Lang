# peano

Iso-recursive data crossing unit boundaries. `nat.sce` builds Peano numerals
over `mu a. Top | a`; `arith.sce` declares its *own* `N` alias — structural
equality is what makes it compatible with the imported one, so no nominal
type has to be shared between separately compiled units.

`fold`ed values built in one unit are `unfold`ed and recursed over in another;
under wasm-level linking the `$Wrap` structs flow between instances.

```console
$ main -c nat.sce -o nat.sceo              # Nat.scei spells the mu-types out
$ main -c arith.sce -o arith.sceo
$ main -c demo.sce -o demo.sceo
$ main --link nat.sceo arith.sceo demo.sceo -o prog.sceo
$ main --run prog.sceo
- : Int = 9
```
