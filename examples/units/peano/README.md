# peano

Recursive data crossing unit boundaries. `nat.sce` declares
`type nat = | Z | S of nat` — sugar over `mu a. Top | a` — and
`arith.sce` declares its *own* ADT with its own constructor names
(`Zero`/`Next`). Structural equality is what makes them compatible: neither
the type nor the constructors have to be shared between separately compiled
units.

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
