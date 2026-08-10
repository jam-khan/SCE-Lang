# geometry

A functor crossing a unit boundary. `shapes.sce` exports the functor `Scale`;
its generated `Scale.scei` is the signature `{k : Int} => {by : Int -> Int}`,
and `report.sce` imports and applies it.

Under wasm-level linking this is the strongest form of the claim: the `Scale`
closure is a GC struct created by `shapes.wasm`'s instance, and `report`'s
code `call_ref`s it across instances — WasmGC structural type identity is what
makes that legal.

```console
$ main -c vec.sce -o vec.sceo
$ main -c shapes.sce -o shapes.sceo        # writes Shapes.scei and Scale.scei
$ main -c report.sce -o report.sceo
$ main --link vec.sceo shapes.sceo report.sceo -o prog.sceo
$ main --run prog.sceo
- : Int = 49
```
