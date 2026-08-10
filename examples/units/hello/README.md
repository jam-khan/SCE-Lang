# hello

The smallest realistic split: two leaf providers and a consumer.

```console
$ main -c counter.sce -o counter.sceo      # writes Counter.scei
$ main -c fmt.sce -o fmt.sceo              # writes Fmt.scei
$ main -c app.sce -o app.sceo              # imports resolve against the .scei files
$ main --link counter.sceo fmt.sceo app.sceo -o prog.sceo
$ main --run prog.sceo
- : String = "[yes]"
```

`counter` and `fmt` are independent, so they may be linked in either order —
the commutation test checks both give the same `main`. `whole.sce` is the same
program as one file.
