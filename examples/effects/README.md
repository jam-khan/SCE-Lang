# effects

No ambient authority: the language has no print statement. `Sys` is a
host-built provider unit, and a program performs IO only if its link line
grants it — the same wiring, checks, and attenuation that apply to any other
dependency apply to capabilities.

```console
$ main -c app.sce -o app.sceo       # `import Sys` uses the built-in interface
$ main --link sys app.sceo -o prog.sceo
$ main --run prog.sceo
[app] greeting world
[app] greeting again
- : String = "hello, world / hello, again"
```

`sandbox` is effect confinement: the sandboxed `Pure` module cannot mention
`Sys` (a compile-time scope error), so it provably performs no IO. Attenuation
is ordinary code — `Log.info` is `Sys.print` wrapped with a prefix, and a
component handed only `Log` can write lines but never chooses their shape.
