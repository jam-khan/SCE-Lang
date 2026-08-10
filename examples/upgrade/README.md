# upgrade

Dynamic upgrade with a typed state handoff. `appv1` runs as a statically
linked unit; `appv2` is a functor whose import interface — old `motto`, old
`owner` — **is the migration contract**. The driver loads v2 at run time and
applies it to v1's exports: functor application is the migration step, and the
types say exactly which state the new version inherits.

```console
$ main -c appv1.sce -o appv1.sceo
$ main -c appv2.sce -o appv2.sceo
$ main -c driver.sce -o driver.sceo
$ main --link appv1.sceo loader driver.sceo -o prog.sceo
$ main --run prog.sceo
- : String = "v2 for jam (was: keep going)"
$ rm appv2.sceo
$ main --run prog.sceo
- : String = "still v1: keep going (cannot open artifact: appv2.sceo: No such file or directory)"
```

A missing upgrade — or one whose interface drifted from the loader's declared
type — comes back as `inr {err}`, and the program keeps running v1. Rollback
is not a mechanism; it is the `inr` branch.
