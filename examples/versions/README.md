# versions

Two versions of the same library in one program. `libv1` and `libv2` both
declare `module Lib` with the same interface. Linking both statically is
rejected — same-name coexistence is an *ambiguity*, caught at link time:

```console
$ main --link libv1.sceo libv2.sceo client.sceo -o bad.sceo
link error: units libv1 and libv2 both export 'Lib'; the label would become ambiguous
```

But version choice is per **use site**, not per program: the client links v1
statically and loads v2 where it wants it, so both versions run side by side
under one name, each reached through its own route.

```console
$ main -c libv1.sce -o libv1.sceo
$ main -c libv2.sce -o libv2.sceo
$ main -c client.sce -o client.sceo
$ main --link libv1.sceo loader client.sceo -o prog.sceo
$ main --run prog.sceo
- : String = "hello, world (v1) | HELLO, world (v2)"
```

The loader's declared type is the version contract: an artifact whose
interface drifted from `{Lib : {version : String; greet : String -> String}}`
comes back as `inr {err}` — version skew is a value the program handles, not
a crash.
