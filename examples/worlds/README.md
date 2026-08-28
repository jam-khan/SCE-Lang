# worlds

Environments are values. Two arrive by different routes and both are entered
with `box`:

- `fancy.sceo` is loaded from disk — `box w in ?.Theme.decorate "hello"` runs
  code under an environment that did not exist until run time;
- `snap` is the current world, captured with `let snap = ?` and re-entered
  when a load fails — rollback is evaluating under a value you kept.

Inside a box the body sees *only* the world it was given: names from the
enclosing scope do not resolve, so what the boxed code can reach is precisely
what the value contains.

```console
$ main -c fancy.sce -o fancy.sceo
$ main -c host.sce -o host.sceo
$ main --link loader host.sceo -o prog.sceo
$ main --run prog.sceo
- : String = "** hello ** / hello"
```

The first half is the loaded world; the second is the `ghost.sceo` load
failing and the snapshot answering instead. Neither pattern is expressible in
a language whose contexts are not values.
