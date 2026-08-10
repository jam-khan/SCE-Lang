# harness

One loaded artifact, two worlds. `report.sce` is written against an interface
— `{ fetch : String -> String }` is everything it can reach — and the host
instantiates the *same* loaded functor twice: once with a live `fetch` backed
by `Sys.readfile`, once with a canned in-memory one. Environments are
records, instantiation is application: hermetic testing of a dynamically
loaded component with no mocking framework.

```console
$ main -c report.sce -o report.sceo
$ main -c host.sce -o host.sceo
$ main --link sys loader host.sceo -o prog.sceo
$ printf 'live' > data.txt
$ main --run prog.sceo
- : String = "data(answer) = 42 / data(data.txt) = live"
$ rm data.txt
$ main --run prog.sceo
- : String = "data(answer) = 42 / data(data.txt) = <missing>"
```

The mock instance is deterministic whatever the filesystem holds, and the
component cannot tell which world it is in — it has no route to `Sys`, the
clock, or the loader, only to the `Env` record its instantiator built.
