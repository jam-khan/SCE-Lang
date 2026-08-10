# dynconfig

Runtime product lines: a config file decides which implementation gets linked.
`plain` and `fancy` are leaf units with the same interface; `chooser` reads
`skin.txt` and loads whichever artifact it names. Swapping the implementation
is editing one line of text — nothing recompiles, and a missing or stale
artifact is a value the program handles, not a crash.

```console
$ main -c plain.sce -o plain.sceo
$ main -c fancy.sce -o fancy.sceo
$ main -c chooser.sce -o chooser.sceo
$ main --link sys loader chooser.sceo -o prog.sceo
$ printf 'fancy.sceo' > skin.txt     # no trailing newline
$ main --run prog.sceo
- : String = "** hello **"
$ printf 'plain.sceo' > skin.txt
$ main --run prog.sceo
- : String = "hello"
```
