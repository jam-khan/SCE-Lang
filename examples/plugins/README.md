# plugins

A plugin manager written in the language: runtime linking with capability
confinement. The manager loads plugin artifacts *at run time*, interface-checks
them, and links each against an attenuated capability record.

The loader is itself a capability whose **type declares the contract**: the
`Loader` import names the exact signature every plugin must satisfy, and the
runtime check is structural equality between that signature and the loaded
artifact's stored type — the same comparison the static linker makes, made
later. Failure comes back as a union the program cases on, not a crash.

```console
$ main -c shout.sce -o shout.sceo
$ main -c quiet.sce -o quiet.sceo
$ main -c manager.sce -o manager.sceo
$ main --link sys loader manager.sceo -o prog.sceo
$ main --run prog.sceo
[shout] making some noise
[quiet] staying quiet
- : String = "shout! (quiet) <cannot open artifact: ghost.sceo: No such file or directory>"
```

What each piece demonstrates:

- **Least authority, by scoping.** A plugin is a sandboxed functor from the
  capabilities it is handed to its exports. `evil.sce` tries to call `Sys`
  directly and does not compile — confinement is a scope error, not a runtime
  denial.
- **Attenuation is ordinary code.** `Caps.for_plugin` wraps `Sys.print` with a
  per-plugin prefix; a plugin can log but never chooses the shape of the line,
  and it cannot read files at all.
- **Mutual distrust.** Two loaded plugins cannot see each other — or anything
  else — unless the manager wires them.
