# wiring

Capability delegation between plugins, decided entirely by the host. Both
plugins satisfy the same ABI — a functor from `{log, peer}` capabilities to
`{run}` — and neither can name, load, or observe the other. The host wires
`exclaim`'s exported `run` in as `chain`'s `peer` capability, so one plugin's
authority over another exists exactly where the host constructed it:

```console
$ main -c exclaim.sce -o exclaim.sceo
$ main -c chain.sce -o chain.sceo
$ main -c host.sce -o host.sceo
$ main --link sys loader host.sceo -o prog.sceo
$ main --run prog.sceo
[chain] chaining hi
[exclaim] exclaiming hi
- : String = "<hi!>"
```

- **Delegation is a record field.** `peer = ex.run` is the entire wiring
  mechanism — no registry, no service lookup, no policy engine.
- **The default is isolation.** `exclaim`'s own `peer` is wired to the
  identity function; had the host passed that to `chain` too, the plugins
  would be fully independent. Connectivity is opt-in, per capability record.
- **Attenuation composes.** Each plugin logs through its own prefixed logger
  and reaches nothing else; the delegated `peer` carries `exclaim`'s behavior
  but none of its capabilities.
