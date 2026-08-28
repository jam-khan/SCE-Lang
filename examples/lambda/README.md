# lambda

A lambda-calculus interpreter with real text parsing — the first non-toy
program in the tree, and every piece of the language shows up in it:

- **ADTs everywhere**: tokens, terms, options, and parse results are
  datatypes; every unit redeclares them structurally and imports nothing but
  what it calls.
- **String introspection is a capability.** The core's string primitives are
  `^` and `=` — strings are write-only. `Str.head`/`Str.tail` arrive as host
  primitives through the link line, exactly like `Sys.print`: the lexer is
  the only unit that imports `Str`, so the interface tells you which unit can
  inspect text.
- **Separate compilation at scale**: `lexer`, `parser`, `eval`, and `pretty`
  are independent units over shared structural types; the parser never sees
  `Str`, the evaluator never sees tokens.
- **Failure is a value**: a parse error flows back as `Err`, and the
  evaluator's fuel bound makes divergent terms answer instead of hang.

```console
$ main -c lexer.sce -o lexer.sceo
$ main -c parser.sce -o parser.sceo
$ main -c eval.sce -o eval.sceo
$ main -c pretty.sce -o pretty.sceo
$ main -c main.sce -o main.sceo
$ main --link str lexer.sceo parser.sceo eval.sceo pretty.sceo main.sceo -o prog.sceo
$ main --run prog.sceo
- : String = "\\f. \\x. f (f (f (f x)))  ;  a  ;  parse error: expected ')'"
```

The first result is Church `2 + 2` normalizing to Church `4`; the second is
`(\x.\y. x) a b` reducing to `a`; the third is a malformed input handled
in-language. The suite also runs the whole interpreter under node, with `str`
compiled as its own wasm module behind the link module.
