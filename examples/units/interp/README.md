# interp

A modular interpreter: the AST is an algebraic data type
(`type expr = | Lit of Int | Add of expr * expr` — sugar over an
iso-recursive union), and each pass is its own compilation unit. `eval` and
`show` import *nothing* — each redeclares the type and matches on the
structure directly, so a new pass can be written, compiled, and linked
without touching (or even having) the constructors' unit. Only the driver
imports all three.

```console
$ main -c ast.sce -o ast.sceo
$ main -c eval.sce -o eval.sceo
$ main -c show.sce -o show.sceo
$ main -c main.sce -o main.sceo
$ main --link ast.sceo eval.sceo show.sceo main.sceo -o all.sceo
$ main --run all.sceo
- : String = "((1 + 2) + 39) = 42"
```

The generated `Ast.scei` spells the recursive type out structurally — the
ADT sugar leaves no trace in the interface:

```
{lit : Int -> (mu a. Int | {_1 : a} & {_2 : a})} & {add : ...}
```

so agreement between passes is checked field by field at link time — no
nominal type (and no constructor names) have to survive separate
compilation, and the passes may be linked in any order before the driver.
