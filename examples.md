# SCE-Lang: the examples, with all code

SCE-Lang is an ML-flavoured surface language for **λSCE**, a merge calculus
with first-class modules, elaborating to **λE**, a calculus with first-class
environments and *no variables*: `?` denotes the entire context, `?.n`
projects its n-th component, and the surface language's job is to turn names
into positions. Interfaces are ordinary structural types, modules and
functors are ordinary terms, and linking is ordinary evaluation — so separate
compilation, dynamic loading, and capability control are one mechanism seen
at three times. Every example below is a live test fixture: the suite runs
each on every commit, through the interpreter and (where applicable) a
WasmGC backend under node, and all paths must agree.

Single files run directly:

```console
$ dune exec bin/main.exe examples/modules.sce
$ dune exec bin/main.exe -- --wasm out.wasm examples/modules.sce && node wasm/run.js out.wasm
```

Unit sets and capability examples use the separate-compilation CLI shown in
each section (`main` abbreviates `dune exec bin/main.exe --`).

Conventions worth knowing before reading:

- **Running artifacts:** `--run` executes a linked artifact's `main` export
  if it has one; otherwise the module value itself is the result. Whole
  files without a trailing `;; expr` evaluate to the record of their
  top-level bindings.
- **Notation vs the paper:** the surface `Top` is the paper's unit/empty
  type ε; surface `,,` is the paper's parallel merge and `,,,` its dependent
  merge; `?` is the paper's environment query.
- **Elided primitives:** `Bool`, `String`, comparison and arithmetic
  operators (`&&`, `mod`, `/`, …) are implementation primitives layered on
  the formalized calculus, which has only `Int` and ε as base types.

---

## 1. The tour: single files

Six files introduce the language layer by layer.

### 1.1 basics — literals, records, recursion

The ML-flavoured baseline: type aliases, annotated parameters, `let rec`
with a return annotation (typing is synthesis-only), records and projection.
A program without a trailing `;; expr` evaluates to the record of its
top-level bindings.

#### `examples/basics.sce`

```ocaml
(* Literals, primitives, functions and records. *)

type Point = { x : Int; y : Int }

let origin : Point = { x = 0; y = 0 }

let move (p : Point) (dx : Int) : Point = { x = p.x + dx; y = p.y }

let rec fact (n : Int) : Int = if n <= 1 then 1 else n * fact (n - 1)

let describe (p : Point) : String =
  if p.x = 0 && p.y = 0 then "origin" else "somewhere else"

;; { shifted = (move origin 7).x
   ; five    = fact 5
   ; what    = describe origin
   ; joined  = "a" ^ "b" ^ "c"
   }
```

### 1.2 merges — the two merges

`,,` is non-dependent (both sides checked in the same context); `,,,` is
dependent (the right side sees the left) — the difference structs are built
on. `linkall` satisfies every labelled import of a functor at once.

#### `examples/merges.sce`

```ocaml
(* The two merges.

   `,,` is non-dependent: both sides are checked in the same context.
   `,,,` is dependent: the right side additionally sees the left one, which is
   how a struct lets a later declaration use an earlier one. *)

let plain = { a = 1 } ,, { b = 2 }

let dependent = { a = 1 } ,,, { b = a + 1 }

(* `linkall` satisfies every labelled import at once. *)
module Parts = struct
  let width : Int = 3
  let height : Int = 4
end

module Area =
  linkall Parts with functor (X : { width : Int } & { height : Int }) -> struct
    let area : Int = X.width * X.height
  end

;; { p = plain.b; d = dependent.b; area = Area.area }
```

### 1.3 unions — the raw union primitives

Unions are eliminated with `case`; both branches must have the same type,
and an injection needs an ascription so the other side is known. These are
the primitives the ADT sugar (1.5) desugars to.

#### `examples/unions.sce`

```ocaml
(* Unions are eliminated with `case`. Both branches must have the same type,
   and an injection needs an ascription so the other side is known. These are
   the raw primitives; adt.sce shows the datatype sugar layered on them. *)

type Tagged = Int | String

let tag (n : Int) : Tagged =
  if n < 0 then (inr "negative" : Tagged) else (inl n : Tagged)

let render (v : Tagged) : String =
  case v of
    | inl n -> if n = 0 then "zero" else "positive"
    | inr s -> s
  end

;; { neg = render (tag (0 - 1)); zero = render (tag 0); pos = render (tag 9) }
```

### 1.4 recursive — iso-recursive types by hand

`mu a. A` binds `a` in `A`; `fold` needs an ascription naming the recursive
type, `unfold` peels one layer. A recursive ADT desugars to exactly this.

#### `examples/recursive.sce`

```ocaml
(* Iso-recursive types. `mu a. A` binds `a` in `A`; `fold` needs an ascription
   naming the recursive type, and `unfold` peels one layer off. These are the
   raw primitives; a recursive ADT (adt.sce) desugars to exactly this. *)

type Nat = mu a. Top | a

let zero : Nat = (fold (inl () : Top | Nat) : mu a. Top | a)

let succ (n : Nat) : Nat = (fold (inr n : Top | Nat) : mu a. Top | a)

let is_zero (n : Nat) : Bool =
  case unfold n of
    | inl u -> true
    | inr m -> false
  end

;; { z = is_zero zero; one = is_zero (succ zero) }
```

### 1.5 adt — datatypes as pure sugar

A declaration with a leading `|` becomes a plain alias over binary unions,
records, and `mu`; constructors and `match` become the ascribed
`inl`/`inr`/`fold`/`case` a user writes by hand. Nothing downstream changes —
the sugar costs zero new metatheory, and the interfaces it leaves behind are
fully structural (constructor names are surface-only).

#### `examples/adt.sce`

```ocaml
(* Algebraic data types are sugar: a declaration with a leading `|` becomes a
   plain type alias over binary unions, records, and `mu`; constructors and
   `match` become the ascribed inl/inr/fold/case a user writes by hand. *)

type shape =
  | Circle of Int
  | Rect of Int * Int
  | Point

let area (s : shape) : Int =
  match s with
  | Circle r -> r * r * 3
  | Rect (w, h) -> w * h
  | Point -> 0
  end

(* A recursive payload wraps the alias in `mu`; fold/unfold appear on their
   own. Tuple payloads are records with fields _1 .. _n, so `(a, b)` is an
   ordinary tuple expression. *)
type expr =
  | Lit of Int
  | Add of expr * expr

let rec eval (e : expr) : Int =
  match e with
  | Lit n -> n
  | Add (a, b) -> eval a + eval b
  end

(* Nullary-only types are enums; `_` is the catch-all arm. *)
type color = | Red | Green | Blue

let warm (c : color) : Bool =
  match c with
  | Red -> true
  | _ -> false
  end

;; { rect = area (Rect (4, 5));
    sum = eval (Add (Add (Lit 1, Lit 2), Lit 39));
    red = warm Red; blue = warm Blue }
```

### 1.6 modules — structs, functors, sandboxing, linking

The module layer in one file — including the no-subtyping story: types are
compared with structural *equality*, so `Doubler(Counter)` is rejected
(Counter's type is wider than the import) while `link Counter with Doubler`
copes, by looking the imported labels up and keeping both halves.
`sandbox struct` elaborates under the empty context: nothing from outside is
reachable inside.

#### `examples/modules.sce`

```ocaml
(* Structures, functors, sandboxing and linking.

   A `struct` is a dependent merge chain, so a declaration can use the ones
   before it. A `sandbox struct` elaborates under Top instead of the enclosing
   context, so nothing from outside is reachable inside it. *)

module Counter = struct
  let start : Int = 10
  let bump (n : Int) : Int = n + 1
  let started : Int = bump start
end

module Secret = sandbox struct
  let key : Int = 42
end

(* A functor's parameter is its import interface; `X.start` resolves through
   the signature written right here. *)
module Doubler (X : { start : Int }) = struct
  let doubled : Int = X.start * 2
end

(* There is no subtyping: `Doubler(Counter)` would be rejected, because
   Counter's type is wider than `{ start : Int }`. Direct application needs an
   argument of exactly the import type. *)
module Applied = Doubler({ start = Counter.start })

(* Linking is the mechanism that does cope with a wider module: it looks the
   imported labels up in it and keeps both halves in the result. *)
module Linked =
  link Counter with functor (X : { start : Int }) -> struct
    let next : Int = X.start + 1
  end

(* `open` brings a module's fields into scope for what follows. *)
open Counter

;; { started = started
   ; doubled = Applied.doubled
   ; next    = Linked.next
   ; secret  = Secret.key
   }
```

---

## 2. Separate compilation: the `units/` case studies

A unit compiles to a binary artifact (`.sceo`) holding a closed core term,
and emits a human-readable interface (`.scei`) alongside; you compile
against interfaces and link against implementations. A unit is wrapped as a
**sandboxed functor** from its imports to its exports — closed by the
calculus itself, not by toolchain discipline. The linker is a left fold of
the very composition term the in-language `link`/`linkall` elaborate to,
and every set below also ships `whole.sce`, the same program as one file:
the test suite drives each set through every path (whole interpreted,
whole→wasm, core-linked one-shot / incrementally / permuted,
core-linked→wasm, wasm-level-linked) and requires one answer.

### 2.1 hello — the smallest realistic split

Two independent leaf providers and a consumer; since `counter` and `fmt`
are independent, link order commutes.

```console
$ main -c counter.sce -o counter.sceo      # writes Counter.scei
$ main -c fmt.sce -o fmt.sceo              # writes Fmt.scei
$ main -c app.sce -o app.sceo              # imports resolve against the .scei files
$ main --link counter.sceo fmt.sceo app.sceo -o prog.sceo
$ main --run prog.sceo
- : String = "[yes]"
```

#### `examples/units/hello/counter.sce`

```ocaml
(* A leaf unit: no imports. Compiling it writes Counter.scei next to the
   artifact, so downstream units can say just `import Counter`. *)

module Counter = struct
  let start : Int = 10
  let bump (n : Int) : Int = n + 1
end
```

#### `examples/units/hello/fmt.sce`

```ocaml
(* A second leaf unit, so linking exercises more than one provider. *)

module Fmt = struct
  let bracket (s : String) : String = "[" ^ s ^ "]"
  let yes (b : Bool) : String = if b then "yes" else "no"
end
```

#### `examples/units/hello/app.sce`

```ocaml
(* The consumer: both imports resolve against the generated .scei files.
   This whole file compiles to a sandboxed functor from its imports to its
   exports — linking applies it to projections wired out of the providers. *)

import Counter
import Fmt

module App = struct
  let level : Int = Counter.bump (Counter.bump Counter.start)
  let big : Bool = level > 11
end

let main : String = Fmt.bracket (Fmt.yes App.big)
```

#### `examples/units/hello/whole.sce`

```ocaml
(* The three units of this directory as one program — the twin the test suite
   diffs every linking path against. *)

module Counter = struct
  let start : Int = 10
  let bump (n : Int) : Int = n + 1
end

module Fmt = struct
  let bracket (s : String) : String = "[" ^ s ^ "]"
  let yes (b : Bool) : String = if b then "yes" else "no"
end

module App = struct
  let level : Int = Counter.bump (Counter.bump Counter.start)
  let big : Bool = level > 11
end

;; Fmt.bracket (Fmt.yes App.big)
```

### 2.2 diamond — provider sharing is the default

`left` and `right` both import `Lib`; `top` imports both sides. The linker
installs **one** copy of `Lib` and both importers' checks resolve against
it — no double inclusion, no coordination beyond the shared interface. The
sides link in either order. (The dual policy — two providers exporting the
*same* label — is rejected eagerly; see `versions`, 3.5.)

```console
$ main --link lib.sceo left.sceo right.sceo top.sceo -o all.sceo
$ main --run all.sceo
- : Int = 31
$ main --link lib.sceo right.sceo left.sceo top.sceo -o alt.sceo
$ main --run alt.sceo
- : Int = 31
```

#### `examples/units/diamond/lib.sce`

```ocaml
(* The shared provider at the top of the diamond: linked once, its exports
   satisfy every downstream import of `Lib`. *)

module Lib = struct
  let base : Int = 10
  let scale (n : Int) : Int = n * 2
end
```

#### `examples/units/diamond/left.sce`

```ocaml
(* One side of the diamond: uses Lib's data. *)

import Lib

module Left = struct
  let value : Int = Lib.base + 1
end
```

#### `examples/units/diamond/right.sce`

```ocaml
(* The other side: uses Lib's function. Both sides check against the same
   Lib.scei, and linking installs a single copy of Lib for both. *)

import Lib

module Right = struct
  let value : Int = Lib.scale Lib.base
end
```

#### `examples/units/diamond/top.sce`

```ocaml
(* The bottom of the diamond: both sides arrive, each built over the one
   shared Lib. *)

import Left
import Right

let main : Int = Left.value + Right.value
```

#### `examples/units/diamond/whole.sce`

```ocaml
(* The four units of this directory as one program — the twin the test suite
   diffs every linking path against. *)

module Lib = struct
  let base : Int = 10
  let scale (n : Int) : Int = n * 2
end

module Left = struct
  let value : Int = Lib.base + 1
end

module Right = struct
  let value : Int = Lib.scale Lib.base
end

;; Left.value + Right.value
```

### 2.3 peano — structural types replace nominal sharing

A recursive ADT crossing unit boundaries. `nat.sce` declares
`type nat = | Z | S of nat`; `arith.sce` declares its *own* ADT with its own
constructor names (`Zero`/`Next`). Structural equality is what makes them
compatible: neither the type nor the constructors have to be shared between
separately compiled units — the direct answer to ML's `with type` sharing
machinery. `fold`ed values built in one unit are `unfold`ed in another.

```console
$ main --link nat.sceo arith.sceo demo.sceo -o prog.sceo
$ main --run prog.sceo
- : Int = 9
```

#### `examples/units/peano/nat.sce`

```ocaml
(* Peano numerals as an ADT — sugar over the iso-recursive union
   mu a. Top | a (see examples/recursive.sce for the raw encoding). The
   .scei this generates spells the type out structurally, so consumers need
   no shared nominal declaration. *)

type nat = | Z | S of nat

module Nat = struct
  let zero : nat = Z
  let succ (n : nat) : nat = S n
  let rec add (m : nat) (n : nat) : nat =
    match m with
    | Z -> n
    | S p -> S (add p n)
    end
  let rec mul (m : nat) (n : nat) : nat =
    match m with
    | Z -> Z
    | S p -> add n (mul p n)
    end
  let rec toint (n : nat) : Int =
    match n with
    | Z -> 0
    | S p -> 1 + toint p
    end
end
```

#### `examples/units/peano/arith.sce`

```ocaml
(* This unit declares its own ADT with its own constructor names; it matches
   Nat's because types are compared structurally — neither the type nor the
   constructors have to survive separate compilation. *)

import Nat

type nat = 
  | Zero 
  | Next of nat

module Arith = struct
  let two : nat = Next (Next Zero)
  let three : nat = Nat.succ two
  let six : nat = Nat.mul two three
end
```

#### `examples/units/peano/demo.sce`

```ocaml
(* Folded values built in one unit are unfolded and recursed over in another. *)

import Nat
import Arith

let main : Int = Nat.toint (Nat.add Arith.six Arith.three)
```

#### `examples/units/peano/whole.sce`

```ocaml
(* The three units of this directory as one program. *)

type nat = | Z | S of nat

module Nat = struct
  let zero : nat = Z
  let succ (n : nat) : nat = S n
  let rec add (m : nat) (n : nat) : nat =
    match m with
    | Z -> n
    | S p -> S (add p n)
    end
  let rec mul (m : nat) (n : nat) : nat =
    match m with
    | Z -> Z
    | S p -> add n (mul p n)
    end
  let rec toint (n : nat) : Int =
    match n with
    | Z -> 0
    | S p -> 1 + toint p
    end
end

module Arith = struct
  let two : nat = S (S Z)
  let three : nat = Nat.succ two
  let six : nat = Nat.mul two three
end

;; Nat.toint (Nat.add Arith.six Arith.three)
```

### 2.4 interp — modular passes over a shared structural AST

A modular interpreter: the AST is an ADT, and each pass is its own unit.
`eval` and `show` import *nothing* — each redeclares the type and matches on
the structure directly, so a new pass can be written, compiled, and linked
without touching (or even having) the constructors' unit. The generated
`Ast.scei` spells the recursive type out structurally; agreement between
passes is checked field by field at link time.

```console
$ main --link ast.sceo eval.sceo show.sceo main.sceo -o all.sceo
$ main --run all.sceo
- : String = "((1 + 2) + 39) = 42"
```

#### `examples/units/interp/ast.sce`

```ocaml
(* The shared AST as an algebraic data type. The .scei spells the type out
   structurally, so passes need no shared nominal declaration. *)

type expr = | Lit of Int | Add of expr * expr

module Ast = struct
  let lit (n : Int) : expr = Lit n
  let add (x : expr) (y : expr) : expr = Add (x, y)
end
```

#### `examples/units/interp/eval.sce`

```ocaml
(* An evaluation pass. It imports nothing: it redeclares the type and matches
   on the structure — compatibility with Ast's values is structural. *)

type expr = | Lit of Int | Add of expr * expr

module Eval = struct
  let rec run (e : expr) : Int =
    match e with
    | Lit n -> n
    | Add (a, b) -> run a + run b
    end
end
```

#### `examples/units/interp/show.sce`

```ocaml
(* A pretty-printing pass — same shape as Eval, independent of it. Decimal
   rendering is written in the language (^ and = are the only string
   primitives). *)

type expr = | Lit of Int | Add of expr * expr

module Show = struct
  let digit (d : Int) : String =
    if d = 0 then "0" else if d = 1 then "1" else if d = 2 then "2"
    else if d = 3 then "3" else if d = 4 then "4" else if d = 5 then "5"
    else if d = 6 then "6" else if d = 7 then "7" else if d = 8 then "8"
    else "9"
  let rec go (n : Int) : String =
    if n < 10 then digit n else go (n / 10) ^ digit (n mod 10)
  let int (n : Int) : String =
    if n < 0 then "-" ^ go (0 - n) else go n
  let rec expr (e : expr) : String =
    match e with
    | Lit n -> int n
    | Add (a, b) -> "(" ^ expr a ^ " + " ^ expr b ^ ")"
    end
end
```

#### `examples/units/interp/main.sce`

```ocaml
(* The driver links the passes. It has its own structurally identical ADT, so
   locally built constructors and Ast's builders are interchangeable. *)

import Ast
import Eval
import Show

type expr = | Lit of Int | Add of expr * expr

let e = Add (Add (Ast.lit 1, Lit 2), Lit 39)

let main : String = Show.expr e ^ " = " ^ Show.int (Eval.run e)
```

#### `examples/units/interp/whole.sce`

```ocaml
(* The four units of this directory as one program — the twin the test suite
   diffs every linking path against. *)

type expr = | Lit of Int | Add of expr * expr

module Ast = struct
  let lit (n : Int) : expr = Lit n
  let add (x : expr) (y : expr) : expr = Add (x, y)
end

module Eval = struct
  let rec run (e : expr) : Int =
    match e with
    | Lit n -> n
    | Add (a, b) -> run a + run b
    end
end

module Show = struct
  let digit (d : Int) : String =
    if d = 0 then "0" else if d = 1 then "1" else if d = 2 then "2"
    else if d = 3 then "3" else if d = 4 then "4" else if d = 5 then "5"
    else if d = 6 then "6" else if d = 7 then "7" else if d = 8 then "8"
    else "9"
  let rec go (n : Int) : String =
    if n < 10 then digit n else go (n / 10) ^ digit (n mod 10)
  let int (n : Int) : String =
    if n < 0 then "-" ^ go (0 - n) else go n
  let rec expr (e : expr) : String =
    match e with
    | Lit n -> int n
    | Add (a, b) -> "(" ^ expr a ^ " + " ^ expr b ^ ")"
    end
end

let e = Add (Add (Ast.lit 1, Lit 2), Lit 39)

;; Show.expr e ^ " = " ^ Show.int (Eval.run e)
```

### 2.5 geometry — functor closures cross wasm instances

`shapes.sce` exports the functor `Scale` (its generated interface is the
signature `{k : Int} => {by : Int -> Int}`); `report.sce` imports and
applies it. Under wasm-level linking this is the strongest form of the
claim: the `Scale` closure is a GC struct created by `shapes.wasm`'s
instance, and `report`'s code `call_ref`s it across instances — WasmGC
structural type identity carrying the same bet the source type system makes.

```console
$ main --link vec.sceo shapes.sceo report.sceo -o prog.sceo
$ main --run prog.sceo
- : Int = 49
```

#### `examples/units/geometry/vec.sce`

```ocaml
(* A leaf unit of plain arithmetic. *)

module Vec = struct
  let dot (x1 : Int) (y1 : Int) (x2 : Int) (y2 : Int) : Int = x1 * x2 + y1 * y2
  let norm2 (x : Int) (y : Int) : Int = dot x y x y
end
```

#### `examples/units/geometry/shapes.sce`

```ocaml
(* Exports a plain module *and* a functor. The functor's .scei is a signature
   ({k : Int} => {by : Int -> Int}), so a consumer unit can import it and apply
   it — a functor value crossing a unit boundary. *)

import Vec

module Shapes = struct
  let area (w : Int) (h : Int) : Int = w * h
  let diag2 (w : Int) (h : Int) : Int = Vec.norm2 w h
end

module Scale (K : { k : Int }) = struct
  let by (n : Int) : Int = n * K.k
end
```

#### `examples/units/geometry/report.sce`

```ocaml
(* Applies the imported functor: under wasm-level linking, the closure was
   built by shapes.wasm's instance and is called from this unit's code. *)

import Shapes
import Scale

module Doubler = Scale({ k = 2 })

let main : Int = Doubler.by (Shapes.area 3 4) + Shapes.diag2 3 4
```

#### `examples/units/geometry/whole.sce`

```ocaml
(* The three units of this directory as one program. *)

module Vec = struct
  let dot (x1 : Int) (y1 : Int) (x2 : Int) (y2 : Int) : Int = x1 * x2 + y1 * y2
  let norm2 (x : Int) (y : Int) : Int = dot x y x y
end

module Shapes = struct
  let area (w : Int) (h : Int) : Int = w * h
  let diag2 (w : Int) (h : Int) : Int = Vec.norm2 w h
end

module Scale (K : { k : Int }) = struct
  let by (n : Int) : Int = n * K.k
end

module Doubler = Scale({ k = 2 })

;; Doubler.by (Shapes.area 3 4) + Shapes.diag2 3 4
```

### 2.6 textlib — both linking levels in one program

`show.sce` renders decimals with recursion (the core has no int-to-string
primitive); `summary.sce` is linked *by the toolchain* while its own body
uses the language's first-class `linkall` — the toolchain's linker and the
calculus's linking construct are the same mechanism, so they compose.

```console
$ main --link show.sceo csv.sceo summary.sceo -o prog.sceo
$ main --run prog.sceo
- : String = "35,70,-35"
```

#### `examples/units/textlib/show.sce`

```ocaml
(* Decimal rendering written in the language itself: the core's only string
   primitives are ^ and =, so digits come from recursion over / and mod. *)

module Show = struct
  let digit (d : Int) : String =
    if d = 0 then "0" else if d = 1 then "1" else if d = 2 then "2"
    else if d = 3 then "3" else if d = 4 then "4" else if d = 5 then "5"
    else if d = 6 then "6" else if d = 7 then "7" else if d = 8 then "8"
    else "9"
  let rec go (n : Int) : String =
    if n < 10 then digit n else go (n / 10) ^ digit (n mod 10)
  let int (n : Int) : String =
    if n < 0 then "-" ^ go (0 - n) else go n
end
```

#### `examples/units/textlib/csv.sce`

```ocaml
(* A middle unit: consumes Show, is consumed by summary. *)

import Show

module Csv = struct
  let cell (n : Int) : String = Show.int n
  let row (a : Int) (b : Int) (c : Int) : String =
    cell a ^ "," ^ cell b ^ "," ^ cell c
end
```

#### `examples/units/textlib/summary.sce`

```ocaml
(* Both linking levels in one program: this unit is linked by the toolchain,
   while its body links Stats with a functor using the language's own
   first-class `linkall`. *)

import Csv

module Stats = struct
  let lo : Int = 7
  let hi : Int = 42
end

module Spread = linkall Stats with functor (X : { lo : Int } & { hi : Int }) ->
  struct let range : Int = X.hi - X.lo end

let main : String = Csv.row Spread.range (Spread.range * 2) (0 - Spread.range)
```

#### `examples/units/textlib/whole.sce`

```ocaml
(* The three units of this directory as one program. *)

module Show = struct
  let digit (d : Int) : String =
    if d = 0 then "0" else if d = 1 then "1" else if d = 2 then "2"
    else if d = 3 then "3" else if d = 4 then "4" else if d = 5 then "5"
    else if d = 6 then "6" else if d = 7 then "7" else if d = 8 then "8"
    else "9"
  let rec go (n : Int) : String =
    if n < 10 then digit n else go (n / 10) ^ digit (n mod 10)
  let int (n : Int) : String =
    if n < 0 then "-" ^ go (0 - n) else go n
end

module Csv = struct
  let cell (n : Int) : String = Show.int n
  let row (a : Int) (b : Int) (c : Int) : String =
    cell a ^ "," ^ cell b ^ "," ^ cell c
end

module Stats = struct
  let lo : Int = 7
  let hi : Int = 42
end

module Spread = linkall Stats with functor (X : { lo : Int } & { hi : Int }) ->
  struct let range : Int = X.hi - X.lo end

;; Csv.row Spread.range (Spread.range * 2) (0 - Spread.range)
```

---

## 3. Effects and runtime linking

The language has no print statement. `Sys` (`print`, `readfile`), `Str`
(`head`, `tail`), and `Loader` are provider units the *host* materializes; a
program has exactly the authority its link line grants, and everything else
about capabilities — attenuation, delegation, confinement — is ordinary
code. Runtime linking needed no new construct, only a way for a unit value
to *arrive* at run time:

```ocaml
import Loader : { load : String -> (Sig | {err : String}) }
```

The declared success type is the contract: `load` unmarshals an artifact,
compares its stored interface against `Sig` structurally — the static
linker's check, made later — and returns a union the program cases on.

### 3.1 effects — authority flows through the link line

`--link sys` grants IO. `sandbox` is effect confinement: the sandboxed
`Pure` module cannot even mention `Sys` (a compile-time scope error), so it
provably performs no IO. Attenuation is ordinary code: `Log.info` is
`Sys.print` wrapped with a prefix.

```console
$ main -c app.sce -o app.sceo       # `import Sys` uses the built-in interface
$ main --link sys app.sceo -o prog.sceo
$ main --run prog.sceo
[app] greeting world
[app] greeting again
- : String = "hello, world / hello, again"
```

#### `examples/effects/app.sce`

```ocaml
(* Effects enter through linking: `sys` is a host-built provider unit, and
   this unit gets IO only because the link line grants it. *)

import Sys

module Log = struct
  let info (s : String) : Top = Sys.print ("[app] " ^ s)
end

module Greeter = struct
  let hello (name : String) : String =
    let noted : Top = Log.info ("greeting " ^ name) in
    "hello, " ^ name
end

(* A sandboxed struct cannot reach Sys — or Log — at all: mentioning either
   in here is a *scope error*, not a runtime denial. *)
module Pure = sandbox struct
  let double (n : Int) : Int = n * 2
end

let main : String =
  let a : String = Greeter.hello "world" in
  let b : String = Greeter.hello "again" in
  a ^ " / " ^ b
```

### 3.2 boot — construction-time effects meet the linker

The provider prints *while its exports are being built* — not inside any
function a caller might invoke later — and the consumer imports **two**
labels from it, so the linker's wire projects the provider twice. One line,
not three: every operand of a merge or link is bound exactly once, so a
unit's effects fire exactly once, in link-line order, however many imports
are wired out of it. A composition term that spliced the provider into the
wire would print `loading provider` three times here. This is the
operational pin for the linearized elaboration; the in-language counterpart
(a `linkall` whose provider prints) is pinned in the same suite. A
corollary: link *order* commutes for values but not for traces — which is
why permutation tests compare values while trace tests fix the link line.

```console
$ main -c provider.sce -o provider.sceo    # writes A1.scei, A2.scei
$ main -c consumer.sce -o consumer.sceo
$ main --link sys provider.sceo consumer.sceo -o prog.sceo
$ main --run prog.sceo
loading provider
- : Int = 3
```

#### `examples/boot/provider.sce`

```ocaml
(* A provider with a construction-time effect: the print fires while the
   unit's exports are being built, not inside any exported function. The
   linker binds each unit exactly once, so linking this into a consumer with
   two imports still prints one line — a composition term that spliced the
   provider into the wire would print once per wired import, plus once. *)

import Sys

module A1 = struct let v : Int = 1 end
module A2 = struct let w : Int = 2 end

let boot : Top = Sys.print "loading provider"
```

#### `examples/boot/consumer.sce`

```ocaml
(* Two imports from the same provider: the wire projects two labels, and the
   provider's boot line must still appear exactly once. *)

import A1
import A2

let main : Int = A1.v + A2.w
```

### 3.3 plugins — a plugin manager, with confinement as a scope error

The manager loads plugin artifacts at run time, interface-checks them, and
instantiates each with the language's own `link`, *at the use site*:
`(link { Cap = ... } with p).run name` — first-class linking applied to a
functor that arrived from disk. The wire is label-preserving rather than
renaming, so the host aligns labels by building the capability record under
the label the plugin imports. A plugin is a sandboxed functor from the
capabilities it is handed to its exports — `evil.sce` tries to call `Sys`
directly and *does not compile* (the test suite pins the failure stage). Two
loaded plugins cannot see each other unless the manager wires them. A
missing artifact is a value, not a crash.

```console
$ main --link sys loader manager.sceo -o prog.sceo
$ main --run prog.sceo
[shout] making some noise
[quiet] staying quiet
- : String = "shout! (quiet) <cannot open artifact: ghost.sceo: No such file or directory>"
```

#### `examples/plugins/shout.sce`

```ocaml
(* A plugin: a sandboxed functor from the capabilities it is handed to its
   exports. It can log — because the manager passes a log capability — and
   nothing else. *)

import Cap : { log : String -> Top }

let run (msg : String) : String =
  let noted : Top = Cap.log "making some noise" in
  msg ^ "!"
```

#### `examples/plugins/quiet.sce`

```ocaml
(* A second plugin with the same interface and different behavior. *)

import Cap : { log : String -> Top }

let run (msg : String) : String =
  let noted : Top = Cap.log "staying quiet" in
  "(" ^ msg ^ ")"
```

#### `examples/plugins/evil.sce`

```ocaml
(* This plugin tries to reach Sys directly instead of going through the
   capability it was handed. It does not compile: `Sys` is an unbound variable
   inside a sandboxed unit — confinement is a scope error, not a runtime
   denial. Try it:

     $ main -c evil.sce -o evil.sceo
     3:29: scope error: unbound variable 'Sys'

   (Kept as a negative fixture; the test suite asserts the rejection.) *)

let run (msg : String) : String =
  let stolen : Top = Sys.print "escaped the sandbox!" in
  msg
```

#### `examples/plugins/manager.sce`

```ocaml
(* A plugin manager: loads plugin artifacts at run time, interface-checks
   them, and links each against an *attenuated* capability record. The loader
   is itself a capability whose type declares the interface every plugin must
   satisfy — the same structural check the static linker makes, made later. *)

import Sys
import Loader : { load : String ->
  (({Cap : {log : String -> Top}} => {run : String -> String}) | {err : String}) }

(* A local view on the loader's union: constructor names are surface-only, so
   an ADT with the same payloads matches the host's result type exactly. *)
type loaded =
  | Plugin of (({Cap : {log : String -> Top}}) => {run : String -> String})
  | Failed of {err : String}

module Caps = struct
  (* each plugin logs through its own prefix and can do nothing else *)
  let for_plugin (name : String) : { log : String -> Top } =
    { log = fun (s : String) -> Sys.print ("[" ^ name ^ "] " ^ s) }
end

(* Linking at the use site: the capability record is built under the label
   the plugin imports, `link` wires it in and keeps both halves, and `run` is
   projected out of the result — dynamic linking as an ordinary expression. *)
let plug (name : String) (path : String) : String =
  match Loader.load path with
  | Plugin p -> (link { Cap = Caps.for_plugin name } with p).run name
  | Failed e -> "<" ^ e.err ^ ">"
  end

let main : String =
  plug "shout" "shout.sceo" ^ " " ^
  plug "quiet" "quiet.sceo" ^ " " ^
  plug "ghost" "ghost.sceo"
```

### 3.4 dynconfig — runtime product lines

A one-line config file names which artifact gets linked. `plain` and `fancy`
are leaf units with the same interface; `chooser` reads `skin.txt` and loads
whichever it names. Swapping implementations recompiles nothing; a missing
or stale artifact is an `inr` value the program handles.

```console
$ main --link sys loader chooser.sceo -o prog.sceo
$ printf 'fancy.sceo' > skin.txt
$ main --run prog.sceo
- : String = "** hello **"
$ printf 'plain.sceo' > skin.txt
$ main --run prog.sceo
- : String = "hello"
```

#### `examples/dynconfig/plain.sce`

```ocaml
(* A leaf implementation unit; loadable because leaves are unit values too. *)

module Skin = struct
  let render (s : String) : String = s
end
```

#### `examples/dynconfig/fancy.sce`

```ocaml
(* Same interface, different implementation. *)

module Skin = struct
  let render (s : String) : String = "** " ^ s ^ " **"
end
```

#### `examples/dynconfig/chooser.sce`

```ocaml
(* Configuration-driven runtime linking: a config file names the artifact to
   load, so swapping the implementation means editing one line of text — no
   recompilation of anything. *)

import Sys
import Loader : { load : String ->
  (({Skin : {render : String -> String}}) | {err : String}) }

(* Local views on the host unions: readfile and load return plain binary
   unions, and an ADT with the same payloads names their branches. *)
type file = | Contents of String | NoFile of {err : String}
type skin = | Loaded of {Skin : {render : String -> String}}
            | Missing of {err : String}

let main : String =
  let path : String =
    match Sys.readfile "skin.txt" with
    | Contents p -> p
    | NoFile e -> "plain.sceo"
    end
  in
  match Loader.load path with
  | Loaded s -> s.Skin.render "hello"
  | Missing e -> "no skin: " ^ e.err
  end
```

### 3.5 versions — dependency hell becomes a wiring decision

Two versions of `module Lib` with the same interface. Linking both
statically is rejected — same-name coexistence is an ambiguity, caught at
link time with both units named:

```console
$ main --link libv1.sceo libv2.sceo client.sceo -o bad.sceo
link error: units libv1 and libv2 both export 'Lib'; the label would become ambiguous
```

But version choice is per *use site*: the client links v1 statically and
loads v2 where it wants it, so both versions run side by side under one
name. The loader's declared type is the version contract — an artifact whose
interface drifted comes back as `inr {err}`.

```console
$ main --link libv1.sceo loader client.sceo -o prog.sceo
$ main --run prog.sceo
- : String = "hello, world (v1) | HELLO, world (v2)"
```

#### `examples/versions/libv1.sce`

```ocaml
(* Version 1 of a library. *)

module Lib = struct
  let version : String = "v1"
  let greet (s : String) : String = "hello, " ^ s ^ " (v1)"
end
```

#### `examples/versions/libv2.sce`

```ocaml
(* Version 2: the same module name, the same interface, new behavior.
   Linking both versions statically is rejected — the label would be
   ambiguous — but nothing stops v2 from being *loaded* at a use site. *)

module Lib = struct
  let version : String = "v2"
  let greet (s : String) : String = "HELLO, " ^ s ^ " (v2)"
end
```

#### `examples/versions/client.sce`

```ocaml
(* Two versions of Lib in one program: v1 arrives statically through the link
   line, v2 is loaded at a use site. The choice of version is per use site,
   not per program. *)

import Lib
import Loader : { load : String ->
  (({Lib : {version : String; greet : String -> String}}) | {err : String}) }

type fetched =
  | V2 of {Lib : {version : String; greet : String -> String}}
  | NoV2 of {err : String}

let main : String =
  let old : String = Lib.greet "world" in
  match Loader.load "libv2.sceo" with
  | V2 m -> old ^ " | " ^ m.Lib.greet "world"
  | NoV2 e -> old ^ " | no v2: " ^ e.err
  end
```

### 3.6 wiring — delegation is a record field

Both plugins satisfy the same ABI — a functor from `{log, peer}`
capabilities to `{run}` — and neither can name, load, or observe the other.
The host wires `exclaim`'s exported `run` in as `chain`'s `peer` capability:
one plugin's authority over another exists exactly where the host
constructed it. No registry, no service lookup, no policy engine; isolation
is the default (`exclaim`'s own `peer` is the identity function).

```console
$ main --link sys loader host.sceo -o prog.sceo
$ main --run prog.sceo
[chain] chaining hi
[exclaim] exclaiming hi
- : String = "<hi!>"
```

#### `examples/wiring/exclaim.sce`

```ocaml
(* A plugin that only shouts. Its peer capability goes unused — what the
   manager wires in is invisible from here. *)

import Cap : { log : String -> Top; peer : String -> String }

let run (s : String) : String =
  let noted : Top = Cap.log ("exclaiming " ^ s) in
  s ^ "!"
```

#### `examples/wiring/chain.sce`

```ocaml
(* A plugin that decorates whatever its peer produces. It cannot name the
   other plugin, load anything, or reach Sys — `peer` is the one route it has,
   and the manager decides where that route leads. *)

import Cap : { log : String -> Top; peer : String -> String }

let run (s : String) : String =
  let noted : Top = Cap.log ("chaining " ^ s) in
  "<" ^ Cap.peer s ^ ">"
```

#### `examples/wiring/host.sce`

```ocaml
(* Delegation is manager-wired: chain's `peer` capability *is* exclaim's run
   function. The plugins never see each other — one plugin's authority over
   another exists only because the host built it into a capability record. *)

import Sys
import Loader : { load : String ->
  (({Cap : {log : String -> Top; peer : String -> String}}
      => {run : String -> String}) | {err : String}) }

type loaded =
  | Plugin of (({Cap : {log : String -> Top; peer : String -> String}})
                 => {run : String -> String})
  | Failed of {err : String}

module Caps = struct
  let log_for (name : String) : String -> Top =
    fun (s : String) -> Sys.print ("[" ^ name ^ "] " ^ s)
end

let idpeer (s : String) : String = s

let main : String =
  match Loader.load "exclaim.sceo" with
  | Plugin p ->
    let ex = p({ Cap = { log = Caps.log_for "exclaim"; peer = idpeer } }) in
    (match Loader.load "chain.sceo" with
     | Plugin q ->
       let ch = q({ Cap = { log = Caps.log_for "chain"; peer = ex.run } }) in
       ch.run "hi"
     | Failed e -> "<" ^ e.err ^ ">"
     end)
  | Failed e -> "<" ^ e.err ^ ">"
  end
```

### 3.7 upgrade — typed dynamic upgrade with state handoff

`appv1` runs statically linked; `appv2` is a functor whose import interface
— old `motto`, old `owner` — **is the migration contract**. The driver loads
v2 at run time and applies it to v1's exports: functor application is the
migration step, and the types say exactly which state the new version
inherits. A missing or drifted upgrade comes back as `inr {err}` and v1
keeps running — rollback is not a mechanism; it is the `inr` branch.

```console
$ main --link appv1.sceo loader driver.sceo -o prog.sceo
$ main --run prog.sceo
- : String = "v2 for jam (was: keep going)"
$ rm appv2.sceo
$ main --run prog.sceo
- : String = "still v1: keep going (cannot open artifact: appv2.sceo: No such file or directory)"
```

#### `examples/upgrade/appv1.sce`

```ocaml
(* The running version: a leaf unit, linked statically. Its exports are the
   state a future version will inherit. *)

module App = struct
  let motto : String = "keep going"
  let owner : String = "jam"
end
```

#### `examples/upgrade/appv2.sce`

```ocaml
(* The upgrade: a functor whose import interface *is* the migration contract.
   It cannot run without being handed the old version's state, and the types
   say exactly which pieces it inherits. *)

import Old : { motto : String; owner : String }

let banner : String = "v2 for " ^ Old.owner ^ " (was: " ^ Old.motto ^ ")"
let owner : String = Old.owner
```

#### `examples/upgrade/driver.sce`

```ocaml
(* Dynamic upgrade with typed state handoff: v1 is linked statically, v2
   arrives at run time as an artifact. Applying the loaded functor to v1's
   exports is the migration; a missing or mismatched upgrade is a value, and
   the program keeps running v1. *)

import App
import Loader : { load : String ->
  (({Old : {motto : String; owner : String}}
      => {banner : String; owner : String}) | {err : String}) }

type fetched =
  | Upgrade of (({Old : {motto : String; owner : String}})
                  => {banner : String; owner : String})
  | NoUpgrade of {err : String}

let main : String =
  match Loader.load "appv2.sceo" with
  | Upgrade up ->
    let next = up({ Old = { motto = App.motto; owner = App.owner } }) in
    next.banner
  | NoUpgrade e -> "still v1: " ^ App.motto ^ " (" ^ e.err ^ ")"
  end
```

---

## 4. The calculus at work

Four examples that only make sense in a language where environments are
values and linking is a term.

### 4.1 linkrec — recursive linking as a derived form

`Parity` is a functor whose import interface — `{ even : Int -> Bool }` — is
satisfied by its *own* export: an ordinary `let rec` ties the knot, so
mutual recursion (`even`/`odd`) closes through a single function-typed
import. This is exactly the shape the Lean mechanization proves sound:
recursive linking is a *derived form*, inheriting progress, preservation,
correctness, and determinism rather than needing its own metatheory. The
toolchain's linker deliberately stays acyclic — cross-unit recursion is out
of scope, matching the calculus.

```console
$ main parity.sce
- : {even10 : Bool} & {odd10 : Bool} & {even7 : Bool} = { even10 = true; odd10 = false; even7 = false }
```

#### `examples/linkrec/parity.sce`

```ocaml
(* Recursive linking as a derived form: a functor whose import is satisfied by
   its own export, tied with an ordinary let rec. This is the mechanization's
   derived recursive linking (`mrec_elab`, RecLinking.lean) written in surface
   syntax — no new primitive. Note the reading is generative: each recursive
   call re-applies the functor, so construction work repeats per call. *)

module Parity = functor (X : { even : Int -> Bool }) -> struct
  let odd (n : Int) : Bool = if n = 0 then false else X.even (n - 1)
  let even (n : Int) : Bool = if n = 0 then true else odd (n - 1)
end

(* The knot: the import each application receives is the function being
   defined, so the module's own export flows back in as its import. *)

let rec even (n : Int) : Bool = 
   let m = Parity({ even = even }) in 
   m.even n

let odd (n : Int) : Bool = 
   let m = Parity({ even = even }) in 
   m.odd n

;; { even10 = even 10; odd10 = odd 10; even7 = even 7 }
```

### 4.2 linker — the link step, written in the language it links

`link P with f` means: extend the world with the provider, wire its
exports into the functor's import record, keep both halves. That sentence is
a one-line program — `P ,,, f({ Seed = P.Seed })` — and because the builtin
construct elaborates to exactly this shape, the two must agree. `host.sce`
checks that at run time, on the *same* functor loaded from disk, comparing
field by field on both halves (whole-value agreement at these types, since
`=` is primitive-only). There is no linker formalism to trust: the linker's
composition term is an ordinary term of the calculus, one the program itself
can write.

```console
$ main --link loader host.sceo -o prog.sceo
$ main --run prog.sceo
- : String = "hand-written link = builtin link, both halves kept"
```

#### `examples/linker/step.sce`

```ocaml
(* A functor unit: the import interface is the record a linker must supply. *)

import Seed : { start : Int }

let bump : Int = Seed.start + 1
```

#### `examples/linker/host.sce`

```ocaml
(* The link step, written in the language it links — and checked against the
   builtin on the *same* loaded functor. `link P with f` means: extend the
   world with the provider, wire its export into the import record, keep both
   halves. The hand-written merge below is that sentence spelled out; the
   builtin elaborates to the same composition shape, so the two must agree —
   compared field by field on both halves, which at these types is the whole
   value (`=` is primitive-only). *)

import Loader : { load : String ->
  (({Seed : {start : Int}} => {bump : Int}) | {err : String}) }

type loaded =
  | Step of (({Seed : {start : Int}}) => {bump : Int})
  | Failed of {err : String}

module P = struct
  module Seed = struct let start : Int = 10 end
end

let main : String =
  match Loader.load "step.sceo" with
  | Step f ->
    let builtin = link P with f in
    let byhand = P ,,, f({ Seed = P.Seed }) in
    if (builtin.bump = byhand.bump)
       && (builtin.Seed.start = byhand.Seed.start)
       && (byhand.bump = P.Seed.start + 1)
    then "hand-written link = builtin link, both halves kept"
    else "disagreement"
  | Failed e -> "<" ^ e.err ^ ">"
  end
```

### 4.3 worlds — environments are values

Two environments arrive by different routes and both are entered with `box`:
`fancy.sceo` is loaded from disk — `box w in ?.Theme.decorate "hello"` runs
code under an environment that did not exist until run time — and `snap` is
the current world, captured with `let snap = ?` and re-entered when a load
fails: rollback is evaluating under a value you kept. Inside a box the body
sees *only* the world it was given; names from the enclosing scope do not
resolve.

```console
$ main --link loader host.sceo -o prog.sceo
$ main --run prog.sceo
- : String = "** hello ** / hello"
```

#### `examples/worlds/fancy.sce`

```ocaml
(* A world on disk: a leaf artifact whose value will be entered with box. *)

module Theme = struct
  let decorate (s : String) : String = "** " ^ s ^ " **"
end
```

#### `examples/worlds/host.sce`

```ocaml
(* Environments are values. One arrives from disk and is entered with `box`;
   another is the current world, captured with `?` and re-entered when the
   load fails. Inside a box the body sees only the world it was given — names
   from out here do not resolve. *)

import Loader : { load : String ->
  (({Theme : {decorate : String -> String}}) | {err : String}) }

type loaded =
  | World of {Theme : {decorate : String -> String}}
  | NoWorld of {err : String}

module Base = struct let decorate (s : String) : String = s end

(* the world as of this line, reified — Base is a field of it *)
let snap = ?

let themed (path : String) : String =
  match Loader.load path with
  | World w -> box w in ?.Theme.decorate "hello"
  | NoWorld e -> box snap in ?.Base.decorate "hello"
  end

let main : String = themed "fancy.sceo" ^ " / " ^ themed "ghost.sceo"
```

### 4.4 harness — one artifact, two worlds

`report.sce` is written against an interface — `{ fetch : String -> String }`
is everything it can reach — and the host instantiates the *same* loaded
functor twice: once with a live `fetch` backed by `Sys.readfile`, once with
a canned in-memory one. Environments are records, instantiation is
application: hermetic testing of a dynamically loaded component with no
mocking framework. The component cannot tell which world it is in.

```console
$ main --link sys loader host.sceo -o prog.sceo
$ printf 'live' > data.txt
$ main --run prog.sceo
- : String = "data(answer) = 42 / data(data.txt) = live"
$ rm data.txt
$ main --run prog.sceo
- : String = "data(answer) = 42 / data(data.txt) = <missing>"
```

#### `examples/harness/report.sce`

```ocaml
(* A component written against an interface, not a world: everything it can
   reach is in Env. Which world that is — live or canned — is its caller's
   decision, per instantiation. *)

import Env : { fetch : String -> String }

let run (k : String) : String = "data(" ^ k ^ ") = " ^ Env.fetch k
```

#### `examples/harness/host.sce`

```ocaml
(* One loaded artifact, two worlds: the same functor is instantiated against
   a live environment backed by Sys and a canned in-memory one. Environments
   are records, instantiation is application — mocking without a framework. *)

import Sys
import Loader : { load : String ->
  (({Env : {fetch : String -> String}} => {run : String -> String})
    | {err : String}) }

type loaded =
  | Report of (({Env : {fetch : String -> String}}) => {run : String -> String})
  | Failed of {err : String}
type file = | Contents of String | NoFile of {err : String}

let live (k : String) : String =
  match Sys.readfile k with
  | Contents s -> s
  | NoFile e -> "<missing>"
  end

let canned (k : String) : String = "42"

let main : String =
  match Loader.load "report.sceo" with
  | Report f ->
    let mock = f({ Env = { fetch = canned } }) in
    let prod = f({ Env = { fetch = live } }) in
    mock.run "answer" ^ " / " ^ prod.run "data.txt"
  | Failed e -> "<" ^ e.err ^ ">"
  end
```

---

## 5. Case study: lambda — an interpreter in five units

A lambda-calculus interpreter with real text parsing. ADTs everywhere
(tokens, terms, options, parse results), redeclared structurally across
units. **String introspection is a capability**: the core's only string
primitives are `^` and `=` — strings are write-only — so `Str.head` and
`Str.tail` arrive as host primitives through the link line, and the lexer is
the *only* unit that imports `Str`: the interfaces alone tell you which unit
can look inside a string. Failure is a value (parse errors flow back as
`Err`; the evaluator's fuel bound makes divergent terms answer instead of
hang). The suite also runs the whole interpreter under node, with `str`
compiled as its own wasm module.

```console
$ main --link str lexer.sceo parser.sceo eval.sceo pretty.sceo main.sceo -o prog.sceo
$ main --run prog.sceo
- : String = "\\f. \\x. f (f (f (f x)))  ;  a  ;  parse error: expected ')'"
```

(The first result is Church `2 + 2` normalizing to Church `4`; the second is
`(\x.\y. x) a b` reducing to `a`; the third is malformed input handled
in-language.)

#### `examples/lambda/lexer.sce`

```ocaml
(* Text to tokens through the Str capability: head and tail are the only
   string introspection the host grants; everything else is written here. *)

import Str

type tok  = | TLam | TDot | TLP | TRP | TId of String
type toks = | TNil | TCons of tok * toks

module Lex = struct
  let stop (c : String) : Bool =
    c = "" || c = " " || c = "\n" || c = "\\" || c = "." || c = "(" || c = ")"
  let rec ident (acc : String) (s : String) : { name : String; rest : String } =
    let c = Str.head s in
    if stop c then { name = acc; rest = s }
    else ident (acc ^ c) (Str.tail s)
  let rec go (s : String) : toks =
    let c = Str.head s in
    if c = "" then TNil
    else if c = " " then go (Str.tail s)
    else if c = "\n" then go (Str.tail s)
    else if c = "\\" then TCons (TLam, go (Str.tail s))
    else if c = "." then TCons (TDot, go (Str.tail s))
    else if c = "(" then TCons (TLP, go (Str.tail s))
    else if c = ")" then TCons (TRP, go (Str.tail s))
    else let r = ident "" s in TCons (TId r.name, go r.rest)
  let lex (s : String) : toks = go s
end
```

#### `examples/lambda/parser.sce`

```ocaml
(* Recursive descent over the token list. The token and term types are
   redeclared here — structural equality is the shared contract, so this unit
   imports nothing. *)

type tok  = | TLam | TDot | TLP | TRP | TId of String
type toks = | TNil | TCons of tok * toks
type term = | Var of String | Lam of String * term | App of term * term

(* one step of parsing: a term and what remains, or an error *)
type pres   = | POk of term * toks | PErr of String
type parsed = | Ok of term | Err of String

module Parse = struct
  let rec parse_term (ts : toks) : pres =
    let parse_atom (ts : toks) : pres =
      match ts with
      | TNil -> PErr "unexpected end of input"
      | TCons (t, rest) ->
        (match t with
         | TId x -> POk (Var x, rest)
         | TLam ->
           (match rest with
            | TCons (t2, r2) ->
              (match t2 with
               | TId x ->
                 (match r2 with
                  | TCons (t3, r3) ->
                    (match t3 with
                     | TDot ->
                       (match parse_term r3 with
                        | POk (b, r4) -> POk (Lam (x, b), r4)
                        | PErr m -> PErr m
                        end)
                     | _ -> PErr "expected '.' after the binder"
                     end)
                  | TNil -> PErr "expected '.' after the binder"
                  end)
               | _ -> PErr "expected a variable after '\\'"
               end)
            | TNil -> PErr "expected a variable after '\\'"
            end)
         | TLP ->
           (match parse_term rest with
            | POk (b, r2) ->
              (match r2 with
               | TCons (t2, r3) ->
                 (match t2 with
                  | TRP -> POk (b, r3)
                  | _ -> PErr "expected ')'"
                  end)
               | TNil -> PErr "expected ')'"
               end)
            | PErr m -> PErr m
            end)
         | TRP -> PErr "unexpected ')'"
         | TDot -> PErr "unexpected '.'"
         end)
      end
    in
    let starts (ts : toks) : Bool =
      match ts with
      | TNil -> false
      | TCons (t, r) ->
        (match t with
         | TId x -> true
         | TLam -> true
         | TLP -> true
         | _ -> false
         end)
      end
    in
    let rec more (acc : term) (ts : toks) : pres =
      if starts ts then
        match parse_atom ts with
        | POk (a, rest) -> more (App (acc, a)) rest
        | PErr m -> PErr m
        end
      else POk (acc, ts)
    in
    match parse_atom ts with
    | POk (a, rest) -> more a rest
    | PErr m -> PErr m
    end

  let parse (ts : toks) : parsed =
    match parse_term ts with
    | POk (t, rest) ->
      (match rest with
       | TNil -> Ok t
       | TCons (x, r) -> Err "trailing tokens after the term"
       end)
    | PErr m -> Err m
    end
end
```

#### `examples/lambda/eval.sce`

```ocaml
(* Normal-order reduction with capture-avoiding substitution and a fuel
   bound, so a diverging term answers instead of hanging. Imports nothing. *)

type term = | Var of String | Lam of String * term | App of term * term
type opt  = | ONone | OSome of term

module Eval = struct
  let rec free (x : String) (t : term) : Bool =
    match t with
    | Var y -> x = y
    | Lam (y, b) -> if x = y then false else free x b
    | App (f, a) -> free x f || free x a
    end
  let rec fresh (x : String) (v : term) (b : term) : String =
    if free x v || free x b then fresh (x ^ "'") v b else x
  let rec subst (x : String) (v : term) (t : term) : term =
    match t with
    | Var y -> if x = y then v else Var y
    | Lam (y, b) ->
      if x = y then Lam (y, b)
      else if free y v then
        let z = fresh (y ^ "'") v b in
        Lam (z, subst x v (subst y (Var z) b))
      else Lam (y, subst x v b)
    | App (f, a) -> App (subst x v f, subst x v a)
    end
  let rec step (t : term) : opt =
    match t with
    | Var x -> ONone
    | Lam (x, b) ->
      (match step b with
       | OSome b2 -> OSome (Lam (x, b2))
       | ONone -> ONone
       end)
    | App (f, a) ->
      (match f with
       | Lam (x, b) -> OSome (subst x a b)
       | _ ->
         (match step f with
          | OSome f2 -> OSome (App (f2, a))
          | ONone ->
            (match step a with
             | OSome a2 -> OSome (App (f, a2))
             | ONone -> ONone
             end)
          end)
       end)
    end
  let rec norm (fuel : Int) (t : term) : term =
    if fuel = 0 then t
    else
      match step t with
      | OSome t2 -> norm (fuel - 1) t2
      | ONone -> t
      end
end
```

#### `examples/lambda/pretty.sce`

```ocaml
(* Terms back to text, with minimal parentheses. Imports nothing. *)

type term = | Var of String | Lam of String * term | App of term * term

module Pretty = struct
  let rec print (t : term) : String =
    match t with
    | Var x -> x
    | Lam (x, b) -> "\\" ^ x ^ ". " ^ print b
    | App (f, a) ->
      let pf =
        (match f with
         | Lam (x, b) -> "(" ^ print f ^ ")"
         | _ -> print f
         end)
      in
      let pa =
        (match a with
         | Var x -> print a
         | _ -> "(" ^ print a ^ ")"
         end)
      in
      pf ^ " " ^ pa
    end
end
```

#### `examples/lambda/main.sce`

```ocaml
(* The driver: lex, parse, normalize, print. Parse failure is a value the
   program handles, and the fuel bound makes Omega answer instead of hang. *)

import Lex
import Parse
import Eval
import Pretty

type term   = | Var of String | Lam of String * term | App of term * term
type parsed = | Ok of term | Err of String

let run (src : String) : String =
  match Parse.parse (Lex.lex src) with
  | Ok t -> Pretty.print (Eval.norm 1000 t)
  | Err m -> "parse error: " ^ m
  end

let main : String =
  run "(\\m.\\n.\\f.\\x. m f (n f x)) (\\f.\\x. f (f x)) (\\f.\\x. f (f x))"
  ^ "  ;  " ^ run "(\\x.\\y. x) a b"
  ^ "  ;  " ^ run "\\x. (x"
```
