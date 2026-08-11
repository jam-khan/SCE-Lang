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
