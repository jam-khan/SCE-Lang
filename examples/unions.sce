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
