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
