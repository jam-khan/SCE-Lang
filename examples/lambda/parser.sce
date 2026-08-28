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
