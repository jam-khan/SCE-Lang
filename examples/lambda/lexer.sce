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
