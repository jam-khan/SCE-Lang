(* Located errors, shared by the source passes; Pipeline renders them. *)

open Ast

exception Error of string * loc

let err loc fmt = Printf.ksprintf (fun s -> raise (Error (s, loc))) fmt

(* Elab's judgement helpers raise their own exception. *)
let lift loc f =
  try f () with Sce_core.Elab.Elab_error m -> raise (Error (m, loc))

(* A duplicate label makes *both* copies unreachable: srlookup refuses it. *)
let rec check_unique what = function
  | [] -> ()
  | (l, loc) :: rest ->
    if List.mem_assoc l rest then
      err loc "duplicate label '%s' in this %s" l what
    else check_unique what rest
