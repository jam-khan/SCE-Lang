(* The λSCE context discipline, in one place: Sugar fills the slots with types,
   Debruijn counts them to turn a name into an index, and if they disagree the
   indices silently point at the wrong slot.

   Head of the list is index 0 — the innermost binding, and the right-most
   component of the intersection, as `Elab.slookup` and `Eval.lookup` read it. *)

module type SLOT = sig
  type t
end

module Make (S : SLOT) = struct
  type env = S.t list

  let empty : env = []
  let push (s : S.t) (env : env) : env = s :: env
  let nth (env : env) (i : int) : S.t option = List.nth_opt env i

  (* One entry per λSCE form that extends the context, named for its Elab rule. *)

  let lam a env = push a env    (* Lam (x, A, body): body under ctx & A *)
  let letb a env = push a env   (* Letb (x, e1, A, e2): e2 under ctx & A *)
  let mrg a env = push a env    (* Mrg (x, e1, e2): e2 under ctx & typeof e1 *)
  let openm a env = push a env  (* Openm (x, {l : A}, e2): e2 under ctx & A *)
  let case_branch a env = push a env  (* Case: each branch under ctx & A resp. B *)

  (* Nmrg (e1, e2): e2 under ctx, unchanged *)
  let nmrg (_ : S.t) (env : env) : env = env

  (* Flam: body under (ctx & (A -> B)) & A — argument 0, function itself 1. *)
  let flam ~self ~arg env = push arg (push self env)

  (* Mstruct/Mfunctor (Sandboxed, ...): the outer context is gone. A sandboxed
     functor then pushes its parameter with `lam`, giving Top & A. *)
  let sandbox (_ : env) : env = empty

  (* Box (e1, e2): e2 under typeof e1, wholesale. Its component structure is not
     knowable from syntax, so names do not cross a box — use `?` and `?.n`. *)
  let box (_ : env) : env = empty
end
