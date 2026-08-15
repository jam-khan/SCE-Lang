(* The λSCE context discipline, in one place. *)

module type SLOT = sig
  type t
end

module Make (S : SLOT) = struct
  type env = S.t list

  let empty : env = []
  let push (s : S.t) (env : env) : env = s :: env
  let nth (env : env) (i : int) : S.t option = List.nth_opt env i

  (* One entry per λSCE form that extends the context. The comment on each
     names the elaboration rule in lib/sce/elab.ml it mirrors. *)

  (* Lam (A, body): body under ctx & A *)
  let lam a env = push a env

  (* Letb (e1, A, e2): e2 under ctx & A *)
  let letb a env = push a env

  (* Flam (A, B, body): body under (ctx & (A -> B)) & A, so the argument is
     index 0 and the function itself is index 1. *)
  let flam ~self ~arg env = push arg (push self env)

  (* Mrg (e1, e2): e2 under ctx & typeof e1 *)
  let mrg a env = push a env

  (* Nmrg (e1, e2): e2 under ctx, unchanged *)
  let nmrg (_ : S.t) (env : env) : env = env

  (* Case (_, el, er): each branch under ctx & A resp. ctx & B *)
  let case_branch a env = push a env

  (* Openm (e1, e2): e1 : {l : A}, e2 under ctx & A *)
  let openm a env = push a env

  (* Mstruct (Sandboxed, body) and Mfunctor (Sandboxed, A, body): the outer
     context is gone. A sandboxed functor then pushes its parameter with `lam`
     as usual, giving Top & A. *)
  let sandbox (_ : env) : env = empty

  (* Box (e1, e2): e2 under typeof e1, replacing the context wholesale. Its
     component structure is not knowable from syntax, so named bindings do not
     cross a box — inside one, reach the context with `?` and `?.n`. *)
  let box (_ : env) : env = empty
end