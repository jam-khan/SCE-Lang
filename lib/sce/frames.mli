(** Shared context-extension rules for name resolution and desugaring. *)

module type SLOT = sig
  type t
end

module Make (S : SLOT) : sig
  (** Slots are ordered innermost first, so the list head has index zero. *)
  type env = S.t list

  val empty : env

  (** [nth env i] returns [None] beyond the end and raises [Invalid_argument]
      if [i] is negative. *)
  val nth : env -> int -> S.t option

  (** Each of these binding forms adds one slot at index zero. *)
  val lam : S.t -> env -> env
  val letb : S.t -> env -> env
  val mrg : S.t -> env -> env
  val openm : S.t -> env -> env
  val case_branch : S.t -> env -> env

  (** A non-dependent merge preserves its ambient context; the slot argument
      is ignored. *)
  val nmrg : S.t -> env -> env

  (** The argument becomes index zero and the recursive function index one. *)
  val flam : self:S.t -> arg:S.t -> env -> env

  (** Discard outer slots before adding a sandboxed functor's parameter. *)
  val sandbox : env -> env

  (** Discard names on entry to a box. Its replacement environment's shape
      is not available to name resolution; access it through explicit queries. *)
  val box : env -> env
end
