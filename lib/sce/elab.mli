(** Type-directed elaboration from resolved source-core terms to the
    explicit-environment core. Type comparisons are syntactic. *)

exception Elab_error of string

(** Unroll a mu body by substituting its complete recursive type. That type
    must be closed, since substitution does not shift free variables. *)
val unfold_mu : Ast.typ -> Ast.typ

(** Positional lookup along the left spine of intersections, starting with
    the right component at index zero and excluding the terminal base.
    @raise Elab_error if the index has no component, including negative indices. *)
val slookup : Ast.typ -> int -> Ast.typ

(** Test label presence through intersections and signatures, without
    requiring uniqueness. *)
val label_in : string -> Ast.typ -> bool

(** Find a uniquely occurring label through intersections and signatures.
    Return [None] for either absence or ambiguity. *)
val srlookup_opt : Ast.typ -> string -> Ast.typ option

(** Collect record fields in left-to-right order through intersections and
    signatures. Other type forms contribute no fields; duplicates are kept. *)
val record_fields : Ast.typ -> (string * Ast.typ) list

(** The exception-raising form of [srlookup_opt].
    @raise Elab_error for absent or ambiguous labels. *)
val srlookup : Ast.typ -> string -> Ast.typ

(** Erase signatures and translate module arrows to ordinary core arrows. *)
val elab_typ : Ast.typ -> Core_lambdae.Ast.typ

(** Result type of a primitive operation.
    @raise Elab_error for incompatible operand types. *)
val typ_of_binop : Ast.binop -> Ast.typ -> Ast.typ -> Ast.typ

(** Build a non-dependent merge. Each operand is evaluated once, left to
    right, under the original ambient environment, including any host effects. *)
val nmrg_core : Core_lambdae.Ast.exp -> Core_lambdae.Ast.exp -> Core_lambdae.Ast.exp

(** [linked_core provider_type imports result_type provider target] builds
    a merge of the provider and the target's result. The target must have
    type [imports -> result_type]; [imports] must be a record or a left-nested
    intersection of records, all supplied unambiguously by the provider.
    These preconditions are not checked by this term constructor. Provider
    and target are evaluated once each, in that order, before application. *)
val linked_core :
  Core_lambdae.Ast.typ -> Core_lambdae.Ast.typ -> Core_lambdae.Ast.typ ->
  Core_lambdae.Ast.exp -> Core_lambdae.Ast.exp -> Core_lambdae.Ast.exp

(** [elab ctx e] returns the source-core type and elaborated term, with
    [Query] assigned [ctx]. Context extension appends an intersection
    component on the right. Types must be well-scoped, treating [Fold]'s
    annotation as a mu body; scope is not checked separately.
    @raise Elab_error for invalid typing rules, absent or ambiguous fields,
    unsatisfied imports, or non-value closure environments. *)
val elab : Ast.typ -> Ast.nameless -> Ast.typ * Core_lambdae.Ast.exp

(** Type-check a whole program under [Ast.TTop], discarding its elaboration. *)
val check : Ast.nameless -> Ast.typ

(** Elaborate a whole program under [Ast.TTop], discarding its source type. *)
val compile : Ast.nameless -> Core_lambdae.Ast.exp
