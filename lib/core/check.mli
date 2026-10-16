(** Structural type checking for the explicit-environment core calculus.
    Type equality is syntactic; no subtyping or recursive-type equivalence
    is performed. *)

exception Type_error of string

(** [unfold_mu body] substitutes [Ast.TMu body] for the variable bound by
    that mu. The complete recursive type must be closed: substitution does
    not shift free type variables. *)
val unfold_mu : Ast.typ -> Ast.typ

(** Positional lookup along the left spine of intersections, starting with
    the right component at index zero. The terminal base is not a component.
    @raise Type_error if the index has no component, including negative indices. *)
val tlookup : Ast.typ -> int -> Ast.typ

(** Whether a label occurs in a record or either side of an intersection.
    This tests presence, not uniqueness. *)
val lin : string -> Ast.typ -> bool

(** Result type of a primitive operation.
    @raise Type_error for incompatible operand types. *)
val type_of_binop : Ast.binop -> Ast.typ -> Ast.typ -> Ast.typ

(** [infer ctx e] checks [e] with [Query] assigned [ctx]. Context extension
    appends an intersection component on the right. Types must be well-scoped,
    treating [Fold]'s annotation as a mu body; scope is not checked separately.
    @raise Type_error for an invalid typing rule, absent or ambiguous field,
    or non-value closure environment. *)
val infer : Ast.typ -> Ast.exp -> Ast.typ

(** [typecheck e] is [infer Ast.TTop e], the whole-program entry point. *)
val typecheck : Ast.exp -> Ast.typ
