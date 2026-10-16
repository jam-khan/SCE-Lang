(** Link compiled units by constructing ordinary core terms. *)

val import_fields : Sce_core.Ast.typ -> (string * Sce_core.Ast.typ) list
(** Collect record fields through intersections and signatures, ignoring
    other components.
    @raise Units.Artifact.Error if no fields are found. *)

val link : Artifact.t list -> Artifact.t
(** Combine units from left to right, supplying each unit's imports from
    accumulated exports. The first unit must have no imports, export labels
    must not overlap, and each import must match uniquely at its declared type.
    The resulting core term is typechecked but not evaluated.
    @raise Units.Artifact.Error if these checks fail or the list is empty. *)

val wasm_parts :
  Artifact.t list -> string list * Core_lambdae.Ast.typ list * Core_lambdae.Ast.exp
(** Construct the same composition using environment projections for units.
    Return unit names, their core slot types, and the link body; all lists
    follow input order. The environment must be [Unit] extended on the right
    by the unit values in that order. Selects a unique [main] export when
    present; otherwise returns the whole composition.
    Performs the interface checks of {!link}, without typechecking the body.
    @raise Units.Artifact.Error if interface checks fail or the list is empty. *)

val runnable : Artifact.t -> Sce_core.Ast.typ * Core_lambdae.Ast.exp
(** Select a unique [main] export, or return the entire artifact's exports.
    Returns its source type and core term without evaluating either.
    @raise Units.Artifact.Error if the artifact still has imports. *)
