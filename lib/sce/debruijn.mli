(** Resolve term names using the binding rules shared with desugaring. *)

exception Error of string

(** Resolve a whole term from an empty name context, replacing each [Var]
    with a projection of [Query]. The nearest binder has index zero;
    recursive function bodies bind the argument before the recursive name.
    Names cannot cross a box or a sandbox boundary. Explicit projections
    are preserved without checking their bounds or types.
    @raise Error for unresolved names or explicit closure constructors. *)
val resolve : Ast.named -> Ast.nameless
