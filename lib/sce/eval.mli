(** Direct interpreters for resolved source-core terms. Supply a value
    environment, normally [Ast.Unit] for a whole program. Evaluation performs
    no type check and may diverge. Failed runtime operations, including
    missing fields, invalid import packages, and division by zero, raise
    [Failure]. *)

(** Big-step evaluation. Applications, merges, links, and primitive operands
    evaluate from left to right. Non-dependent merges preserve the ambient
    environment for both operands; sandboxed functors capture [Ast.Unit]. *)
val eval : Ast.nameless -> Ast.nameless -> Ast.nameless

(** One small step under the supplied environment; values are unchanged. *)
val step : Ast.nameless -> Ast.nameless -> Ast.nameless

(** Repeated small-step evaluation until the value predicate holds. *)
val eval' : Ast.nameless -> Ast.nameless -> Ast.nameless
