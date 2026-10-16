(** Core interpreters. Supply a value environment; [Ast.Unit] is the empty
    whole-program environment. Application, merge operands, and primitive
    operands evaluate from left to right. Evaluation performs no type check
    and may diverge. Failed runtime operations, including division by zero,
    raise [Failure]; exceptions from host callbacks propagate unchanged. *)

(** Process-wide resolver for host capabilities, initially returning [None].
    Applying [Hostfn (name, _, _)] resolves [name] at application time and
    calls its callback with the evaluated argument. The callback must return
    a value of the declared result type; neither property is checked here.
    Missing capabilities raise [Failure]. Callbacks may perform host effects. *)
val host_dispatch : (string -> (Ast.exp -> Ast.exp) option) ref

(** Big-step evaluation under the supplied environment. *)
val eval : Ast.exp -> Ast.exp -> Ast.exp

(** One small step; values are returned unchanged. A step may invoke a host
    callback when reducing a capability application. *)
val step : Ast.exp -> Ast.exp -> Ast.exp

(** Repeated small-step evaluation until the value predicate holds. *)
val eval' : Ast.exp -> Ast.exp -> Ast.exp
