(** Compile core lambda-E expressions to WebAssembly-GC. Compilation does not
    evaluate expressions or invoke host capabilities. [Hostfn] values become
    closures calling imported [host] functions when the module runs.

    Input must be a well-typed source expression, with nonnegative projection
    indices and no runtime [Clos] or [Fclos] values. Detected inconsistencies
    raise [Error] or [Core_lambdae.Check.Type_error]. Generated code uses Wasm
    traps for runtime faults rather than the interpreter's exceptions. *)

exception Error of string
(** Unsupported source values or inconsistent source types. *)

val program :
  ?customs:(string * string) list -> Core_lambdae.Ast.exp -> Ir.modul
(** Compile with unit as the initial environment and export the result through
    [main]. [customs] defaults to [[]] and supplies custom section names and raw
    byte payloads, for example an [sce.slot] interface declaration. *)

val to_binary :
  ?customs:(string * string) list -> Core_lambdae.Ast.exp -> string
(** Compile with [program] and return the binary bytes. *)

val to_wat :
  ?customs:(string * string) list -> Core_lambdae.Ast.exp -> string
(** Compile with [program] and return the diagnostic text from [Wat.modul]. *)

val link_module :
  names:string list ->
  unit_types:Core_lambdae.Ast.typ list ->
  Core_lambdae.Ast.exp ->
  Ir.modul
(** Compile a composition body whose environment is the ordered merge of unit
    results, initially unit. [names] and [unit_types] must have matching lengths
    and order; this precondition is not checked here. Each invocation of [main]
    calls imported [u0.main], [u1.main], and so on once, in order, before the
    body. The last unit is at projection zero. An [sce.units] custom section
    records the expected unit names for the host. *)

val link_binary :
  names:string list ->
  unit_types:Core_lambdae.Ast.typ list ->
  Core_lambdae.Ast.exp ->
  string
(** Binary encoding of [link_module]. *)

val link_wat :
  names:string list ->
  unit_types:Core_lambdae.Ast.typ list ->
  Core_lambdae.Ast.exp ->
  string
(** Diagnostic text for [link_module], with the limitations of [Wat.modul]. *)
