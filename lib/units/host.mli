(** Built-in capability units. Initializing this module installs the core
    evaluator's dispatcher for printing, file reads, strings, and loading. *)

val sys_typ : Sce_core.Ast.typ
(** Interface of [Sys]: [print] and [readfile]. *)

val str_typ : Sce_core.Ast.typ
(** Interface of [Str]: [head] and [tail], operating on bytes. *)

val sys : Artifact.t
(** Import-free unit exporting the [Sys] capability record. *)

val str : Artifact.t
(** Import-free unit exporting the [Str] capability record. *)

val out : (string -> unit) ref
(** Output sink for [Sys.print], initially [print_string]. Each call receives
    the supplied string followed by a newline. *)

val loader : Artifact.t list -> Artifact.t
(** Construct a loader from the first [Loader] import in the supplied units.
    Its interface must be exactly [{load : String -> (T | {err : String})}]. Loading
    accepts an artifact only when its slot type equals [T], then evaluates it.
    Recognized artifact errors become the [err] alternative; malformed
    serialized data and evaluation failures may still raise exceptions.
    @raise Units.Artifact.Error if no loader interface is found or its shape differs. *)

val is_host_unit : string -> bool
(** Recognize the CLI unit names [sys], [str], and [loader]. *)
