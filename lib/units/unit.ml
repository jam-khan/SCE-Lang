(* A unit is a *sandboxed functor* from its imports to its exports, closed by
   the calculus (`sandbox` elaborates under Top) rather than by toolchain
   discipline. This is where a source file becomes one. *)

module S = Sce_core.Ast

open Artifact

(* One import header as a self-contained named type, spliced into the unit
   file before desugaring. File interfaces live next to the importing source. *)
let import_typ ~dir (b : Ast.binder) (src : Ast.import_source) : Ast.typ =
  let from_file base =
    let path = Filename.concat dir (base ^ ".scei") in
    let content =
      try
        let ic = open_in_bin path in
        let s = really_input_string ic (in_channel_length ic) in
        close_in ic;
        s
      with Sys_error _ ->
        (* `import Sys`/`import Str` fall back to the built-in host
           interfaces, unless a .scei file shadows them. *)
        if base = "Sys" then print_typ Host.sys_typ
        else if base = "Str" then print_typ Host.str_typ
        else err "import %s: interface file %s not found" b.bd_name path
    in
    match Driver.parse_intf content with
    | Error e -> err "%s:%d:%d: %s" path e.line e.col e.message
    | Ok intf -> expand_aliases intf
  in
  match src with
  | Ast.IAuto -> from_file b.bd_name
  | Ast.IFile base -> from_file base
  | Ast.IInline t -> t

let imports_binder = "%imports"

(* The whole design in one function: a unit is its declarations as a sandboxed
   struct, or — when it imports — a sandboxed functor over the record of
   imports, opened. Everything downstream is the whole-program machinery. *)
let wrapper (imports : (Ast.binder * Ast.typ) list) (p : Ast.program) :
    Ast.program =
  let loc = Ast.dummy_loc in
  let node it : Ast.exp = { it; loc } in
  let wrapped =
    match imports with
    | [] -> node (Ast.EStruct (Ast.Sandboxed, p.decls))
    | (b0, _) :: _ ->
      let fields = List.map (fun (b, t) -> (b.Ast.bd_name, t)) imports in
      (* the parameter's record type is where a duplicate import is caught, so
         it carries the first import's location rather than a dummy *)
      let param =
        {
          Ast.p_bind = { Ast.bd_name = imports_binder; bd_loc = b0.Ast.bd_loc };
          p_typ = { Ast.it = Ast.TRcd fields; loc = b0.Ast.bd_loc };
        }
      in
      node
        (Ast.EFunctor
           ( Ast.Sandboxed,
             [ param ],
             node
               (Ast.EOpen
                  ( node (Ast.EVar imports_binder),
                    node (Ast.EStruct (Ast.Open, p.decls)) )) ))
  in
  { Ast.imports = []; decls = []; main = Some wrapped }

(* Split the synthesized unit type into interface halves. *)
let info (t : S.typ) : S.typ option * S.typ =
  match t with
  | S.TSig (S.TyArrM (i, S.TyIntf e)) -> (Some i, e)
  | t -> (None, t)
