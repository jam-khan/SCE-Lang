open Js_of_ocaml

(* Exported to JS as `sce.run`. Every field is always present so the two
   branches build the same object type: on success `typ`/`value`/`core` are
   set, on failure `error` carries the rendered (caret-pointed) message. *)
let () =
  Js.export "sce"
    (object%js
       method run (input : Js.js_string Js.t) =
         let src = Js.to_string input in
         let mk ok typ value core error =
           object%js
             val ok = ok
             val typ = Js.string typ
             val value = Js.string value
             val core = Js.string core
             val error = Js.string error
           end
         in
         match Sce.Pipeline.run src with
         | Ok o ->
           mk Js._true
             (Sce.Pipeline.type_string o)
             (Sce.Pipeline.value_string o)
             (Sce.Pipeline.core_string o)
             ""
         | Error e -> mk Js._false "" "" "" (Sce.Pipeline.render ~src e)
    end)
