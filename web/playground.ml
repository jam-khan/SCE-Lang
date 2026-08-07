open Js_of_ocaml

(* Exported to JS as `sce.run`. Every field is always present so the two
   branches build the same object type: on success `ast`/`value` are set,
   on failure `error` carries the rendered (caret-pointed) message. *)
let () =
  Js.export "sce"
    (object%js
       method run (input : Js.js_string Js.t) =
         let src = Js.to_string input in
         let mk ok ast value error =
           object%js
             val ok = ok
             val ast = Js.string ast
             val value = Js.string value
             val error = Js.string error
           end
         in
         match Sce.Driver.parse src with
         | Ok tree -> (
             match Sce.Interp.eval tree with
             | v ->
                 mk Js._true (Sce.Ast.string_of_expr tree) (string_of_int v) ""
             | exception Division_by_zero ->
                 mk Js._false
                   (Sce.Ast.string_of_expr tree)
                   "" "runtime error: division by zero")
         | Error err -> mk Js._false "" "" (Sce.Driver.render ~src err)
    end)
