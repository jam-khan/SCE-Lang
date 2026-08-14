(* The two merges.

   `;` is non-dependent: both sides are checked in the same context.
   `;;` is dependent: the right side additionally sees the left one, which is
   how a struct lets a later declaration use an earlier one. *)

let plain = { a = 1 } ; { b = 2 }

let dependent = { a = 1 } ;; { b = a + 1 }

(* `linkall` satisfies every labelled import at once. *)
module Parts = struct
  let width : Int = 3
  let height : Int = 4
end

module Area =
  linkall Parts with functor (X : { width : Int } & { height : Int }) -> struct
    let area : Int = X.width * X.height
  end

let main = { p = plain.b, d = dependent.b, area = Area.area }
