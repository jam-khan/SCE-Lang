(* Differential tests for the wasm backend.

   For every program: compile it to wasm, run it under node, and require the
   rendered result to equal what the OCaml interpreter produces. The two agree
   on formatting by construction — wasm/run.js reproduces lib/core/pretty.ml —
   so a mismatch is a real difference in behaviour, not in presentation. *)

let failures = ref 0
let skipped = ref false

let check name condition =
  if condition then Printf.printf "PASS  %s\n" name
  else (
    Printf.printf "FAIL  %s\n" name;
    incr failures)

let run_js = "../wasm/run.js"
let examples_dir = "../examples"

let have cmd = Sys.command (Printf.sprintf "%s >/dev/null 2>&1" cmd) = 0

(* Closures print with their type in pretty.ml and without one in wasm, where
   types are erased. Collapse both to `<fun>` so everything else still gets
   compared exactly. *)
let normalise s =
  let b = Buffer.create (String.length s) in
  let n = String.length s in
  let i = ref 0 in
  while !i < n do
    if s.[!i] = '<' then begin
      (* The closing angle bracket is the first `>` that is not the tail of an
         arrow, since the printed type inside may contain `->`. *)
      let j = ref !i in
      while !j < n && not (s.[!j] = '>' && (!j = 0 || s.[!j - 1] <> '-')) do incr j done;
      let j = if !j < n then !j else n - 1 in
      let seg = String.sub s !i (j - !i + 1) in
      let starts p = String.length seg >= String.length p
                     && String.sub seg 0 (String.length p) = p in
      Buffer.add_string b (if starts "<fun" || starts "<rec fun" then "<fun>" else seg);
      i := j + 1
    end
    else begin
      Buffer.add_char b s.[!i];
      incr i
    end
  done;
  Buffer.contents b

type outcome = Value of string | Failed of string

let interpret src =
  match Sce.Pipeline.run src with
  | Ok o -> Value (normalise (Sce.Pipeline.value_string o))
  | Error e -> Failed e.stage

let read_file path =
  let ic = open_in_bin path in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  s

let compile_and_run src =
  match Sce.Pipeline.run_to_core src with
  | Error e -> Failed e.stage
  | Ok core -> (
    match Wasm_backend.Compile.to_binary core with
    | exception Wasm_backend.Compile.Error _ -> Failed "compile"
    | bin ->
      let wasm = Filename.temp_file "sce" ".wasm" in
      let out = Filename.temp_file "sce" ".out" in
      let oc = open_out_bin wasm in
      output_string oc bin;
      close_out oc;
      let status =
        Sys.command (Printf.sprintf "node %s %s > %s 2>&1" run_js wasm out)
      in
      let text = String.trim (read_file out) in
      Sys.remove wasm;
      Sys.remove out;
      if status = 0 then Value (normalise text) else Failed "runtime")

(* Both sides must agree on the value, or both must fail. Failure *stages*
   differ by design — the interpreter says "runtime", wasm reports a trap — so
   only the fact of failure is compared. *)
let agree name src =
  match (interpret src, compile_and_run src) with
  | Value a, Value b ->
    if a = b then check name true
    else (
      check name false;
      Printf.printf "        interpreter %s\n        wasm        %s\n" a b)
  | Failed _, Failed _ -> check name true
  | a, b ->
    check name false;
    let show = function Value v -> "= " ^ v | Failed s -> "failed in " ^ s in
    Printf.printf "        interpreter %s\n        wasm        %s\n" (show a) (show b)

let programs =
  [
    (* literals and primitives *)
    ("unit", ";; ()");
    ("integer", ";; 42");
    ("arithmetic", ";; 1 + 2 * 3 - 4");
    ("precedence", ";; (1 + 2) * (10 - 4) / 2");
    ("division", ";; 7 / 2");
    ("modulo", ";; 17 mod 5");
    ("negation", ";; 0 - 5");
    ("boolean", ";; true");
    ("comparison", ";; 3 <= 3");
    ("short-circuit", ";; true && not false || false");
    ("integer equality", ";; 2 = 2");
    ("conditional", ";; if 1 < 2 then 10 else 20");
    ("nested conditional", ";; if false then 1 else if true then 2 else 3");
    (* strings *)
    ("string literal", {|;; "hello"|});
    ("concatenation", {|;; "ab" ^ "cd" ^ "ef"|});
    ("string equality", {|;; "abc" = "abc"|});
    ("string inequality", {|;; "abc" <> "abd"|});
    ("string escapes", {|;; "a\nb\"c\\d"|});
    ("empty string", {|;; "" ^ "x"|});
    (* records and merges *)
    ("empty record", ";; {}");
    ("record", ";; { a = 1; b = 2 }");
    ("projection", ";; { a = 1; b = 2 }.b");
    ("nested record", ";; { a = { b = 1 } }.a.b");
    ("non-dependent merge", ";; { a = 1 } ,, { b = 2 }");
    ("dependent merge", ";; { a = 1 } ,,, { b = a + 1 }");
    ("context index", ";; { a = 1 } ,,, ?.[0]");
    (* functions *)
    ("let", ";; let x = 1 in x + 1");
    ("nested let", ";; let a = 1 in let b = 2 in let c = 3 in a + b * c");
    ("lambda", ";; (fun (x : Int) -> x * 2) 21");
    ("closure capture", ";; let a = 10 in (fun (x : Int) -> x + a) 5");
    ("curried", "let f (x : Int) (y : Int) : Int = x + y ;; f 3 4");
    ("returns a function",
     ";; let mk (a : Int) : Int -> Int = fun (b : Int) -> a + b in (mk 3) 4");
    ("higher order",
     "let twice (f : Int -> Int) (x : Int) : Int = f (f x)\n\
      ;; twice (fun (n : Int) -> n * 3) 2");
    ("function value", ";; fun (x : Int) -> x");
    (* recursion *)
    ("factorial",
     ";; let rec fact (n : Int) : Int = if n <= 1 then 1 else n * fact (n - 1) \
      in fact 5");
    ("fibonacci",
     ";; let rec fib (n : Int) : Int = if n < 2 then n else fib (n - 1) + fib \
      (n - 2) in fib 20");
    ("recursion with two parameters",
     ";; let rec add (x : Int) (y : Int) : Int = if x = 0 then y else add (x - \
      1) (y + 1) in add 5 7");
    (* unions *)
    ("injection", {|;; (inl 1 : Int | String)|});
    ("case on inl",
     {|;; case (inl 7 : Int | String) of inl n -> n * 2 | inr s -> 0 end|});
    ("case on inr",
     {|;; case (inr "hi" : Int | String) of inl n -> "num" | inr s -> s end|});
    (* iso-recursive types *)
    ("fold", "type N = mu a. Top | a\n;; (fold (inl () : Top | N) : mu a. Top | a)");
    ("unfold",
     "type N = mu a. Top | a\n\
      let z : N = (fold (inl () : Top | N) : mu a. Top | a)\n\
      ;; case unfold z of inl u -> \"zero\" | inr m -> \"succ\" end");
    (* modules *)
    ("structure", "module M = struct let a : Int = 2 let b : Int = a * 3 end ;; M.b");
    ("sandboxed structure",
     "module M = sandbox struct let k : Int = 42 end ;; M.k");
    ("functor",
     "module F (X : { a : Int }) = struct let b : Int = X.a + 1 end\n\
      module A = F({ a = 1 })\n\
      ;; A.b");
    ("link",
     "module C = struct let start : Int = 1 end\n\
      module L = link C with functor (X : { start : Int }) -> struct let next : \
      Int = X.start + 1 end\n\
      ;; L.next");
    ("linkall",
     "module P = struct let w : Int = 3 let h : Int = 4 end\n\
      module A = linkall P with functor (X : { w : Int } & { h : Int }) -> \
      struct let area : Int = X.w * X.h end\n\
      ;; A.area");
    ("open", ";; open { a = 1; b = 2 } in a + b");
    ("program without a main", "let a : Int = 1\nlet b : Int = 2");
    (* allocation pressure: fib 24 is ~150k calls, all heap-allocating *)
    ("allocation pressure",
     ";; let rec fib (n : Int) : Int = if n < 2 then n else fib (n - 1) + fib \
      (n - 2) in fib 24");
    ("string allocation",
     ";; let rec rep (n : Int) (s : String) : String = if n = 0 then s else rep \
      (n - 1) (s ^ \"xyz\") in rep 200 \"\"");
    (* traps: both sides must fail *)
    ("division by zero", ";; 1 / 0");
    ("modulo by zero", ";; 1 mod 0");
  ]

let test_examples () =
  print_endline "-- examples --";
  let files = Sys.readdir examples_dir in
  Array.sort compare files;
  Array.iter
    (fun f ->
      if Filename.check_suffix f ".sce" then
        agree ("example: " ^ f) (read_file (Filename.concat examples_dir f)))
    files

(* Binaryen is an independent check that a module our own emitter is happy with
   is genuinely well-formed. Skipped when it is not installed. *)
let test_validity () =
  if not (have "wasm-opt --version") then
    print_endline "-- validation -- skipped (wasm-opt not found)"
  else begin
    print_endline "-- validation --";
    List.iter
      (fun (name, src) ->
        match Sce.Pipeline.run_to_core src with
        | Error _ -> ()
        | Ok core ->
          let wasm = Filename.temp_file "sce" ".wasm" in
          let oc = open_out_bin wasm in
          output_string oc (Wasm_backend.Compile.to_binary core);
          close_out oc;
          let ok =
            Sys.command
              (Printf.sprintf
                 "wasm-opt --enable-gc --enable-reference-types --enable-bulk-memory %s -o /dev/null 2>/dev/null"
                 wasm)
            = 0
          in
          Sys.remove wasm;
          check ("binaryen validates: " ^ name) ok)
      programs
  end

let () =
  if not (have "node --version") then begin
    print_endline "wasm tests skipped: node is not installed (brew install node)";
    skipped := true
  end;
  if not !skipped then begin
    print_endline "-- compiled vs interpreted --";
    List.iter (fun (name, src) -> agree name src) programs;
    print_newline ();
    test_examples ();
    print_newline ();
    test_validity ();
    print_newline ();
    if !failures = 0 then print_endline "all wasm tests passed"
    else (
      Printf.printf "%d wasm test(s) failed\n" !failures;
      exit 1)
  end
