(* Binary encoding primitives: LEB128, vectors, and section framing.

   A section's payload has to be prefixed with its byte length, so payloads are
   built into a scratch buffer and then spliced in. *)

let u32 buf n =
  let n = ref n in
  let continue_ = ref true in
  while !continue_ do
    let byte = !n land 0x7f in
    n := !n lsr 7;
    if !n = 0 then (
      Buffer.add_char buf (Char.chr byte);
      continue_ := false)
    else Buffer.add_char buf (Char.chr (byte lor 0x80))
  done

(* Signed LEB128: sign-extend rather than zero-fill, and stop only once the
   remaining bits agree with the sign bit of the byte just written. *)
let s32 buf n =
  let n = ref n in
  let continue_ = ref true in
  while !continue_ do
    let byte = !n land 0x7f in
    n := !n asr 7;
    let sign_bit_set = byte land 0x40 <> 0 in
    if (!n = 0 && not sign_bit_set) || (!n = -1 && sign_bit_set) then (
      Buffer.add_char buf (Char.chr byte);
      continue_ := false)
    else Buffer.add_char buf (Char.chr (byte lor 0x80))
  done

let byte buf b = Buffer.add_char buf (Char.chr (b land 0xff))

let vec buf f xs =
  u32 buf (List.length xs);
  List.iter (fun x -> f buf x) xs

let name buf s =
  u32 buf (String.length s);
  Buffer.add_string buf s

(* Build a payload, then emit `id`, its length, and the payload itself. An
   empty payload is omitted entirely, which is what the spec expects for
   sections with no entries. *)
let section buf id f =
  let payload = Buffer.create 256 in
  f payload;
  if Buffer.length payload > 0 then begin
    byte buf id;
    u32 buf (Buffer.length payload);
    Buffer.add_buffer buf payload
  end

let magic = "\x00\x61\x73\x6d"
let version = "\x01\x00\x00\x00"
