(* Http_simple's URI codec (mllib), which the browser shell uses on every
   request.  On 3,000 pseudo-random strings of all 256 bytes, decode_hex
   (encode_hex s) = s.  On 3,000 strings over "ab+%0F9zG ", decode_hex is
   compared with the usual form decoding ('+' is a space, %XY with two hex
   digits is that byte, anything else is itself), and the differences are
   classified.  Recorded as found: decode_hex raises Failure "unhexify" on
   a '%' followed by a non-hex digit, where the usual decoding passes it
   through; the .mli says nothing about malformed input.  The generator is
   a fixed linear congruential sequence, not Random. *)
let state = ref 99
let next () = state := (!state * 1103515245 + 12345) land 0x7fffffff; !state lsr 8
let pick n = next () mod n
let is_hex c = match c with '0'..'9' | 'a'..'f' | 'A'..'F' -> true | _ -> false
let model s =
  let b = Buffer.create 16 and n = String.length s in
  let rec go j =
    if j < n then
      match s.[j] with
      | '+' -> Buffer.add_char b ' '; go (j + 1)
      | '%' when j + 2 <= n - 1 && is_hex s.[j + 1] && is_hex s.[j + 2] ->
          Buffer.add_char b (Char.chr (int_of_string ("0x" ^ String.sub s (j + 1) 2))); go (j + 3)
      | c -> Buffer.add_char b c; go (j + 1)
  in
  go 0; Buffer.contents b

let () =
  let n = 3000 in
  let rt = ref 0 and agree = ref 0 and raised = ref 0 and other = ref 0 in
  let first_rt = ref None and first_raise = ref None and first_other = ref None in
  for _ = 1 to n do
    let s = String.init (pick 12) (fun _ -> Char.chr (pick 256)) in
    let r = try Http_simple.decode_hex (Http_simple.encode_hex s) with e -> "(raises " ^ Printexc.to_string e ^ ")" in
    if r = s then incr rt else if !first_rt = None then first_rt := Some (String.escaped s ^ " -> " ^ String.escaped r);
    let alphabet = "ab+%0F9zG " in
    let u = String.init (pick 10) (fun _ -> alphabet.[pick (String.length alphabet)]) in
    match Http_simple.decode_hex u with
    | d when d = model u -> incr agree
    | d -> incr other; if !first_other = None then first_other := Some (u ^ " -> " ^ String.escaped d)
    | exception e -> incr raised; if !first_raise = None then first_raise := Some (u ^ " raises " ^ Printexc.to_string e)
  done;
  Printf.printf "decode_hex (encode_hex s) = s     %d of %d\n" !rt n;
  Option.iter (Printf.printf "  first difference: %s\n") !first_rt;
  Printf.printf "decode_hex = the usual decoding   %d of %d\n" !agree n;
  Printf.printf "  raises (a %% then a non-hex digit) %d" !raised;
  Option.iter (Printf.printf ", first: %s") !first_raise;
  Printf.printf "\n  other differences                %d\n" !other;
  Option.iter (Printf.printf "  first other: %s\n") !first_other
