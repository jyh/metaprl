(* Http_simple's two request parsers (mllib), which the browser shell runs on
   every request and every form post; test_http_simple covers only the hex
   codec under them.
   - decode_uri: fixed paths, printed as the code answers today. Recorded as
     found, not judged here: the URI is hex-decoded BEFORE it is split, so an
     encoded slash (%2F) separates segments, and '+' in a path is a space (the
     form-body rule). ".." at the root is dropped (Lm_filename_util.simplify_path),
     so a path cannot climb above the root.
   - parse_post_body, application/x-www-form-urlencoded: fixed bodies, then a
     model: 2,000 generated lists of 1-4 (key, value) pairs over "ab =&+%/\t",
     each encoded the usual way (space -> '+', letters as themselves, every other
     byte %XX), joined with '&'; the parse must give back the list.
   NOT covered: multipart/form-data. The generator is a fixed linear
   congruential sequence, not Random (its sequence differs by OCaml version). *)
open Http_server_type

let state = ref 7
let next () = state := (!state * 1103515245 + 12345) land 0x7fffffff; !state lsr 8
let pick n = next () mod n

let show l = "[" ^ String.concat "; " (List.map (Printf.sprintf "%S") l) ^ "]"
let showp l =
  "[" ^ String.concat "; " (List.map (fun (k, v) -> Printf.sprintf "(%S, %S)" k v) l) ^ "]"

let guard f = try f () with Failure m -> "Failure " ^ m | Not_found -> "Not_found"

let uri s = Printf.printf "decode_uri %S = %s\n" s (guard (fun () -> show (Http_simple.decode_uri s)))

let form =
  { content_type_main = "application"; content_type_sub = "x-www-form-urlencoded"; content_type_params = [] }

let post s =
  Printf.printf "post %S = %s\n" s (guard (fun () -> showp (Http_simple.parse_post_body form s)))

let encode s =
  let b = Buffer.create 16 in
  String.iter (fun c ->
      match c with
      | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' -> Buffer.add_char b c
      | ' ' -> Buffer.add_char b '+'
      | c -> Buffer.add_string b (Printf.sprintf "%%%02X" (Char.code c))) s;
  Buffer.contents b

let alphabet = "ab =&+%/\t"
let gen_string () = String.init (pick 4) (fun _ -> alphabet.[pick (String.length alphabet)])

let () =
  List.iter uri
    [ ""; "/"; "/a/b"; "/a//b/"; "/a/./b"; "/a/../b"; "/../../etc"; "/a%2Fb"; "/a+b"; "/a%20b"; "/%zz" ];
  List.iter post
    [ ""; "a"; "a="; "=b"; "a=1&b=2"; "a=b=c"; "a&&b"; "a=1&"; " a = 1 "; "a+b=c+d"; "k=%26%3D" ];
  let n = 2000 and bad = ref 0 and first = ref "" in
  for _ = 1 to n do
    let pairs = List.init (1 + pick 4) (fun _ -> gen_string (), gen_string ()) in
    let body = String.concat "&" (List.map (fun (k, v) -> encode k ^ "=" ^ encode v) pairs) in
    let got = guard (fun () -> showp (Http_simple.parse_post_body form body)) in
    if got <> showp pairs then begin
      if !bad = 0 then first := Printf.sprintf "%S: got %s, want %s" body got (showp pairs);
      incr bad
    end
  done;
  Printf.printf "form-urlencoded round trip: %d of %d disagree%s\n" !bad n
    (if !bad = 0 then "" else " (first: " ^ !first ^ ")")
