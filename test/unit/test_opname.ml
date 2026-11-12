(* Opname (refiner/refbase): hash-consed operator names. An opname is a
   string list, innermost name first (make_opname ["a"; "b"] is a inside b);
   string_of_opname prints it outermost first, separated by "!", and
   opname_root is the outermost name. Opnames built here are shared
   (make_opname returns the same record for the same list). A copy that
   went through Marshal carries a different token, so it is not shared:
   eq, intern and normalize_opname then look it up again and re-point it.
   dst_opname's remainder is a new record, not the shared one, but eq and
   intern must still treat it as the opname it names, also when it was split
   off a marshalled copy. Each line prints what the code returns. *)

open Opname

let show_list l = "[" ^ String.concat "; " (List.map (fun s -> "\"" ^ s ^ "\"") l) ^ "]"
let b = string_of_bool
let line name v = Printf.printf "%-52s %s\n" name v
let attempt name f =
  line name (try f () with Invalid_argument m -> "Invalid_argument " ^ m | Not_found -> "Not_found")

let copy (op : opname) : opname = Marshal.from_string (Marshal.to_string op []) 0

let () =
  let ab = make_opname [ "a"; "b" ] in
  line "string_of_opname [a; b]" (string_of_opname ab);
  line "opname_root [a; b]" (opname_root ab);
  line "dest_opname [a; b]" (show_list (dest_opname ab));
  line "string_of_opname nil" ("\"" ^ string_of_opname nil_opname ^ "\"");
  line "opname_root nil" ("\"" ^ opname_root nil_opname ^ "\"");
  line "dest_opname nil" (show_list (dest_opname nil_opname));
  line "make_opname [] == nil_opname" (b (make_opname [] == nil_opname));
  line "make_opname [a; b] == make_opname [a; b]" (b (make_opname [ "a"; "b" ] == ab));
  line "mk_opname a (make_opname [b]) == [a; b]" (b (mk_opname "a" (make_opname [ "b" ]) == ab));
  attempt "dst_opname [a; b]" (fun () ->
      let s, rest = dst_opname ab in
      Printf.sprintf "%s, %s (shared: %b)" s (show_list (dest_opname rest)) (rest == make_opname [ "b" ]));
  attempt "dst_opname nil" (fun () -> let s, _ = dst_opname nil_opname in s);
  line "eq [a; b] [a; b]" (b (eq ab (make_opname [ "a"; "b" ])));
  line "eq [a; b] [b; a]" (b (eq ab (make_opname [ "b"; "a" ])));
  line "eq [a; b] [a]" (b (eq ab (make_opname [ "a" ])));
  line "compare [a; b] [a; b]" (string_of_int (compare ab (make_opname [ "a"; "b" ])));
  line "compare [a] [b] < 0" (b (compare (make_opname [ "a" ]) (make_opname [ "b" ]) < 0));
  (* A marshalled copy. *)
  let m = copy ab in
  line "marshalled copy == original" (b (m == ab));
  line "marshalled copy: string_of_opname" (string_of_opname m);
  line "marshalled copy: eq copy original" (b (eq m ab));
  line "marshalled copy: eq copy [b; a]" (b (eq (copy ab) (make_opname [ "b"; "a" ])));
  line "marshalled copy: intern copy == intern original" (b (intern (copy ab) == intern ab));
  line "marshalled copy: normalize_opname copy == original" (b (normalize_opname (copy ab) == ab));
  line "marshalled copy: mk_opname c copy == [c; a; b]"
    (b (mk_opname "c" (copy ab) == make_opname [ "c"; "a"; "b" ]));
  line "marshalled copy: compare copy original" (string_of_int (compare (copy ab) ab));
  line "dst_opname [a; b]: eq rest [b]" (b (eq (snd (dst_opname ab)) (make_opname [ "b" ])));
  line "marshalled copy: dst_opname, eq rest [b]" (b (eq (snd (dst_opname (copy ab))) (make_opname [ "b" ])));
  line "marshalled copy: dst_opname, intern rest == intern [b]"
    (b (intern (snd (dst_opname (copy ab))) == intern (make_opname [ "b" ])));
  line "marshalled copy: OpnameSet.mem copy {original}" (b (OpnameSet.mem (OpnameSet.singleton ab) (copy ab)));
  (* The special opnames. *)
  List.iter (fun (n, op) -> line ("special " ^ n) (string_of_opname op))
    [ "var_opname", var_opname; "context_opname", context_opname; "xperv", xperv;
      "sequent_opname", sequent_opname; "xnil_opname", xnil_opname; "xcons_opname", xcons_opname;
      "xconcl_opname", xconcl_opname ];
  line "sequent_opname == make_opname [sequent; Perv]" (b (sequent_opname == make_opname [ "sequent"; "Perv" ]))
