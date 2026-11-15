(* unit-link: filter *)
(* MathBus's file form of a term (library/mathBus.ml write_node /
   read_node, through Mbterm.write_node_to_file and read_node_from_file),
   the Nuprl-5 link's wire format: each term goes to a temporary file
   (its name is never printed) and back, and the line prints the file's
   size, its last 8 characters (the trailer word, which read_node reads
   and ignores) and "same" when the term read back is alpha_equal to the
   one written.  The last base64 group is padded one, two or no times
   here, and it always ends in the trailer's low byte, 0x00, so the bits a
   padded group drops are zero: a change to how they are shifted shows in
   no output.  With use_unicode false and true (two characters to a 32-bit
   word: string_value_with_unicode).  The writers (write_32bit,
   flush_buffer, flush_bufferp) and readers (read_32bit) were reached by no
   unit test, theory build or proof census (2026-11-15 rank).  The labels
   and their SubTypes (which subterms are 32-bit integers) are stored in
   the local registry here, as test_mbterm_round_trip does: the link reads
   them from lib/registry.txt, which no build installs.
   The expected file is the output of the code as written (2026-11-15),
   never typed. *)
open Refiner.Refiner.Term
open Refiner.Refiner.TermType
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst

let labels = [ "Attributes"; "String"; "LongInteger"; "Token"; "Term"; "Variable"; "Bindings"; "Level";
               "ObjectId"; "ParmList"; "TermIndex"; "TokenIndex"; "StringIndex"; "MString"; "MLongInteger";
               "MLevel"; "MToken" ]
let () =
  List.iteri (fun i l -> Registry.registry_store_local l "StringId" (Lint32.lint32_of_int (0x1101 + i))) labels;
  (* SubTypes: which subterms are 32-bit integers (-1: all of them; 0: none), as MathBus.subtypes reads it *)
  let ints = [ "String"; "LongInteger"; "Token"; "Variable"; "TermIndex"; "TokenIndex"; "StringIndex"; "MString"; "MLongInteger"; "MToken" ] in
  List.iter (fun l -> Registry.registry_store_local l "SubTypes" (Lint32.lint32_of_int (if List.mem l ints then -1 else 0))) labels;
  MathBus.assign_mbs_vals ();
  Mbterm.assign_mbs_terms ()

let v = Lm_symbol.add
let op s ps = mk_op (Opname.make_opname [ s; "Test" ]) ps
let c = mk_term (op "c" []) []
let str s = make_param (String s)

(* Write the MathBus node of a term to a file, read it back, and compare the terms.
   The file is a temporary one; its name is never printed. *)
let file_trip name t =
  let tmp = Filename.temp_file "mbfile" ".mb" in
  let r =
    try
      Mbterm.write_node_to_file (Mbterm.mbterm_of_term t) tmp;
      let size = (Unix.stat tmp).Unix.st_size in
      (* the file's last 8 characters: the trailer word, which read_node reads and ignores *)
      let tail = let ic = open_in_bin tmp in let n = in_channel_length ic in
                 seek_in ic (max 0 (n - 8)); let s = really_input_string ic (min 8 n) in close_in ic; String.escaped s in
      let t' = Mbterm.term_of_mbterm (Mbterm.read_node_from_file tmp) in
        Printf.sprintf "%5d bytes  ends %-12s %s" size tail (if alpha_equal t t' then "same" else "DIFFERS: " ^ Simple_print.SimplePrint.string_of_term t')
    with e -> "raised " ^ Printexc.to_string e
  in
    (try Sys.remove tmp with _ -> ());
    Printf.printf "%-22s %s\n%!" name r

let cases = [
  "constant", c;
  "strings, odd and even", mk_term (op "s" [ str "abc"; str "abcd"; str "" ]) [];
  "a long string", mk_term (op "s" [ str (String.make 300 'x') ]) [];
  "a 17-bit number", mk_term (op "n" [ make_param (Number (Lm_num.num_of_int 100000)) ]) [];
  "a big number", mk_term (op "n" [ make_param (Number (Lm_num.num_of_string "123456789012")) ]) [];
  "a binding", mk_term (op "lam" []) [ mk_bterm [ v "x" ] (mk_var_term (v "x")) ];
  "200 subterms", mk_term (op "g" []) (List.init 200 (fun _ -> mk_bterm [] c));
]

let () =
  print_endline "use_unicode false:";
  List.iter (fun (n, t) -> file_trip n t) cases;
  MathBus.use_unicode := true;
  print_endline "use_unicode true:";
  List.iter (fun (n, t) -> file_trip n t) cases
