(* Dform (refiner/reflib), the display-form engine: a table of forms per
   theory, kept as the "dform" resource, selected by mode, with precedences
   that decide where parentheses go.  The proof census runs 237 of its 551
   points and the unit tests 46 (2026-11-11 reach census).
   One theory, "dft", installs its forms through Dform.add_dform the way a
   theory's display forms do, and is closed; each case prints a term
   through Dform.string_of_term with a base taken at that theory's
   bookmark.  The forms:
     plus{'a; 'b}    slot["le"]{'a} " + " slot["lt"]{'b}, precedence P,
                     parenthesised when needed (DFormParens)
     times{'a; 'b}   slot["le"]{'a} " * " slot["lt"]{'b}, precedence T,
                     P < T, parenthesised when needed
     box{'a}         "[" slot{'a} "]", inheriting its context's precedence
     neg{'a}         "~" slot{'a}, in mode tex only
     hide{'a}        "hidden", in every mode except html
     pair{'a; 'b}    an OCaml printer: "<" a "," b ">" through dform_printer
     boom            an OCaml printer that raises Failure
     lit[s:s]        slot["raw"; s] (the parameter, raw), slot["esc"; s] and
                     slot["cesc"; s] for the escapes
   The expected file is the output of the code as written (2026-11-11),
   never typed.  Pinned as found: an equal-precedence child is
   parenthesised in a slot["le"] and not in a slot["lt"], so with the
   theories' own placement (le on the left, as in itt_int_base's add) a
   nested plus displays right-associated: (1 + 2) + 3 keeps its
   parentheses and 1 + (2 + 3) prints as 1 + 2 + 3.  Also: the raw mode ignores every form, the src mode
   selects none of these (src forms must name it), a form naming the raw
   mode is refused, and an unknown bookmark fails. *)
open Lm_symbol
open Opname
open Term_sig
open Refiner.Refiner
open TermType
open Term
open TermMan
open Dform

let uop s = make_opname [ s; "Dft" ]
let sv s = mk_so_var_term (Lm_symbol.add s) [] []
let mk o ts = mk_term (mk_op (uop o) []) (List.map (fun t -> mk_bterm [] t) ts)
let slot eq t = mk_term (mk_op (mk_opname "slot" xperv) [ make_param (String eq) ]) [ mk_bterm [] t ]
let slot0 t = mk_term (mk_op (mk_opname "slot" xperv) []) [ mk_bterm [] t ]
let slot_s eq s = mk_term (mk_op (mk_opname "slot" xperv) [ make_param (String eq); make_param (MString (Lm_symbol.add s)) ]) []
let str = mk_xstring_term
let lit_p v = mk_term (mk_op (uop "lit") [ make_param (MString (Lm_symbol.add v)) ]) []
let lit s = mk_term (mk_op (uop "lit") [ make_param (String s) ]) []
let num n = mk_term (mk_op (uop "num") [ make_param (Number (Lm_num.num_of_int n)) ]) []
let plus a b = mk "plus" [ a; b ]
let times a b = mk "times" [ a; b ]
let box a = mk "box" [ a ]
let neg a = mk "neg" [ a ]
let hide a = mk "hide" [ a ]
let pair a b = mk "pair" [ a; b ]
let boom = mk "boom" []
let x = mk_var_term (Lm_symbol.add "x")

let prec_p = Precedence.new_prec ()
let prec_t = Precedence.new_prec ()
let () = Precedence.add_lt prec_p prec_t

let form ?(modes = AllModes) ?(options = []) name pattern print =
  add_dform { dform_modes = modes; dform_pattern = pattern; dform_options = options; dform_print = print; dform_name = name }

let () =
  form "plus" ~options:[ DFormPrec prec_p; DFormParens ] (plus (sv "a") (sv "b"))
    (DFormExpansion (mk_xlist_term [ slot "le" (sv "a"); str " + "; slot "lt" (sv "b") ]));
  form "times" ~options:[ DFormPrec prec_t; DFormParens ] (times (sv "a") (sv "b"))
    (DFormExpansion (mk_xlist_term [ slot "le" (sv "a"); str " * "; slot "lt" (sv "b") ]));
  form "box" ~options:[ DFormInheritPrec ] (box (sv "a"))
    (DFormExpansion (mk_xlist_term [ str "["; slot0 (sv "a"); str "]" ]));
  form "neg" ~modes:(Modes [ "tex" ]) (neg (sv "a")) (DFormExpansion (mk_xlist_term [ str "~"; slot0 (sv "a") ]));
  form "hide" ~modes:(ExceptModes [ "html" ]) (hide (sv "a")) (DFormExpansion (mk_xlist_term [ str "hidden" ]));
  form "pair" (pair (sv "a") (sv "b"))
    (DFormPrinter (fun info ->
         match dest_term info.dform_term with
         | { term_terms = [ a; b ]; _ } ->
             Lm_rformat.format_string info.dform_buffer "<";
             info.dform_printer info.dform_buffer NOParens (dest_bterm a).bterm;
             Lm_rformat.format_string info.dform_buffer ",";
             info.dform_printer info.dform_buffer NOParens (dest_bterm b).bterm;
             Lm_rformat.format_string info.dform_buffer ">"
         | _ -> Lm_rformat.format_string info.dform_buffer "?"));
  form "boom" boom (DFormPrinter (fun _ -> failwith "boom"));
  form "lit" (lit_p "s")
    (DFormExpansion (mk_xlist_term [ slot_s "raw" "s"; str "|"; slot_s "esc" "s"; str "|"; slot_s "cesc" "s" ]));
  Mp_resource.close_theory "dft";
  (* the raw-mode check runs when the theory's table is built, not here *)
  form ~modes:(Modes [ "raw" ]) "bad" (mk "bad" []) (DFormExpansion (mk_xlist_term [ str "bad" ]));
  Mp_resource.close_theory "dft_raw"

let base mode = get_mode_base (Mp_resource.theory_bookmark "dft") mode null_shortener

let run name f =
  let r =
    try f () with
    | Invalid_argument s -> "INVALID_ARGUMENT: " ^ s
    | Failure s -> "FAILURE: " ^ s
    | Not_found -> "NOT_FOUND"
  in
  Printf.printf "%-34s %s\n" name r

let show mode name t = run (mode ^ " " ^ name) (fun () -> string_of_term (base mode) t)

let a = num 1 and b = num 2 and c = num 3

let () =
  print_endline "== precedence and parentheses (prl)";
  List.iter (fun (n, t) -> show "prl" n t)
    [ "1 + 2", plus a b;
      "(1 + 2) + 3", plus (plus a b) c;
      "1 + (2 + 3)", plus a (plus b c);
      "(1 * 2) + 3", plus (times a b) c;
      "1 + (2 * 3)", plus a (times b c);
      "(1 + 2) * 3", times (plus a b) c;
      "1 * (2 + 3)", times a (plus b c);
      "(1 * 2) * 3", times (times a b) c;
      "1 * (2 * 3)", times a (times b c);
      "box{1 + 2} * 3", times (box (plus a b)) c;
      "box{1 + 2}", box (plus a b);
      "pair{1 + 2; 3 * 1}", pair (plus a b) (times c a);
      "plus{x; 'v}", plus x (sv "v");
      "an undisplayed term", mk "other" [ a ];
      "num[1] (no form)", a ];
  print_endline "== modes";
  List.iter (fun mode ->
      show mode "neg{1}" (neg a);
      show mode "hide{1}" (hide a);
      show mode "1 + 2" (plus a b))
    [ "prl"; "tex"; "html"; "src"; "raw" ];
  print_endline "== parameters through slot";
  show "prl" "lit[\"a\\tb\"q\"]" (lit "a\tb\"q");
  print_endline "== errors";
  show "prl" "boom" boom;
  show "prl" "plus{boom; 1}" (plus boom a);
  run "a theory with a form naming raw" (fun () ->
      string_of_term (get_mode_base (Mp_resource.theory_bookmark "dft_raw") "prl" null_shortener) a);
  run "an unknown bookmark" (fun () ->
      string_of_term (get_mode_base (Mp_resource.theory_bookmark "no_such_theory") "prl" null_shortener) a);
  print_endline "== meta terms and bound terms";
  run "prl rule 1 + 2 --> 2 * 3" (fun () ->
      string_of_mterm (base "prl") (MetaImplies (MetaTheorem (plus a b), MetaTheorem (times b c))));
  run "prl rewrite 1 + 2 <--> 3" (fun () ->
      string_of_mterm (base "prl") (MetaIff (MetaTheorem (plus a b), MetaTheorem c)));
  run "prl bterm y. y + 1" (fun () ->
      string_of_bterm (base "prl") (mk_bterm [ Lm_symbol.add "y" ] (plus (mk_var_term (Lm_symbol.add "y")) a)));
  print_endline "== slot terms";
  let sb = save_slot_terms (base "prl") in
  let s = string_of_term sb (plus a (times b c)) in
  Printf.printf "%-34s %s\n" "printed with slot tags" s;
  Lm_string_set.StringTable.iter (fun k t -> Printf.printf "  tag %-28s %s\n" k (string_of_term (base "prl") t))
    (get_slot_terms sb)
