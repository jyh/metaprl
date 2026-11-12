(* Dform's formatting primitives, the Perv forms a theory's display forms
   are written in (refiner/reflib/dform.ml init_list: szone, azone, ezone,
   pushm with a number, a string or nothing, popm, space, hspace) and
   slot on a number, token or string parameter: the lines only the proof
   census reached (2026-11-11 reach census: 29 lines of dform.ml reached by
   the census and by no unit test, test_dform included).  One theory,
   "dfp", installs forms the way test_dform's does; each term is printed
   through Dform.format_term with a base at that theory's bookmark, and the
   buffer is rendered at width 80 and at width 16 (to show where each zone
   breaks).  Every output is the code's own (measured 2026-11-11).
   Not covered: pushfont / popfont (their escape codes come from the
   terminal's terminfo entry, so the output would be the machine's), slot
   on a shape, an operator or a level parameter. *)
open Lm_symbol
open Opname
open Term_sig
open Refiner.Refiner
open TermType
open Term
open TermMan
open Dform

let uop s = make_opname [ s; "Dfp" ]
let sv s = mk_so_var_term (Lm_symbol.add s) [] []
let mk o ts = mk_term (mk_op (uop o) []) (List.map (fun t -> mk_bterm [] t) ts)
let slot eq t = mk_term (mk_op (mk_opname "slot" xperv) [ make_param (String eq) ]) [ mk_bterm [] t ]
let slot0 t = mk_term (mk_op (mk_opname "slot" xperv) []) [ mk_bterm [] t ]
let slot_s eq s = mk_term (mk_op (mk_opname "slot" xperv) [ make_param (String eq); make_param (MString (Lm_symbol.add s)) ]) []
let str = mk_xstring_term
let lit_p v = mk_term (mk_op (uop "lit") [ make_param (MString (Lm_symbol.add v)) ]) []
let lit s = mk_term (mk_op (uop "lit") [ make_param (String s) ]) []
let form ?(modes = AllModes) ?(options = []) name pattern print =
  add_dform { dform_modes = modes; dform_pattern = pattern; dform_options = options; dform_print = print; dform_name = name }
let leaf s = mk_term (mk_op (uop s) []) []
let prim name params = mk_term (mk_op (mk_opname name xperv) params) []
let pnum n = make_param (Number (Lm_num.num_of_int n))
let pstr s = make_param (String s)
let words = [ str "aaaaaa"; str "bbbbbb"; str "cccccc" ]
let spaced sep = List.concat (List.mapi (fun i w -> if i = 0 then [ w ] else [ sep; w ]) words)

let () =
  let f name body = form name (leaf name) (DFormExpansion (mk_xlist_term body)) in
  f "sz" ((prim "szone" [] :: str "head:" :: prim "pushm" [ pnum 3 ] :: spaced (prim "space" [])) @ [ prim "popm" []; prim "ezone" [] ]);
  f "az" ((prim "azone" [] :: spaced (prim "space" [])) @ [ prim "ezone" [] ]);
  f "hs" ((prim "szone" [] :: spaced (prim "hspace" [])) @ [ prim "ezone" [] ]);
  f "pmstr" ((prim "szone" [] :: str "head:" :: prim "pushm" [ pstr "--" ] :: spaced (prim "space" [])) @ [ prim "popm" []; prim "ezone" [] ]);
  f "pm0" ((prim "szone" [] :: str "head:" :: prim "pushm" [] :: spaced (prim "space" [])) @ [ prim "popm" []; prim "ezone" [] ]);
  form "n" (mk_term (mk_op (uop "n") [ make_param (MNumber (Lm_symbol.add "k")) ]) [])
    (DFormExpansion (mk_xlist_term [ str "#"; mk_term (mk_op (mk_opname "slot" xperv) [ make_param (MNumber (Lm_symbol.add "k")) ]) [] ]));
  form "t" (mk_term (mk_op (uop "t") [ make_param (MToken (Lm_symbol.add "o")) ]) [])
    (DFormExpansion (mk_xlist_term [ str "@"; mk_term (mk_op (mk_opname "slot" xperv) [ make_param (MToken (Lm_symbol.add "o")) ]) [] ]));
  form "s" (mk_term (mk_op (uop "s") [ make_param (MString (Lm_symbol.add "s")) ]) [])
    (DFormExpansion (mk_xlist_term [ str "$"; mk_term (mk_op (mk_opname "slot" xperv) [ make_param (MString (Lm_symbol.add "s")) ]) [] ]));
  Mp_resource.close_theory "dfp"

let base = get_mode_base (Mp_resource.theory_bookmark "dfp") "prl" null_shortener
let render w t = try let buf = Lm_rformat.new_buffer () in format_term base buf t; Lm_rformat_text.print_text_string w buf with Invalid_argument s -> "Invalid_argument " ^ s

let () =
  List.iter (fun (name, t) ->
      Printf.printf "%s\n  w80 %S\n  w16 %S\n" name (render 80 t) (render 16 t))
    [ "szone \"head:\" pushm[3] a space b space c popm ezone", leaf "sz";
      "azone a space b space c ezone", leaf "az";
      "szone a hspace b hspace c ezone", leaf "hs";
      "szone \"head:\" pushm[\"--\"] ... popm ezone", leaf "pmstr";
      "szone \"head:\" pushm ... popm ezone", leaf "pm0";
      "n[7]: \"#\" slot[@k]", mk_term (mk_op (uop "n") [ pnum 7 ]) [];
      "t[Foo]: \"@\" slot[@o] (a token)", mk_term (mk_op (uop "t") [ make_param (Token (make_opname [ "Foo"; "Bar" ])) ]) [];
      "s[\"q\"]: \"$\" slot[@s]", mk_term (mk_op (uop "s") [ pstr "q" ]) [] ]
