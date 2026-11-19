(* Dform's dform_depth check (refiner/reflib/dform.ml: the slot wrapper
   that, with the debug flag on, compares the formatting buffer's zone
   depth before and after a slot is printed and names an unbalanced one),
   which nothing reached (2026-11-18 rank737; default printing never
   calls slot, so test_dform_bvars could not).  Three forms in a theory
   dfd: wrap{'a} = "[" slot{'a} "]"; shut, an OCaml printer that pushes a
   zone and pops it; open, one that pushes and never pops.  Each term is
   printed with the flag off and on.
   Read from the output: an unbalanced buffer is refused at flush either
   way, with a message that says to use debug_dform_depth; with the flag
   on, each slot whose depth changed is named on stderr, the innermost
   first, so wrap{wrap{open}} names open and then wrap{open}.
   The expected file is the output of the code as written (2026-11-18),
   never typed.  Mutants (2026-11-18, each rebuilt and relinked; an
   identity control unchanged): the depth test inverted, the slot not
   printed inside the check, the message's text dropped: 3 of 3 RED. *)
open Opname
open Refiner.Refiner
open TermType
open Term
open TermMan
open Dform

let uop s = make_opname [ s; "Dfd" ]
let sv s = mk_so_var_term (Lm_symbol.add s) [] []
let mk o ts = mk_term (mk_op (uop o) []) (List.map (fun t -> mk_bterm [] t) ts)
let slot0 t = mk_term (mk_op (mk_opname "slot" xperv) []) [ mk_bterm [] t ]
let str = mk_xstring_term
let form name pattern print =
  add_dform { dform_modes = AllModes; dform_pattern = pattern; dform_options = []; dform_print = print; dform_name = name }

let () =
  form "wrap" (mk "wrap" [ sv "a" ]) (DFormExpansion (mk_xlist_term [ str "["; slot0 (sv "a"); str "]" ]));
  (* a printer that opens a zone and never closes it *)
  form "open" (mk "open" []) (DFormPrinter (fun info -> Lm_rformat.format_pushm info.dform_buffer 2; Lm_rformat.format_string info.dform_buffer "open"));
  form "shut" (mk "shut" []) (DFormPrinter (fun info -> Lm_rformat.format_pushm info.dform_buffer 2; Lm_rformat.format_string info.dform_buffer "shut"; Lm_rformat.format_popm info.dform_buffer));
  Mp_resource.close_theory "dfd"

let base = get_mode_base (Mp_resource.theory_bookmark "dfd") "prl" null_shortener
let leaf = mk "leaf" []

let () =
  List.iter (fun flag ->
      Lm_debug.set_debug "dform_depth" flag;
      List.iter (fun (name, t) ->
          let r = try string_of_term base t with Invalid_argument m -> "Invalid_argument " ^ m in
          Printf.printf "dform_depth %-5b %-18s %s\n%!" flag name r;
          flush stderr)
        [ "wrap{leaf}", mk "wrap" [ leaf ];
          "wrap{shut}", mk "wrap" [ mk "shut" [] ];
          "wrap{open}", mk "wrap" [ mk "open" [] ];
          "wrap{wrap{open}}", mk "wrap" [ mk "wrap" [ mk "open" [] ] ] ])
    [ false; true ];
  Lm_debug.set_debug "dform_depth" false
