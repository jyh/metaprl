(* Term_shape_gen's printers (refiner/term_gen/term_shape_gen.ml):
   print_shape, pp_print_shape, short_string_of_shape and
   string_of_opparam, and opparam_of_term's refusal of variables and
   sequents, which no unit test, theory build or proof census reached
   (2026-11-15 rank; string_of_opparam is also reached by
   test_rewrite_debug_kinds once it lands).  Each shape is printed by all
   four.  The expected file is the output of the code as written
   (2026-11-15). *)
open Lm_symbol
open Term_sig
open Refiner.Refiner
open Term
open TermMan
open TermShape

let op s = Opname.make_opname [ s; "Tsp" ]
let c = mk_simple_term (op "c") []
let v = Lm_symbol.add
let terms = [
  "c", c;
  "f{c; c}", mk_simple_term (op "f") [ c; c ];
  "lam{x. c}", mk_term (mk_op (op "lam") []) [ mk_bterm [ v "x" ] c ];
  "p[1:n; s:s; t:t]{c}", mk_term (mk_op (op "p") [ make_param (Number (Lm_num.num_of_int 1)); make_param (String "s");
                                                     make_param (Token (op "t")) ]) [ mk_bterm [] c ];
  "q[@n:n; @l:l]", mk_term (mk_op (op "q") [ make_param (MNumber (v "n")); make_param (MLevel (mk_level 0 [ mk_level_var (v "l") 0 ])) ]) [] ]

let pp_string sh =
  let b = Buffer.create 64 in
  let fmt = Lm_printf.formatter_of_buffer b in
  pp_print_shape fmt sh; Lm_printf.pp_print_flush fmt (); Buffer.contents b

let print_string_of sh =
  ignore (Lm_printf.flush_stdstr ());
  print_shape Lm_printf.stdstr sh;
  Lm_printf.flush_stdstr ()

let () =
  List.iter (fun (name, t) ->
      let sh = shape_of_term t in
      Printf.printf "== %s\n  string_of_shape        %s\n  print_shape            %s\n  pp_print_shape         %s\n  short_string_of_shape  %s\n"
        name (string_of_shape sh) (print_string_of sh) (pp_string sh) (short_string_of_shape sh);
      Printf.printf "  string_of_opparam      %s\n"
        (try string_of_opparam (opparam_of_term t) with Invalid_argument s -> "Invalid_argument " ^ s)) terms;
  List.iter (fun (name, t) ->
      Printf.printf "opparam_of_term %-12s %s\n" name
        (try ignore (opparam_of_term t); "accepted" with Invalid_argument s -> "Invalid_argument " ^ s))
    [ "'x", mk_var_term (v "x");
      "'a['x]", mk_so_var_term (v "a") [] [ mk_var_term (v "x") ];
      "sequent", mk_sequent_term { sequent_args = c; sequent_hyps = SeqHyp.of_list [ Hypothesis (v "x", c) ]; sequent_concl = c } ]
