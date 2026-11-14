(* Rewrite_debug's printers (refiner/rewrite/rewrite_debug.ml), which only
   the "rewrite" debug flag reaches: no unit test, theory build or proof
   replay did (2026-11-14 rank: 74 of its 166 points).  With the flag set,
   each rewrite below is compiled (term_rewrite) and applied once
   (apply_rewrite) in term_std, and the trace it writes to stderr is
   captured and printed, followed by the result.  The redexes carry every
   parameter kind (numbers, strings, tokens, levels, variables and the
   meta-parameters), a second-order variable with an argument and a
   binder.  The expected file is the output of the code as written
   (2026-11-14). *)
open Term_sig
open Refiner.Refiner
open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan

let op s = Opname.make_opname [ s ]
let v = Lm_symbol.add
let app o ps ts = mk_term (mk_op (op o) ps) (List.map (fun t -> mk_bterm [] t) ts)
let c0 o = app o [] []
let sov x args = mk_so_var_term (v x) [] args
let lam x t = mk_term (mk_op (op "lam") []) [ mk_bterm [ v x ] t ]
let show t = Simple_print.SimplePrint.string_of_term t

let capture_stderr f =
  let file = Filename.temp_file "trd" ".err" in
  flush stderr; Format.pp_print_flush Format.err_formatter ();
  let saved = Unix.dup Unix.stderr in
  let fd = Unix.openfile file [ Unix.O_WRONLY; Unix.O_TRUNC ] 0o600 in
  Unix.dup2 fd Unix.stderr; Unix.close fd;
  let restore () = flush stderr; Format.pp_print_flush Format.err_formatter (); Unix.dup2 saved Unix.stderr; Unix.close saved in
  let r = (try f () with e -> restore (); raise e) in
  restore ();
  let ic = open_in_bin file in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic; Sys.remove file; s, r

let case name redex contractum target =
  let trace, result = capture_stderr (fun () ->
      try
        let rw = Rewrite.term_rewrite Rewrite_sig.Strict Rewrite.empty_args_spec [ redex ] [ contractum ] in
        String.concat " | " (List.map show (Rewrite.apply_rewrite rw Rewrite.empty_args target []))
      with RefineError.RefineError (s, _) -> "refused (" ^ s ^ ")") in
  Printf.printf "== %s\n%s-> %s\n" name trace result

let () =
  Lm_debug.set_debug "rewrite" true;
  let lvl = make_param (MLevel (mk_level 1 [ mk_level_var (v "i") 0 ])) in
  case "every parameter kind"
    (app "p" [ make_param (MNumber (v "n")); make_param (MString (v "s")); make_param (MToken (v "t")); lvl;
               make_param (Number (Lm_num.num_of_int 3)); make_param (String "x"); make_param (Token (op "tok")) ] [ sov "a" [] ])
    (app "q" [ make_param (MNumber (v "n")); make_param (MString (v "s")) ] [ sov "a" [] ])
    (app "p" [ make_param (Number (Lm_num.num_of_int 7)); make_param (String "str"); make_param (Token (op "k"));
               make_param (MLevel (mk_level 1 [ mk_level_var (v "j") 0 ]));
               make_param (Number (Lm_num.num_of_int 3)); make_param (String "x"); make_param (Token (op "tok")) ] [ c0 "c" ]);
  case "a binder and a second-order variable"
    (app "h" [] [ lam "x" (sov "b" [ mk_var_term (v "x") ]) ]) (sov "b" [ c0 "c" ])
    (app "h" [] [ lam "y" (app "f" [] [ mk_var_term (v "y") ]) ]);
  case "no match" (app "h" [] [ sov "a" [] ]) (sov "a" []) (c0 "c");
  Lm_debug.set_debug "rewrite" false;
  case "flag off" (app "h" [] [ sov "a" [] ]) (sov "a" []) (app "h" [] [ c0 "c" ])
