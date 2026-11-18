(* Rewrite.print_rewrite_rule (refiner/rewrite/rewrite.ml), the only caller
   of Rewrite_debug.print_contractum and print_strict, which no unit test
   reached (2026-11-15 profile).  A rewrite  f{'a; 'b} --> f{'b; 'a}  is
   compiled Strict and Relaxed with Rewrite.term_rewrite and printed into
   Lm_printf's string channel; then one with two contracta, and one whose
   contractum is an ML function (Rewrite.fun_rewrite).
   The expected file is the output of the code as written, never typed. *)
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan

let op s = Opname.make_opname [ s ]
let sov x = mk_so_var_term (Lm_symbol.add x) [] []
let f a b = mk_simple_term (op "f") [ a; b ]

let show title rw =
  ignore (Lm_printf.flush_stdstr ());
  Lm_printf.fprintf Lm_printf.stdstr "%a@." Rewrite.print_rewrite_rule rw;
  Printf.printf "== %s\n" title;
  List.iter (fun l ->
      let n = String.length l in
      let l = if n > 0 && l.[n - 1] = '\r' then String.sub l 0 (n - 1) else l in
        if String.trim l <> "" then Printf.printf "  %s\n" l) (String.split_on_char '\n' (Lm_printf.flush_stdstr ()))

let () =
  let redex = f (sov "a") (sov "b") and con = f (sov "b") (sov "a") in
  show "Strict" (Rewrite.term_rewrite Rewrite_sig.Strict Rewrite.empty_args_spec [ redex ] [ con ]);
  show "Relaxed" (Rewrite.term_rewrite Rewrite_sig.Relaxed Rewrite.empty_args_spec [ redex ] [ con ]);
  show "Strict, two contracta (a condition)" (Rewrite.term_rewrite Rewrite_sig.Strict Rewrite.empty_args_spec [ redex ] [ con; sov "a" ]);
  show "Relaxed, an ML contractum (fun_rewrite)" (Rewrite.fun_rewrite Rewrite_sig.Relaxed redex (fun t -> t))
