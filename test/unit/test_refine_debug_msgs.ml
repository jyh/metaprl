(* The "refine" and "rewrites" debug messages of five rewrite creators in
   Refine (refiner/refiner/refine.ml): delayed_rewrite, create_ml_rewrite,
   create_cond_rewrite (and its application trace), delayed_cond_rewrite and
   create_ml_cond_rewrite, which no unit test turned on (2026-11-15
   profile).  test_refine_rw_debug covers create_rewrite's.
   Each creator is called once with both flags off and once with both on,
   in a null refiner; the conditional rewrite  k --> c if q  is then applied
   through crwtactic at the conclusion of  >- k.  Its stderr lines are
   printed as they come, so the expected file pins them.
   Pinned as found: delayed_cond_rewrite's message names
   "add_delayed_cond_rewrite" and create_ml_cond_rewrite's names
   "add_ml_cond_rewrite"; the other three name their own function. *)
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.Refine

(* Linking Simple_print installs the term printer the "rewrites" trace uses. *)
module P = Simple_print.SimplePrint
let _ = P.string_of_term

let op s = Opname.make_opname [ s ]
let k = mk_simple_term (op "k") [] and c = mk_simple_term (op "c") [] and q = mk_simple_term (op "q") []
let seq concl = mk_sequent_term { sequent_args = mk_xlist_term []; sequent_hyps = SeqHyp.empty; sequent_concl = concl }

let say s = flush stderr; print_string s; print_newline ()

let run tag =
  let build = null_refiner ("test_refine_debug_msgs_" ^ tag) in
  say "  create_rewrite (for delayed_rewrite to justify)";
  ignore (create_rewrite build "kc" k c);
  say "  delayed_rewrite";
  delayed_rewrite build "kc" k c (fun () -> failwith "never forced");
  say "  create_ml_rewrite";
  ignore (create_ml_rewrite build "mlkc" (fun t -> t));
  say "  create_cond_rewrite";
  let crw = match create_cond_rewrite build "ckc" Rewrite.empty_args_spec [] [ q ] k c with
    | CondRW r -> r Rewrite.empty_rw_args [] | PrimRW _ -> failwith "prim" in
  say "  delayed_cond_rewrite";
  delayed_cond_rewrite build "ckc" [] [ q ] k c (fun () -> failwith "never forced");
  say "  create_ml_cond_rewrite";
  ignore (create_ml_cond_rewrite build "mlckc" (fun _ _ t -> t, [], (fun _ _ goal _ -> goal)));
  say "  crwtactic (k --> c if q) at the conclusion of >- k";
  let at0 = crwaddr (TermAddr.make_address [ Term_addr_sig.ClauseAddr 0 ]) crw in
  (match refine any_sentinal (crwtactic 0 at0) (mk_msequent (seq k) []) with
   | sg, _ -> say (Printf.sprintf "  %d subgoals" (List.length sg))
   | exception Refiner.Refiner.RefineError.RefineError (loc, _) -> say ("  refused at " ^ loc))

let () =
  say "== both flags off";
  run "off";
  Lm_debug.set_debug "refine" true; Lm_debug.set_debug "rewrites" true;
  say "== \"refine\" and \"rewrites\" on";
  run "on";
  Lm_debug.set_debug "refine" false; Lm_debug.set_debug "rewrites" false
