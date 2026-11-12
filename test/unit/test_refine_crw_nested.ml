(* A conditional rewrite whose condition mentions a bound variable
   (refiner/refiner/refine.ml, create_cond_rewrite), on the two shapes
   test_refine_crw_bound leaves out. Applied at an address where the
   redex does not match, it is refused by the rewriter itself. Under two
   binders of the same name the inner binder is renamed, and the refusal
   names the renamed variable (x1). In a null refiner, the conditional
   rewrite
     hp: h{'a} --> 'a  if [ p{'a} ]
   is applied by crwtactic at the given address in the conclusion of a
   closed sequent with no hypotheses. Each line prints the subgoals or the
   refusal. The expected output is the code's own, never typed. Pinned as
   it reads. *)
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.Refine
let op s = Opname.make_opname [ s ]
let st s l = mk_simple_term (op s) l
let sv x = mk_so_var_term (Lm_symbol.add x) [] []
let show_t t = Simple_print.SimplePrint.string_of_term t
let seq concl = mk_sequent_term { sequent_args = mk_xlist_term []; sequent_hyps = SeqHyp.of_list []; sequent_concl = concl }
let name = "test_refine_crw_nested"
let build = null_refiner name
let es = Rewrite.empty_args_spec
let ra = Rewrite.empty_rw_args
let mkcrw n conds redex contractum =
  match create_cond_rewrite build n es [] conds redex contractum with
  | CondRW r -> prim_cond_rewrite build n [] conds redex contractum; r ra []
  | PrimRW _ -> failwith "prim"
let x = Lm_symbol.add "x"
let lam b = mk_term (mk_op (op "lam") []) [ mk_bterm [ x ] b ]
let hp = mkcrw "hp" [ st "p" [ sv "a" ] ] (st "h" [ sv "a" ]) (sv "a")
let addr l = TermAddr.make_address (Term_addr_sig.ClauseAddr 0 :: List.map (fun i -> Term_addr_sig.Subterm i) l)
let sent () = sentinal_of_refiner (refiner_of_build build)
let case label goal l crw =
  let r =
    try
      let subs, _ = refine (sent ()) (crwtactic 0 (crwaddr (addr l) crw)) (mk_msequent (seq goal) []) in
      "subgoals " ^ String.concat ", " (List.map (fun m -> show_t (explode_sequent (msequent_goal m)).sequent_concl) subs)
    with RefineError.RefineError (n, RefineError.StringVarError (s, v)) -> Printf.sprintf "refused (%s): %s: %s" n s (Lm_symbol.string_of_symbol v)
       | RefineError.RefineError (n, RefineError.RewriteAddressError (a, n', RefineError.StringVarError (s, v))) ->
           Printf.sprintf "refused (%s at %s, %s): %s: %s" n (TermAddr.string_of_address a) n' s (Lm_symbol.string_of_symbol v)
       | RefineError.RefineError (n, _) -> "refused (" ^ n ^ ") other"
  in
  Printf.printf "%-44s %s\n" label r
let () =
  case "hp on lam{x. h{x}} at [] (no match)" (lam (st "h" [ mk_var_term x ])) [] hp;
  case "hp on lam{x. lam{x. h{x}}} at [1;1]" (lam (lam (st "h" [ mk_var_term x ]))) [ 1; 1 ] hp
