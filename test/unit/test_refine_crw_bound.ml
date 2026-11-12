(* A conditional rewrite whose condition would mention a variable bound
   ABOVE the place it is applied (refiner/refiner/refine.ml,
   create_cond_rewrite): the refiner refuses with "Rewrite condition has
   free variable where it is not allowed", naming the variable.
   In a null refiner, with lam{x. t} binding x:
     hc: h{'a} --> 'a  if [ p{'a} ]       hk: h{'a} --> 'a  if [ c ]
   applied by crwtactic at the conclusion, at an address under the binder
   or not.  Each line prints the subgoals' conclusions, or the error.
   Model: refused exactly when the instance of 'a contains the bound x and
   'a occurs in the condition. *)
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.Refine

let op s = Opname.make_opname [ s ]
let simple s ts = mk_simple_term (op s) ts
let sv x = mk_so_var_term (Lm_symbol.add x) [] []
let x = Lm_symbol.add "x"
let lam body = mk_term (mk_op (op "lam") []) [ mk_bterm [ x ] body ]
let seq concl = mk_sequent_term { sequent_args = mk_xlist_term []; sequent_hyps = SeqHyp.of_list []; sequent_concl = concl }
let show_t t = Simple_print.SimplePrint.string_of_term t

let name = "test_refine_crw_bound"
let build = null_refiner name
let es = Rewrite.empty_args_spec
let ra = Rewrite.empty_rw_args
let mkcrw n conds redex contractum =
  match create_cond_rewrite build n es [] conds redex contractum with
  | CondRW r -> prim_cond_rewrite build n [] conds redex contractum; r ra []
  | PrimRW _ -> failwith "prim"
let hc = mkcrw "hc" [ simple "p" [ sv "a" ] ] (simple "h" [ sv "a" ]) (sv "a")
let hk = mkcrw "hk" [ simple "c" [] ] (simple "h" [ sv "a" ]) (sv "a")
let at l c = crwaddr (TermAddr.make_address (Term_addr_sig.ClauseAddr 0 :: List.map (fun i -> Term_addr_sig.Subterm i) l)) c
let sent () = sentinal_of_refiner (refiner_of_build build)

let case label rw concl =
  let line =
    try
      let subgoals, _ = refine (sent ()) (crwtactic 0 rw) (mk_msequent (seq concl) []) in
      "subgoals " ^ String.concat " | " (List.map (fun s -> show_t (explode_sequent (fst (dest_msequent s))).sequent_concl) subgoals)
    with RefineError.RefineError (n, e) ->
      let rec err = function
        | RefineError.RewriteAddressError (a, n', e') -> Printf.sprintf "at [%s] %s: %s" (TermAddr.string_of_address a) n' (err e')
        | RefineError.StringVarError (msg, v) -> Printf.sprintf "%s %s" msg (Lm_symbol.to_string v)
        | _ -> "other"
      in
      Printf.sprintf "RefineError %s %s" n (err e)
  in
  Printf.printf "%-42s %s\n" label line

let () =
  case "hc under lam, instance x" (at [ 1 ] hc) (lam (simple "h" [ mk_var_term x ]));
  case "hc under lam, instance g{x}" (at [ 1 ] hc) (lam (simple "h" [ simple "g" [ mk_var_term x ] ]));
  case "hc under lam, instance c (no x)" (at [ 1 ] hc) (lam (simple "h" [ simple "c" [] ]));
  case "hk under lam, instance x ('a not in cond)" (at [ 1 ] hk) (lam (simple "h" [ mk_var_term x ]));
  case "hc at the root, instance c" (at [] hc) (simple "h" [ simple "c" [] ])
