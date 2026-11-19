(* Refine.create_ml_cond_rewrite (refiner/refiner/refine.ml): an ML
   conditional rewrite, APPLIED.  test_refine_debug_msgs creates one and
   never applies it, so its rewriter wrapper (the check that a subgoal
   mentions no variable bound at the rewritten position, the sentinel
   call, the extract) was reached by nothing (2026-11-18 rank737).  The
   rewriter turns k into c with the subgoals the case names, and refuses
   any other term; it is applied through crwtactic at an address in the
   conclusion of a one-clause sequent.  Each line prints the subgoals'
   conclusions or the refusal (an address refusal unwrapped to its
   cause), and the bound variables the rewriter was given.
   Read from the output: under lam x, a subgoal x is refused ("Rewrite
   condition has free variable where it is not allowed: x"), while a
   subgoal naming a variable free in the whole sequent (y), or x where
   nothing binds it, is accepted; the null sentinel refuses before the
   rewriter runs.
   The expected file is the output of the code as written (2026-11-18),
   never typed.  Mutants (2026-11-18, each rebuilt and relinked; an
   identity control unchanged): the refusal off, the bound-variable
   filter dropped, and the rewriter given no bound variables: 3 of 3 RED. *)
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.Refine

module P = Simple_print.SimplePrint
let op s = Opname.make_opname [ s; "Rmc" ]
let k = mk_simple_term (op "k") [] and c = mk_simple_term (op "c") [] and q = mk_simple_term (op "q") []
let f t = mk_simple_term (op "f") [ t ]
let lam x t = mk_term (mk_op (op "lam") []) [ mk_bterm [ Lm_symbol.add x ] t ]
let var x = mk_var_term (Lm_symbol.add x)
let seq concl = mk_sequent_term { sequent_args = mk_xlist_term []; sequent_hyps = SeqHyp.empty; sequent_concl = concl }
let addr l = TermAddr.make_address (Term_addr_sig.ClauseAddr 0 :: List.map (fun i -> Term_addr_sig.Subterm i) l)
let seen = ref []
(* k --> c, with the subgoals the case asks for; anything else is refused by the rewriter *)
let mlcrw subgoals : ml_cond_rewrite = fun bvars _ t ->
  seen := String.concat "," (List.map Lm_symbol.to_string (Lm_symbol.SymbolSet.elements bvars)) :: !seen;
  if TermSubst.alpha_equal t k then c, subgoals, (fun _ _ goal _ -> goal)
  else raise (RefineError.RefineError ("mlcrw", RefineError.StringError "not k"))

let case name sent subgoals concl path =
  let build = null_refiner ("test_refine_ml_crw_" ^ string_of_int (Hashtbl.hash name)) in
  let crw = match create_ml_cond_rewrite build "mlkc" (mlcrw subgoals) with
    | CondRW r -> r Rewrite.empty_rw_args [] | PrimRW _ -> failwith "prim" in
  let sent = match sent with `Any -> any_sentinal | `Null -> null_sentinal | `Own -> sentinal_of_refiner (refiner_of_build build) in
  seen := [];
  let r =
    match refine sent (crwtactic 0 (crwaddr (addr path) crw)) (mk_msequent (seq concl) []) with
    | sg, _ -> Printf.sprintf "%d subgoals: %s" (List.length sg) (String.concat " | " (List.map (fun m -> P.string_of_term (explode_sequent (fst (dest_msequent m))).sequent_concl) sg))
    | exception RefineError.RefineError (loc, e) ->
       let rec why = function
         | RefineError.StringVarError (m, v) -> " (" ^ m ^ ": " ^ Lm_symbol.to_string v ^ ")"
         | RefineError.StringError m -> " (" ^ m ^ ")"
         | RefineError.RewriteAddressError (_, name, e) -> " at the address, from " ^ name ^ why e
         | _ -> "" in
       "refused at " ^ loc ^ why e
  in
  Printf.printf "%-48s %s; rewriter saw bvars {%s}\n%!" name r (String.concat "; " (List.rev !seen))

let () =
  case ">- k, subgoal q" `Any [ q ] k [];
  case ">- k, no subgoals" `Any [] k [];
  case ">- f{k} at f.1, subgoal q" `Any [ q ] (f k) [ 1 ];
  case ">- lam x. k at lam.1, subgoal q" `Any [ q ] (lam "x" k) [ 1 ];
  case ">- lam x. k at lam.1, subgoal x" `Any [ var "x" ] (lam "x" k) [ 1 ];
  case ">- lam x. k at lam.1, subgoal f{y} (y free)" `Any [ f (var "y") ] (lam "x" k) [ 1 ];
  case ">- k, subgoal x (no binder)" `Any [ var "x" ] k [];
  case ">- c (the rewriter refuses)" `Any [ q ] c [];
  case ">- k under null_sentinal" `Null [ q ] k [];
  case ">- k under its refiner's sentinel" `Own [ q ] k []
