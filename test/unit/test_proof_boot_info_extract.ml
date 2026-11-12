(* Proof_boot.Proof.info at the extract under a refinement: child 0 of a
   rule box (and 0.0 under a wrapped one) is the tactic's own Extract node,
   and info describes it with make_extract_expr, from
   Refine.describe_extract.  No unit test reached that arm (coverage
   recount 11-11: info_ext's Extract arm and all of make_extract_expr).
   Each case builds a one-step proof without a theory, as in
   test_proof_boot (Proof.create on a debug_arg goal, then Proof.refine at
   the root), and prints info at the root, at child 0, and at 0.0 when the
   step is wrapped: the step's expression, its status and its number of
   subgoals.  The expressions are:
     cutT t          cutT t
     nthAssumT i     nthAssumT i, the tactic's own number (the refiner
                     counts from 0, and make_extract_expr adds 1 back)
     idT             the identity step (not an Extract)
     rw c i addr     rw <name> <address> for one rewrite at the goal (i = 0),
                     rw <name> <i> <address> at assumption i > 0: the address of rw
                     composed with addrC's or addrLiteralC's; <rewrite> for
                     a composite one (thenC, or higherC with two matches)
     a conditional   the same, with <conditional-rewrite>; a conditional
       rewrite       rewrite with parameters is rw ( <name> <params> ) addr
     a rule          its name and its arguments
   Measured and printed as fixed cases, not modelled:
     - higherC around ONE rewrite is described with the address of the rw
       (here the root), not the address where the rewrite happened:
       describe_rw passes its own address through RewriteHigher (_, [rw]);
       higherC around one CONDITIONAL rewrite is described with the address
       where it happened;  with two, child 0 is a composition;
     - cutC under rw is described as cutT, the extract being a cut;
     - info at 0.0 of an unwrapped step is refused (Proof_boot.index).
     - higherC with no match succeeds, and is described as <rewrite>;
     - rw idC makes an identity step, not an Extract, so EDIdentity is not
       reached here.
   Not reached: EDComposition (a ComposeJust extract is made only by
   refiner_extract_of_proof, and never becomes an Extract node), EDIdentity,
   and a rule with int or address arguments. *)
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.Refine
open Tactic_boot
open Tactic_boot_sig
open Proof_boot
open Tacticals_boot.Tacticals
open Rewrite_boot.Rewrite

let op s = Opname.make_opname [ s ]
let mk s ts = mk_simple_term (op s) ts
let a = mk "a" [] and b = mk "b" [] and c = mk "c" []
let g x = mk "g" [ x ]
let f x y = mk "f" [ x; y ]
let sov x = mk_so_var_term (Lm_symbol.add x) [] []
let flat s = String.concat " " (List.filter (( <> ) "") (List.map String.trim (String.split_on_char '\n' s)))
let sp t = flat (Simple_print.SimplePrint.string_of_term t)
let seq hyps concl =
  mk_sequent_term { TermType.sequent_args = mk_xlist_term [];
                    sequent_hyps = SeqHyp.of_list (List.mapi (fun k h -> Term_sig.Hypothesis (Lm_symbol.add ("x" ^ string_of_int k), h)) hyps);
                    sequent_concl = concl }

let build = null_refiner "test_proof_boot_info_extract"
let swap = create_iform "swap" false (f (sov "a") (sov "b")) (f (sov "b") (sov "a"))
let ung = create_iform "ung" false (g (sov "a")) (sov "a")
let pre name params subgoals redex contractum = create_cond_rewrite build name Rewrite.empty_args_spec params subgoals redex contractum
let cung = rewrite_of_pre_rewrite (pre "cung" [] [] (g (sov "a")) (sov "a")) Rewrite.empty_rw_args []
let cswap = rewrite_of_pre_rewrite (pre "cswap" [] [ sov "a" ] (f (sov "a") (sov "b")) (f (sov "b") (sov "a"))) Rewrite.empty_rw_args []
let cpar = rewrite_of_pre_rewrite (pre "cpar" [ sov "t" ] [] (g (sov "a")) (sov "a")) Rewrite.empty_rw_args [ c ]
let axiom name goal =
  let mt = Term_sig.MetaTheorem goal in
  let tac = create_rule build name Rewrite.empty_args_spec [] mt in
  prim_rule build name Rewrite.empty_args_spec [] mt [] c;
  Tactic.tactic_of_rule (Tactic.compile_rule build [] tac) Rewrite.empty_rw_args []

let addr p = TermAddr.make_address (List.map (fun i -> Term_addr_sig.Subterm i) p)
let concl = TermAddr.make_address [ Term_addr_sig.ClauseAddr 0 ]
let concl2 = TermAddr.make_address [ Term_addr_sig.ClauseAddr 0; Term_addr_sig.Subterm 2 ]
let ex name = MLast.ExLid (Ploc.dummy, Ploc.VaVal name)
let att = function
  | TermArg t -> "term " ^ sp t | TypeArg t -> "type " ^ sp t | IntArg i -> "int " ^ string_of_int i
  | AddrArg x -> "addr " ^ TermAddr.string_of_address x | BoolArg x -> "bool " ^ string_of_bool x
  | StringArg x -> "\"" ^ x ^ "\"" | TermListArg l -> "terms [" ^ String.concat "; " (List.map sp l) ^ "]"
let args al = String.concat ", " (List.map att (Tactic.expand_arglist al))
let expr = function
  | Proof.ExprGoal -> "goal" | Proof.ExprIdentity -> "identity" | Proof.ExprUnjustified -> "unjustified"
  | Proof.ExprAnnotate -> "annotate" | Proof.ExprExtract al -> "extract (" ^ args al ^ ")"
  | Proof.ExprCompose _ -> "compose" | Proof.ExprWrapped al -> "wrapped (" ^ args al ^ ")"
  | Proof.ExprRule (text, _) -> "rule " ^ text
let st = function Proof.StatusBad -> "bad" | Proof.StatusIncomplete -> "incomplete" | Proof.StatusPartial -> "partial" | Proof.StatusComplete -> "complete"
let pshow p = "[" ^ String.concat ";" (List.map string_of_int p) ^ "]"
let info p at =
  match Proof.info p at with
  | exception RefineError.RefineError (n, _) -> "refused (" ^ n ^ ")"
  | i -> Printf.sprintf "%s, %s, %d subgoal(s)" (expr i.Proof.step_expr) (st i.Proof.step_status) (List.length i.Proof.step_subgoals)

let case label goal hyps tac ats =
  let base = TacticInternal.debug_arg Mp_resource.empty_bookmark a in
  let a0 = { base with TacticInternalType.ref_goal = mk_msequent goal hyps } in
  match Proof.refine (fun x -> x) (Proof.create a0) [] label (ex label) tac with
  | exception RefineError.RefineError (n, _) -> Printf.printf "%s on %s: refused (%s)\n" label (sp goal) n
  | p ->
     Printf.printf "%s on %s\n" label (sp goal);
     List.iter (fun at -> Printf.printf "  info %-6s %s\n" (pshow at) (info p at)) ats

let wrap tac = TacticInternal.wrapT (IntArgList ("wrapped", 7)) tac

let () =
  let t = f (g a) (f b c) in
  case "cutT b" a [] (cutT b) [ []; [ 0 ]; [ 0; 0 ] ];
  case "nthAssumT 2" a [ b; a ] (nthAssumT 2) [ []; [ 0 ] ];
  case "idT" a [] idT [ []; [ 0 ] ];
  case "wrapped cutT b" a [] (wrap (cutT b)) [ []; [ 0 ]; [ 0; 0 ] ];
  case "wrapped nthAssumT 1" a [ a ] (wrap (nthAssumT 1)) [ [ 0 ]; [ 0; 0 ] ];
  case "rw swap 0 []" t [] (rw swap 0 (addr [])) [ []; [ 0 ] ];
  case "rw swap 0 [2]" t [] (rw swap 0 (addr [ 2 ])) [ [ 0 ] ];
  case "rw (addrC [2] swap) 0 []" t [] (rw (addrC [ Term_addr_sig.Subterm 2 ] swap) 0 (addr [])) [ [ 0 ] ];
  case "rw (addrLiteralC [2] ung) 0 [1]" (f (f a (g b)) c) [] (rw (addrLiteralC (addr [ 2 ]) ung) 0 (addr [ 1 ])) [ [ 0 ] ];
  case "rw (addrC [2] cung) 0 concl" (seq [] (f a (g c))) [] (rw (addrC [ Term_addr_sig.Subterm 2 ] cung) 0 concl) [ [ 0 ] ];
  case "rw (higherC ung) 0 [] (one g)" t [] (rw (higherC ung) 0 (addr [])) [ [ 0 ] ];
  case "rw (higherC ung) 0 [] (two g)" (f (g a) (g b)) [] (rw (higherC ung) 0 (addr [])) [ [ 0 ] ];
  case "rw (higherC swap) 0 [] (no f)" a [] (rw (higherC swap) 0 (addr [])) [ [ 0 ] ];
  case "rw (swap thenC addrC [1] ung) 0 []" (f b (g a)) [] (rw (prefix_thenC swap (addrC [ Term_addr_sig.Subterm 1 ] ung)) 0 (addr [])) [ [ 0 ] ];
  case "rw (cutC b) 0 []" t [] (rw (cutC b) 0 (addr [])) [ [ 0 ] ];
  case "rw swap 1 []" a [ f b c ] (rw swap 1 (addr [])) [ [ 0 ] ];
  case "wrapped rw swap 0 []" t [] (wrap (rw swap 0 (addr []))) [ [ 0 ]; [ 0; 0 ] ];
  case "rw cung 0 concl" (seq [] (g (f a b))) [] (rw cung 0 concl) [ []; [ 0 ] ];
  case "rw cswap 0 concl (one condition)" (seq [] (f a (g c))) [] (rw cswap 0 concl) [ [ 0 ] ];
  case "rw cung 0 concl.2" (seq [] (f a (g c))) [] (rw cung 0 concl2) [ [ 0 ] ];
  case "rw (addrC [1] cung) 0 concl.2" (seq [] (f a (f (g c) b))) [] (rw (addrC [ Term_addr_sig.Subterm 1 ] cung) 0 concl2) [ [ 0 ] ];
  case "rw (higherC cung) 0 concl (one g)" (seq [] (f a (g c))) [] (rw (higherC cung) 0 concl) [ [ 0 ] ];
  case "rw (higherC cung) 0 concl (two g)" (seq [] (f (g a) (g c))) [] (rw (higherC cung) 0 concl) [ [ 0 ] ];
  case "rw (cung thenC cung) 0 concl" (seq [] (g (g a))) [] (rw (prefix_thenC cung cung) 0 concl) [ [ 0 ] ];
  case "rw cpar[c] 0 concl" (seq [] (g (f a b))) [] (rw cpar 0 concl) [ [ 0 ] ];
  case "rw cung 1 concl" a [ seq [] (g (f a b)) ] (rw cung 1 concl) [ [ 0 ] ];
  case "rw cpar[c] 1 concl" a [ seq [] (g (f a b)) ] (rw cpar 1 concl) [ [ 0 ] ];
  case "rule ax_a" a [] (axiom "ax_a" a) [ []; [ 0 ] ];
  case "rule ax_a2 (goal a)" b [] (axiom "ax_a2" a) [ [ 0 ] ]
