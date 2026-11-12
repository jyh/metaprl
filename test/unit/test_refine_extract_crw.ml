(* The refiner's extracts and dependencies through CONDITIONAL rewrite
   steps (refiner/refiner/refine.ml): the conditional-rewrite branches of
   compute_dependencies, of the subgoal count behind a step, and of
   describe_extract, which test_refine_extract_rw (rewrites) and
   test_refine_crw (the rewrites themselves, not proofs through them)
   leave out.
   In a null refiner, on closed sequents with no hypotheses:
     sax  >- c                       extract k
     sgi  >- 'a  |-  >- g{'a}        extract q{'x}
   and conditional rewrites
     fc: f{'a; 'a} --> g{'a}  if [ c ]      gc: g{g{'a}} --> g{'a}  if [ ]
   Each theorem  >- P  is proved by ONE crwtactic step at the conclusion,
   then the primitives on every subgoal (the rewritten sequent first, then
   each condition), and justified with derived_rule.  The line prints
   describe_extract of the step, the theorem's extract (extract_term) and
   its dependencies (sorted).  Model: the extract is the extract of the
   rewritten sequent's proof (a condition's proof is not part of it); the
   dependencies are the primitives used on every subgoal plus each
   conditional rewrite named in the step.  Pinned as it reads today. *)
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.Refine

type p = C | G of p | F of p * p
let op s = Opname.make_opname [ s ]
let rec term = function
  | C -> mk_simple_term (op "c") [] | G a -> mk_simple_term (op "g") [ term a ] | F (a, b) -> mk_simple_term (op "f") [ term a; term b ]
let rec show = function C -> "c" | G a -> "g{" ^ show a ^ "}" | F (a, b) -> "f{" ^ show a ^ "; " ^ show b ^ "}"
let show_t t = Simple_print.SimplePrint.string_of_term t
let sv x = mk_so_var_term (Lm_symbol.add x) [] []
let seq concl = mk_sequent_term { sequent_args = mk_xlist_term []; sequent_hyps = SeqHyp.of_list []; sequent_concl = concl }
let rec back t =
  let { Term_sig.term_op; term_terms } = dest_term t in
  match Opname.dest_opname (dest_op term_op).Term_sig.op_name, List.map (fun b -> back (dest_bterm b).Term_sig.bterm) term_terms with
  | [ "c" ], [] -> C | [ "g" ], [ a ] -> G a | [ "f" ], [ a; b ] -> F (a, b) | _ -> failwith "back"
let concl t = back (explode_sequent t).sequent_concl

let name = "test_refine_extract_crw"
let build = null_refiner name
let es = Rewrite.empty_args_spec
let ra = Rewrite.empty_rw_args
let mterm subs goal = List.fold_right (fun s acc -> Term_sig.MetaImplies (Term_sig.MetaTheorem s, acc)) subs (Term_sig.MetaTheorem goal)
let opname n = Opname.mk_opname n (op name)
let prim n subs goal args ext =
  let tac = create_rule build n es [] (mterm subs goal) in
  prim_rule build n es [] (mterm subs goal) args ext; tac
let sax = prim "sax" [] (seq (term C)) [] (mk_simple_term (op "k") [])
let sgi = prim "sgi" [ seq (sv "a") ] (seq (mk_simple_term (op "g") [ sv "a" ])) [ sv "x" ] (mk_simple_term (op "q") [ sv "x" ])
let mkcrw n conds redex contractum =
  match create_cond_rewrite build n es [] conds redex contractum with
  | CondRW r -> prim_cond_rewrite build n [] conds redex contractum; r ra []
  | PrimRW _ -> failwith "prim"
let fc = mkcrw "fc" [ term C ] (mk_simple_term (op "f") [ sv "a"; sv "a" ]) (mk_simple_term (op "g") [ sv "a" ])
let gc = mkcrw "gc" [] (mk_simple_term (op "g") [ mk_simple_term (op "g") [ sv "a" ] ]) (mk_simple_term (op "g") [ sv "a" ])
let at_concl c = crwaddr (TermAddr.make_address [ Term_addr_sig.ClauseAddr 0 ]) c
let sub l c = crwaddr (TermAddr.make_address (List.map (fun i -> Term_addr_sig.Subterm i) l)) c

let sent () = sentinal_of_refiner (refiner_of_build build)
(* prove >- p with the primitives; None if p has an f *)
let rec prove s p =
  match p with
  | C -> Some (snd (refine s (sax ra []) (mk_msequent (seq (term C)) [])))
  | G a -> (match prove s a with
            | Some e -> let _, ext = refine s (sgi ra []) (mk_msequent (seq (term p)) []) in Some (compose ext [ e ])
            | None -> None)
  | F _ -> None
let rec model = function C -> "k" | G a -> "q{" ^ model a ^ "}" | F (a, b) -> "p{" ^ model a ^ "; " ^ model b ^ "}"
let rec uses = function C -> [ "sax" ] | G a -> "sgi" :: uses a | F _ -> []

let describe e =
  let addr a = "[" ^ TermAddr.string_of_address a ^ "]" in
  let ed (o, ints, addrs, ts) = Printf.sprintf "%s ints [%s] addrs [%s] terms [%s]" (List.hd (Opname.dest_opname o))
      (String.concat ";" (List.map string_of_int ints)) (String.concat ";" (List.map addr addrs)) (String.concat ";" (List.map show_t ts)) in
  match describe_extract e with
  | EDCondRewrite None -> "EDCondRewrite None"
  | EDCondRewrite (Some (a, at)) -> "EDCondRewrite " ^ ed a ^ " at " ^ addr at
  | EDRewrite _ -> "EDRewrite" | EDRule _ -> "EDRule" | EDComposition -> "EDComposition"
  | EDNthHyp _ -> "EDNthHyp" | EDCut _ -> "EDCut" | EDIdentity -> "EDIdentity"
let deps n = String.concat " " (List.sort_uniq compare (List.map (fun (_, o) -> List.hd (Opname.dest_opname o)) (compute_dependencies (refiner_of_build build) (opname n))))

let count = ref 0
let theorem label goal crw =
  incr count;
  let n = "thm" ^ string_of_int !count in
  let s = sent () in
  match refine s (crwtactic 0 crw) (mk_msequent (seq (term goal)) []) with
  | exception RefineError.RefineError _ -> Printf.printf "%-40s %s: the rewrite is refused\n" label (show goal)
  | subs, step ->
      let ps = List.map (fun m -> concl (msequent_goal m)) subs in
      (match List.map (prove s) ps with
       | proofs when List.for_all (fun x -> x <> None) proofs ->
           ignore (create_rule build n es [] (mterm [] (seq (term goal))) : prim_tactic);
           derived_rule build n es [] (mterm [] (seq (term goal))) () (compose step (List.map Option.get proofs));
           let ext = try show_t (extract_term (refiner_of_build build) (opname n) []) with e -> "raised " ^ Printexc.to_string e in
           Printf.printf "%-40s %s -> subgoals %s\n   step: %s\n   extract %s (model %s)\n   dependencies %s (model: the step's rewrites + %s)\n"
             label (show goal) (String.concat ", " (List.map show ps)) (describe step) ext (model (List.hd ps)) (deps n)
             (String.concat " " (List.sort_uniq compare (List.concat_map uses ps)))
       | _ -> Printf.printf "%-40s %s -> subgoals %s: not provable here\n" label (show goal) (String.concat ", " (List.map show ps)))

let () =
  theorem "fc" (F (C, C)) (at_concl fc);
  theorem "fc at [1]" (G (F (C, C))) (at_concl (sub [ 1 ] fc));
  theorem "fc candthen gc" (F (G C, G C)) (at_concl (candthenrw fc gc));
  theorem "gc corelse fc (gc fails)" (F (C, C)) (at_concl (corelserw gc fc));
  theorem "gc (no conditions)" (G (G C)) (at_concl gc);
  theorem "fc on a goal it does not match" (G C) (at_concl fc);
  theorem "fc at clause 1 (no hypothesis)" (F (C, C)) (crwaddr (TermAddr.make_address [ Term_addr_sig.ClauseAddr 1 ]) fc);
  (* the step left open inside a composition, closed by a second one: the rule
     [>- g{c}; >- c] --> >- g{f{c; c}}  by (sgi then the step), then nth_hyp on each leaf *)
  let open_case label inner crw =
    incr count;
    let n = "open" ^ string_of_int !count in
    let s = sent () in
    let goal = seq (term (G inner)) in
    let hyps = List.map (fun m -> msequent_goal m) (fst (refine s (crwtactic 0 crw) (mk_msequent (seq (term inner)) []))) in
    let _, gext = refine s (sgi ra []) (mk_msequent goal hyps) in
    let _, rext = refine s (crwtactic 0 crw) (mk_msequent (seq (term inner)) hyps) in
    let closes = List.mapi (fun i h -> snd (refine s (nth_hyp i) (mk_msequent h hyps))) hyps in
    ignore (create_rule build n es [] (mterm hyps goal) : prim_tactic);
    Printf.printf "%-40s %s\n" label
      (try derived_rule build n es [] (mterm hyps goal) () (compose (compose gext [ rext ]) closes);
         Printf.sprintf "subgoals %s; extract with 'e1.. %s; dependencies %s" (String.concat ", " (List.map (fun h -> show (concl h)) hyps))
           (show_t (extract_term (refiner_of_build build) (opname n) (List.mapi (fun i _ -> sv ("e" ^ string_of_int (i + 1))) hyps))) (deps n)
       with e -> "raised " ^ Printexc.to_string e) in
  open_case "open fc inside sgi" (F (C, C)) (at_concl fc);
  open_case "open (fc candthen gc) inside sgi" (F (G C, G C)) (at_concl (candthenrw fc gc))
