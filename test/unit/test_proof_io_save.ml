(* Proof_boot.Proof's save path (io_proof_of_proof, squashed and not)
   on one-step proofs as refined, POSTED at the root (the root is then
   Locked), and after set_goal at the root, squash at [0] and set_goal at
   [0]; plus a bare goal.  For each save it prints the io proof's status
   and node count, the status and node count of the proof reloaded from it
   (proof_of_io_proof), and of the io proof after a round trip through its
   term form (term_of_io_proof, io_proof_of_term).  The proofs are built
   without a theory (Proof.create on a debug_arg goal A with one
   assumption A); the reload's evaluator maps the step text "t" to the
   case's tactic.  The expected file is the output of the code as written,
   never typed.  Pinned as found, not changed:
     - a COMPLETE proof (nthAssumT 1) saved unsquashed reads complete as
       an io proof and incomplete once reloaded;
     - the term round trip equals the squashed save in every case (status
       and node count: 1/8 -> 1/5 for the thenLT step), so the term form
       keeps no primitive extract tree;
     - a proof posted at its root saves exactly as the unposted proof;
     - after squash at [0], idT and addIntT steps reload partial while the
       others reload incomplete.
   Not reached: status_of_io_proof on a root other than a rule box or a
   goal (every root here stays one), io_proof_of_proof's Pending arm. *)
open Refiner.Refiner
open Refiner.Refiner.Term
open Tactic_boot
open Tactic_boot_sig
open Proof_boot
open Tacticals_boot.Tacticals

let at n = mk_simple_term (Opname.make_opname [ n ]) []
let ex name = MLast.ExLid (Ploc.dummy, Ploc.VaVal name)
let id x = x
let st = function Proof.StatusBad -> "bad" | Proof.StatusIncomplete -> "incomplete" | Proof.StatusPartial -> "partial" | Proof.StatusComplete -> "complete"
let nc (a, b) = Printf.sprintf "%d/%d" a b
let try_s f = try f () with
  | RefineError.RefineError (n, _) -> "refused (" ^ n ^ ")"
  | Proof.ProofRefineError (n, _, _, _) -> "ProofRefineError (" ^ n ^ ")"
  | e -> "raised " ^ Printexc.to_string e

(* the evaluator of a reload: every step's text is "t", mapped to the case's tactic *)
let current = ref idT
let parse s = ex s
let eval = function
  | MLast.ExLid (_, Ploc.VaVal "t") -> !current
  | MLast.ExLid (_, Ploc.VaVal "idT") -> idT
  | _ -> raise (Invalid_argument "eval")

let a0 () =
  let base = TacticInternal.debug_arg Mp_resource.empty_bookmark (at "A") in
  { base with TacticInternalType.ref_goal = Refine.mk_msequent (at "A") [ at "A" ] }

let mk tac wrapped =
  let tac = if wrapped then TacticInternal.wrapT (IntArgList ("w", 7)) tac else tac in
  Proof.refine id (Proof.create (a0 ())) [] "t" (ex "t") tac

let save label p =
  List.iter (fun squash ->
      Printf.printf "    %-22s squash %-5b %s\n" label squash
        (try_s (fun () ->
             let io = Proof.io_proof_of_proof squash parse eval p in
             let r = Proof.proof_of_io_proof [] Tactic.null_sentinal Mp_resource.empty_bookmark parse eval io in
             let io2 = Proof.io_proof_of_term parse eval (Proof.term_of_io_proof parse eval io) in
               Printf.sprintf "io %s %s | reload %s %s | term round trip %s %s"
                 (st (Proof.status_of_io_proof io)) (nc (Proof.node_count_of_io_proof io))
                 (try_s (fun () -> st (Proof.status r []))) (try_s (fun () -> nc (Proof.node_count r)))
                 (st (Proof.status_of_io_proof io2)) (nc (Proof.node_count_of_io_proof io2)))))
    [ false; true ]

let () =
  Printf.printf "bare goal\n";
  save "(as created)" (Proof.create (a0 ()));
  List.iter (fun (lbl, tac, w) ->
      current := tac;
      Proof.clear_cache ();
      Printf.printf "%s\n" lbl;
      let p = mk tac w in
      Printf.printf "    %-22s status %s, nodes %s\n" "(as refined)" (st (Proof.status p [])) (nc (Proof.node_count p));
      save "as refined" p;
      save "posted at the root" (Proof.post (fun () -> mk tac w) []);
      save "set_goal B at the root" (Proof.set_goal id (mk tac w) [] (Refine.mk_msequent (at "B") []));
      save "squash at [0]" (Proof.squash id (mk tac w) [ 0 ]);
      save "set_goal B at [0]" (Proof.set_goal id (mk tac w) [ 0 ] (Refine.mk_msequent (at "B") [])))
    [ "cutT B", cutT (at "B"), false;
      "nthAssumT 1", nthAssumT 1, false;
      "idT", idT, false;
      "addIntT k 3", TacticInternal.addIntT "k" 3, false;
      "cutT B thenLT [cutT C; idT]", prefix_thenLT (cutT (at "B")) [ cutT (at "C"); idT ], false;
      "wrapped cutT B", cutT (at "B"), true ]
