(* Proof_boot.Proof's edit operations at the address of a step's EXTRACT:
   child 0 of a refinement, which is the tactic's own Extract node (or the
   Identity node of idT), and 0.0 under a wrapped refinement (child 0 is
   then the Wrapped node).  test_proof_ops_nested and test_proof_ops_edit
   apply the operations at goals and rule boxes only, so the Extract,
   Identity and Wrapped arms of squash_ext, clean_extras_ext, expand_ext,
   replace_child and their neighbours were not reached.
   Each case builds a one-step proof without a theory (Proof.create on a
   debug_arg goal A with one assumption A, then Proof.refine at the root
   with cutT B, nthAssumT 1 or idT, optionally under TacticInternal.wrapT),
   applies one operation at [0] (or [0;0]), and prints the result:
   node_count, the root's status, the root's step expression and its
   number of subgoals, and the step expression at [0].  An operation that
   raises prints the exception.  The expected file is the output of the
   code as written, never typed.  Nothing here is modelled: the cases pin
   what each operation does at an extract address.  Pinned as found, not
   changed:
     - squash, make_assum and set_goal at [0] replace the tactic's Extract
       with an Unjustified node, so a COMPLETE step (nthAssumT 1) becomes
       incomplete; at [0] of idT, squash and make_assum leave the Identity;
     - set_goal at [0] of a WRAPPED step replaces the Wrapped node itself:
       the wrapper is lost (one node fewer);
     - refine, kreitz and paste at [0] put a new refinement or an open goal
       INSIDE the rule box, which keeps its own rule text (root "rule t"
       over a goal);
     - copy from [0] onto the leaf [1] makes the proof incomplete;
     - find_subgoal at [0] answers the root, [].
   Whether the proof editor ever addresses child 0 is not measured. *)
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
let rec expr = function
  | Proof.ExprGoal -> "goal" | Proof.ExprIdentity -> "identity" | Proof.ExprUnjustified -> "unjustified"
  | Proof.ExprAnnotate -> "annotate" | Proof.ExprExtract _ -> "extract"
  | Proof.ExprCompose e -> "compose(" ^ expr e ^ ")" | Proof.ExprWrapped _ -> "wrapped"
  | Proof.ExprRule (text, _) -> "rule " ^ text
let info p a = try let i = Proof.info p a in Printf.sprintf "%s/%d" (expr i.Proof.step_expr) (List.length i.Proof.step_subgoals) with RefineError.RefineError (n, _) -> "refused (" ^ n ^ ")"
let show p =
  let r, n = Proof.node_count p in
  Printf.sprintf "nodes (%d, %d), %s, root %s, [0] %s" r n (st (Proof.status p [])) (info p []) (info p [ 0 ])
let pshow p = "[" ^ String.concat ";" (List.map string_of_int p) ^ "]"

let mk tac wrapped =
  let base = TacticInternal.debug_arg Mp_resource.empty_bookmark (at "A") in
  let a0 = { base with TacticInternalType.ref_goal = Refine.mk_msequent (at "A") [ at "A" ] } in
  let tac = if wrapped then TacticInternal.wrapT (IntArgList ("w", 7)) tac else tac in
  Proof.refine id (Proof.create a0) [] "t" (ex "t") tac

let op name f =
  Printf.printf "    %-16s %s\n" name
    (try show (f ()) with
     | RefineError.RefineError (n, _) -> "refused (" ^ n ^ ")"
     | Invalid_argument s -> "Invalid_argument " ^ s
     | Failure s -> "Failure " ^ s)

let () =
  List.iter (fun (lbl, tac, w, a) ->
      Printf.printf "%s at %s\n    %-16s %s\n" lbl (pshow a) "(unchanged)" (show (mk tac w));
      op "squash" (fun () -> Proof.squash id (mk tac w) a);
      op "clean" (fun () -> Proof.clean id (mk tac w) a);
      op "kreitz" (fun () -> Proof.kreitz id (mk tac w) a);
      op "make_assum" (fun () -> Proof.make_assum id (mk tac w) a);
      op "expand" (fun () -> Proof.expand id (fun _ -> None) (mk tac w) a);
      op "refine idT" (fun () -> Proof.refine id (mk tac w) a "idT" (ex "idT") idT);
      op "refine cutT C" (fun () -> Proof.refine id (mk tac w) a "cutT C" (ex "cutT") (cutT (at "C")));
      op "copy to [1]" (fun () -> Proof.copy id (mk tac w) a [ 1 ]);
      op "copy [1] to it" (fun () -> Proof.copy id (mk tac w) [ 1 ] a);
      op "set_goal B" (fun () -> Proof.set_goal id (mk tac w) a (Refine.mk_msequent (at "B") []));
      op "paste a goal" (fun () -> Proof.paste id (mk tac w) a (Proof.create (Proof.goal (mk tac w) [])));
      Printf.printf "    %-16s %s\n" "find_subgoal 0" (try pshow (Proof.find_subgoal (mk tac w) a 0) with RefineError.RefineError (n, _) -> "refused (" ^ n ^ ")");
      Printf.printf "    %-16s %s\n" "is_leaf" (try string_of_bool (Proof.is_leaf (mk tac w) a) with RefineError.RefineError (n, _) -> "refused (" ^ n ^ ")");
      Printf.printf "    %-16s %s\n" "path_status" (try String.concat ", " (List.map st (Proof.path_status (mk tac w) a)) with RefineError.RefineError (n, _) -> "refused (" ^ n ^ ")"))
    [ "cutT B", cutT (at "B"), false, [ 0 ];
      "nthAssumT 1", nthAssumT 1, false, [ 0 ];
      "idT", idT, false, [ 0 ];
      "wrapped cutT B", cutT (at "B"), true, [ 0 ];
      "wrapped cutT B", cutT (at "B"), true, [ 0; 0 ];
      "wrapped nthAssumT 1", nthAssumT 1, true, [ 0; 0 ] ]
