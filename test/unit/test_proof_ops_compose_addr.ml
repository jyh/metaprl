(* Proof_boot.Proof's edit operations at the extract address of a
   COMPOSED step (cutT B thenLT [...]: its extract is a Compose node) and
   of an ANNOTATED step (addIntT: its extract is an Annotate node), at
   child 0, inside the Compose (0.0, 0.1) and under wrapT (0.0).
   test_proof_ops_extract_addr reaches child 0 of cutT, nthAssumT and idT
   steps only, so info_ext's Compose and Annotate arms, among others, were
   not reached by the unit tests or the theory build.  The cases and the printed fields are that test's,
   plus the step expression at the address itself.  The expected file is
   the output of the code as written, never typed.  Pinned as found, not
   changed:
     - cutT B thenLT [idT; idT] has a plain Extract at 0 (no Compose), so
       0.0 and 0.1 are refused;
     - at 0 of a Compose, squash and make_assum keep the Compose over an
       Unjustified goal, while set_goal replaces the whole Compose with an
       Unjustified node (8 nodes -> 5);
     - inside a Compose (0.1) refine and kreitz are refused with the
       proof's own ProofRefineError ("replace" at [0]), not RefineError;
       set_goal, paste, and copy of [1] onto it replace the node with a
       goal;
     - squash and make_assum leave an Annotate node unchanged (the step
       stays partial), where they turn an Extract into Unjustified.
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
let show_at a p =
  let r, n = Proof.node_count p in
  Printf.sprintf "nodes (%d, %d), %s, root %s, [0] %s, at %s %s" r n (st (Proof.status p [])) (info p []) (info p [ 0 ])
    ("[" ^ String.concat ";" (List.map string_of_int a) ^ "]") (info p a)
let pshow p = "[" ^ String.concat ";" (List.map string_of_int p) ^ "]"

let show = ref (show_at [])
let mk tac wrapped =
  let base = TacticInternal.debug_arg Mp_resource.empty_bookmark (at "A") in
  let a0 = { base with TacticInternalType.ref_goal = Refine.mk_msequent (at "A") [ at "A" ] } in
  let tac = if wrapped then TacticInternal.wrapT (IntArgList ("w", 7)) tac else tac in
  Proof.refine id (Proof.create a0) [] "t" (ex "t") tac

let op name f =
  Printf.printf "    %-16s %s\n" name
    (try !show (f ()) with
     | RefineError.RefineError (n, _) -> "refused (" ^ n ^ ")"
     | Proof.ProofRefineError (n, _, a, _) -> "ProofRefineError (" ^ n ^ " at " ^ pshow a ^ ")"
     | Invalid_argument s -> "Invalid_argument " ^ s
     | Failure s -> "Failure " ^ s)

let () =
  List.iter (fun (lbl, tac, w, a) ->
      show := show_at a;
      Printf.printf "%s at %s\n    %-16s %s\n" lbl (pshow a) "(unchanged)" (!show (mk tac w));
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
    [ "cutT B thenLT [idT; idT]", prefix_thenLT (cutT (at "B")) [ idT; idT ], false, [ 0 ];
      "cutT B thenLT [idT; idT]", prefix_thenLT (cutT (at "B")) [ idT; idT ], false, [ 0; 0 ];
      "cutT B thenLT [idT; idT]", prefix_thenLT (cutT (at "B")) [ idT; idT ], false, [ 0; 1 ];
      "cutT B thenLT [cutT C; idT]", prefix_thenLT (cutT (at "B")) [ cutT (at "C"); idT ], false, [ 0 ];
      "cutT B thenLT [cutT C; idT]", prefix_thenLT (cutT (at "B")) [ cutT (at "C"); idT ], false, [ 0; 1 ];
      "addIntT k 3", TacticInternal.addIntT "k" 3, false, [ 0 ];
      "wrapped addIntT k 3", TacticInternal.addIntT "k" 3, true, [ 0; 0 ] ]
