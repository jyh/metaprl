(* Proof_boot's EDITING operations on nested proofs (squash, kreitz,
   clean, make_assum, expand, set_goal), on the proof as refined and on the
   same proof reloaded through io_proof_of_proof / proof_of_io_proof,
   unsquashed and squashed.  test_proof_ops_kinds and test_proof_ops_nested
   reach these on one-step proofs or not at all.
   The proofs are test_proof_ops_nested's (two or three refinement steps).
   For each, the tree (info, status, find_subgoal at every address) is
   printed for the proof and its two reloads; then each operation is
   applied at the root, at the first inner rule node and at the first leaf
   of the proof as refined (squash and expand also on the reloads), and the
   result's node count, status, expression at that address and leaf flag
   are printed, with every node's goal (conclusion / number of
   assumptions).  The reload's parser and evaluator map a step's text to
   its tactic.  The expected file is the output of the code as written,
   never typed.  Pinned as found, not changed:
     - kreitz at a leaf turns it into an idT step (one more node);
     - make_assum and set_goal at the root make a partial proof incomplete;
       make_assum, at any address, adds one assumption to every goal in the
       proof;
     - a reloaded proof reads incomplete where the proof it was saved from
       read partial, squashed or not;
     - squashing changes the node count of the wrapT proof (2/8 -> 2/7).
   Not reached by any proof here: the arms of squash_ext, expand_ext,
   info_ext and replace_child for Identity, Annotate, Unjustified,
   Extract, Wrapped, Pending and Locked nodes, since index returns only a
   rule box or a leaf at an address of these proofs. *)
open Refiner.Refiner
open Refiner.Refiner.Term
open Tactic_boot
open Tactic_boot_sig
open Proof_boot
open Tacticals_boot.Tacticals

let at n = mk_simple_term (Opname.make_opname [ n ]) []
let ex name = MLast.ExLid (Ploc.dummy, Ploc.VaVal name)
let say fmt = Printf.ksprintf (fun s -> print_string s; flush stdout) fmt
let st = function Proof.StatusBad -> "bad" | Proof.StatusIncomplete -> "incomplete" | Proof.StatusPartial -> "partial" | Proof.StatusComplete -> "complete"
let nc (a, b) = Printf.sprintf "%d/%d" a b
let upd p = p
let try_s f = try f () with RefineError.RefineError (n, _) -> "refused (" ^ n ^ ")" | e -> "raised " ^ Printexc.to_string e
let sa a = "[" ^ String.concat "." (List.map string_of_int a) ^ "]"
let rec expr = function
  | Proof.ExprGoal -> "goal" | Proof.ExprIdentity -> "identity" | Proof.ExprUnjustified -> "unjustified"
  | Proof.ExprExtract _ -> "extract" | Proof.ExprCompose e -> "compose(" ^ expr e ^ ")" | Proof.ExprWrapped _ -> "wrapped"
  | Proof.ExprRule (s, _) -> "rule " ^ s | Proof.ExprAnnotate -> "annotate"

let base () =
  let b = TacticInternal.debug_arg Mp_resource.empty_bookmark (at "A") in
  { b with TacticInternalType.ref_goal = Refine.mk_msequent (at "A") [ at "A" ] }

let rec addresses p addr =
  if Proof.is_leaf p addr then [ addr ]
  else addr :: List.concat (List.mapi (fun i _ -> addresses p (addr @ [ i + 1 ])) (Proof.info p addr).Proof.step_subgoals)

let tree label p =
  say "  %s: nodes %s, status %s\n" label (try_s (fun () -> nc (Proof.node_count p))) (try_s (fun () -> st (Proof.status p [])));
  List.iter (fun a ->
      say "    %-8s %s\n" (sa a) (try_s (fun () ->
          let i = Proof.info p a in
          Printf.sprintf "%s | goal %d, subgoals %d, extras %d | %s%s | find_subgoal 0: %s, %s" (expr i.Proof.step_expr) (List.length i.Proof.step_goal) (List.length i.Proof.step_subgoals)
            (List.length i.Proof.step_extras) (st (Proof.status p a)) (if Proof.is_leaf p a then ", leaf" else "") (try_s (fun () -> sa (Proof.find_subgoal p a 0)))
            (String.concat " " (List.mapi (fun k _ -> try_s (fun () -> sa (Proof.find_subgoal p a (k + 1)))) i.Proof.step_subgoals)))))
    (try addresses p [] with _ -> [])

let refine p a name tac = Proof.refine upd p a name (ex name) tac


(* The parser and evaluator of a reloaded proof: a step's text is its name
   in this table *)
let tactics : (string, Proof.tactic) Hashtbl.t = Hashtbl.create 17
let parse s = ex s
let eval = function
  | MLast.ExLid (_, Ploc.VaVal s) -> (try Hashtbl.find tactics s with Not_found -> raise (Invalid_argument ("eval " ^ s)))
  | _ -> raise (Invalid_argument "eval")
let reload squash p =
  Proof.proof_of_io_proof [] Tactic.null_sentinal Mp_resource.empty_bookmark parse eval (Proof.io_proof_of_proof squash parse eval p)

(* the root, the first inner rule node and the first leaf *)
let pick p =
  let all = try addresses p [] with _ -> [] in
  let leaf a = try Proof.is_leaf p a with _ -> false in
  let first f = match List.filter f all with a :: _ -> [ a ] | [] -> [] in
    [ [] ] @ first (fun a -> a <> [] && not (leaf a)) @ first leaf

(* every node's goal: its conclusion and number of assumptions *)
let goals q =
  String.concat " " (List.map (fun a ->
      let m = (Proof.goal q a).TacticInternalType.ref_goal in
        sa a ^ ":" ^ Simple_print.SimplePrint.string_of_term (Refine.msequent_goal m) ^ "/" ^ string_of_int (Refine.msequent_num_assums m))
    (try addresses q [] with _ -> []))

let ops = [
  "squash", (fun p a -> Proof.squash upd p a);
  "kreitz", (fun p a -> Proof.kreitz upd p a);
  "clean", (fun p a -> Proof.clean upd p a);
  "make_assum", (fun p a -> Proof.make_assum upd p a);
  "expand (no extract)", (fun p a -> Proof.expand upd (fun _ -> None) p a);
  "expand (re-run)", (fun p a -> Proof.expand upd (fun f -> Some (f ())) p a);
  "set_goal B", (fun p a -> Proof.set_goal upd p a (Refine.mk_msequent (at "B") [ at "A" ]));
]

let () =
  let b = at "B" and c = at "C" in
  let steps = [
    "cutT B, then cutT C at [1]", [ [], "cutT B", cutT b; [ 1 ], "cutT C", cutT c ];
    "cutT B, then nthAssumT 1 at [2]", [ [], "cutT B", cutT b; [ 2 ], "nthAssumT 1", nthAssumT 1 ];
    "addIntT k 3, then cutT B at [1], then idT at [1.2]", [ [], "addIntT k 3", TacticInternal.addIntT "k" 3; [ 1 ], "cutT B", cutT b; [ 1; 2 ], "idT", idT ];
    "withTermT w C (cutT B), then wrapT (cutT C) at [1]", [ [], "withTermT", TacticInternal.withTermT "w" c (cutT b); [ 1 ], "wrapT", TacticInternal.wrapT (IntArgList ("w", 1)) (cutT c) ];
    "cutT B thenLT [idT; idT], then nthAssumT 1 at [2]", [ [], "thenLT", prefix_thenLT (cutT b) [ idT; idT ]; [ 2 ], "nthAssumT 1", nthAssumT 1 ];
    "cutT B thenLT [cutT C; idT]", [ [], "thenLT2", prefix_thenLT (cutT b) [ cutT c; idT ] ];
  ] in
  List.iter (fun (name, sts) ->
      say "== %s\n" name;
      Proof.clear_cache ();
      match List.fold_left (fun p (a, n, t) -> refine p a n t) (Proof.create (base ())) sts with
      | exception e -> say "  refine raised %s\n" (Printexc.to_string e)
      | p0 ->
          List.iter (fun (_, n, t) -> Hashtbl.replace tactics n t) sts;
          List.iter (fun (label, p) ->
          tree label p;
          List.iter (fun a ->
              List.iter (fun (oname, f) ->
                if label = "proof" || oname = "squash" || oname = "expand (re-run)" then
                  say "  %-20s at %-6s %s\n" oname (sa a)
                    (try_s (fun () -> let q = f p a in
                       Printf.sprintf "nodes %s, status %s, %s, leaf %b | %s" (nc (Proof.node_count q)) (st (Proof.status q []))
                         (expr (Proof.info q a).Proof.step_expr) (Proof.is_leaf q a) (try_s (fun () -> goals q)))))
                ops)
            (pick p))
            [ "proof", p0; "reloaded", (try reload false p0 with _ -> p0); "reloaded squashed", (try reload true p0 with _ -> p0) ])
    steps
