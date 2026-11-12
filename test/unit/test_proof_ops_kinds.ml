(* Proof_boot's proof-editor operations on the node kinds the existing
   proof tests never build: Identity, Annotate, Wrapped and nested Compose
   nodes, made by the attribute tactics (with*T, add*T), wrapT and
   composite tactics (2026-11-11 reach census: 371 of proof_boot.ml's 864
   points reached by nothing, most of them in the per-node-kind arms of
   info, squash, expand, kreitz, clean, copy/paste and the extract).
   For each proof (one refinement at the root of goal A with assumption
   A): the root's info (expression kind, goal, subgoal and extras counts),
   status and path status, node count, and the leaves; then the same
   after squash, kreitz, clean and expand at the root; copy of the root
   onto its first leaf; refiner_extract_of_proof; and format_proof at
   width 100 for the last.  The proof cache is cleared before each proof.
   Pinned as it reads today, including: squash turns a complete proof's
   status into "incomplete" (it drops the primitive extract the status
   was computed from), and a copy whose goal differs from the leaf's only
   in its attributes is kept as an extra rather than placed at the leaf. *)
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
let print w f = let buf = Lm_rformat.new_buffer () in match f buf with () -> Lm_rformat_text.print_text_string w buf | exception e -> "raised " ^ Printexc.to_string e

let base () =
  let b = TacticInternal.debug_arg Mp_resource.empty_bookmark (at "A") in
  { b with TacticInternalType.ref_goal = Refine.mk_msequent (at "A") [ at "A" ] }

let rec expr = function
  | Proof.ExprGoal -> "goal" | Proof.ExprIdentity -> "identity" | Proof.ExprUnjustified -> "unjustified"
  | Proof.ExprExtract _ -> "extract" | Proof.ExprCompose e -> "compose(" ^ expr e ^ ")" | Proof.ExprWrapped _ -> "wrapped"
  | Proof.ExprRule (s, _) -> "rule " ^ s | Proof.ExprAnnotate -> "annotate"

(* the leaves: addresses of open subgoals, depth first *)
let rec leaves p addr =
  if Proof.is_leaf p addr then [ addr ]
  else
    let info = Proof.info p addr in
    List.concat (List.mapi (fun i _ -> try leaves p (addr @ [ i + 1 ]) with _ -> []) info.Proof.step_subgoals)

let describe label p =
  let info = try_s (fun () -> let i = Proof.info p [] in
    Printf.sprintf "%s, goal %d, subgoals %d, extras %d" (expr i.Proof.step_expr) (List.length i.Proof.step_goal) (List.length i.Proof.step_subgoals) (List.length i.Proof.step_extras)) in
  say "   %-10s info %s | status %s | path [%s] | nodes %s | leaves %s\n" label info
    (try_s (fun () -> st (Proof.status p []))) (try_s (fun () -> String.concat " " (List.map st (Proof.path_status p []))))
    (try_s (fun () -> nc (Proof.node_count p)))
    (try_s (fun () -> String.concat " " (List.map (fun a -> "[" ^ String.concat "." (List.map string_of_int a) ^ "]") (leaves p []))))

let proof name tac =
  say "== %s\n" name;
  Proof.clear_cache ();
  match Proof.refine upd (Proof.create (base ())) [] name (ex name) tac with
  | exception e -> say "   refine raised %s\n" (Printexc.to_string e); None
  | p ->
      describe "refined" p;
      (match Proof.squash upd p [] with p' -> describe "squash" p' | exception e -> say "   squash raised %s\n" (Printexc.to_string e));
      (match Proof.kreitz upd p [] with p' -> describe "kreitz" p' | exception e -> say "   kreitz raised %s\n" (Printexc.to_string e));
      (match Proof.clean upd p [] with p' -> describe "clean" p' | exception e -> say "   clean raised %s\n" (Printexc.to_string e));
      (match Proof.expand upd (fun f -> Some (f ())) p [] with p' -> describe "expand" p' | exception e -> say "   expand raised %s\n" (Printexc.to_string e));
      (match leaves p [] with
       | l :: _ when l <> [] -> (match Proof.copy upd p [] l with p' -> describe "copy->leaf" p' | exception e -> say "   copy raised %s\n" (Printexc.to_string e))
       | _ -> ());
      say "   extract: %s\n" (try_s (fun () -> ignore (Proof.refiner_extract_of_proof p); "ok"));
      Some p

let () =
  let b = at "B" in
  ignore (proof "idT" idT);
  ignore (proof "nthAssumT 1" (nthAssumT 1));
  ignore (proof "cutT B" (cutT b));
  ignore (proof "addIntT k 3" (TacticInternal.addIntT "k" 3));
  ignore (proof "wrapT (cutT B)" (TacticInternal.wrapT (IntArgList ("w", 7)) (cutT b)));
  ignore (proof "cutT B thenLT [idT; nthAssumT 1]" (prefix_thenLT (cutT b) [ idT; nthAssumT 1 ]));
  ignore (proof "withTermT w C (cutT B)" (TacticInternal.withTermT "w" (at "C") (cutT b)));
  ignore (proof "addIntT k 3 thenT cutT B" (prefix_thenT (TacticInternal.addIntT "k" 3) (cutT b)));
  let squashed name tac = match Proof.refine upd (Proof.create (base ())) [] name (ex name) tac with
    | p -> say "-- %s, squashed, format_proof (width 100)\n%s\n" name (print 100 (fun buf -> Proof.format_proof Dform.null_base buf (Proof.squash upd p [])))
    | exception e -> say "-- %s: raised %s\n" name (Printexc.to_string e) in
  Proof.clear_cache ();
  squashed "wrapT (cutT B)" (TacticInternal.wrapT (IntArgList ("w", 7)) (cutT b));
  Proof.clear_cache ();
  (match Proof.refine upd (Proof.create (base ())) [] "addIntT k 3" (ex "addIntT k 3") (TacticInternal.addIntT "k" 3) with
   | p -> say "-- addIntT k 3, set_goal at the root to A with assumptions A, B, format_proof (width 100)\n%s\n"
            (print 100 (fun buf -> Proof.format_proof Dform.null_base buf (Proof.set_goal upd p [] (Refine.mk_msequent (at "A") [ at "A"; b ]))))
   | exception e -> say "-- set_goal: raised %s\n" (Printexc.to_string e));
  (match proof "withIntT k 3 (cutT B thenT addIntT j 4)" (TacticInternal.withIntT "k" 3 (prefix_thenT (cutT b) (TacticInternal.addIntT "j" 4))) with
   | Some p -> say "-- format_proof (width 100)\n%s\n" (print 100 (fun buf -> Proof.format_proof Dform.null_base buf p))
   | None -> ())
