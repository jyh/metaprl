(* Tactic_boot, the parts that no unit test, theory build or proof replay
   reached after test_tactic_boot_rest (2026-11-13 rank): set_concl, the
   attribute printers for an empty and a one-element term list and for a
   false bool, prefix_thenFLT's idT case (the one that checks the list
   length), removeOptionT, and the final hooks run at the end of a
   refinement (finalT, timingT).
   Every outcome is the code's own (measured 2026-11-14).  timingT prints
   its times to stderr; they differ from run to run, so that case captures
   stderr and prints only the words of the line, with each number replaced
   by N. *)
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Tactic_boot
open Tactic_boot_sig
open Tacticals_boot.Tacticals

let at n = mk_simple_term (Opname.make_opname [ n ]) []
let print w f = let buf = Lm_rformat.new_buffer () in match f buf with () -> Lm_rformat_text.print_text_string w buf | exception e -> "raised " ^ Printexc.to_string e
let say fmt = Printf.ksprintf (fun s -> print_string s; flush stdout) fmt
let flat s = String.concat " " (List.filter (( <> ) "") (List.map String.trim (String.split_on_char '\n' s)))
let sp t = flat (Simple_print.SimplePrint.string_of_term t)
let lab s = TermOp.mk_token_term (Opname.make_opname [ "select"; "Perv" ]) (Opname.make_opname [ s ])

let base () =
  let b = TacticInternal.debug_arg Mp_resource.empty_bookmark (at "A") in
  { b with TacticInternalType.ref_goal = Refine.mk_msequent (at "A") [ at "A" ] }

let refine name tac arg =
  match TacticInternal.refine tac arg with
  | exception RefineError.RefineError (s, RefineError.StringError m) -> say "%-36s refused (%s: %s)\n" name s m; None
  | exception e -> say "%-36s raised %s\n" name (Printexc.to_string e); None
  | subgoals, ext -> say "%-36s %d subgoal(s)\n" name (List.length subgoals); Some (subgoals, ext)

let goal_of a = sp (Refine.msequent_goal a.TacticInternalType.ref_goal)
let opts a = String.concat "; " (List.map (fun (t, k) -> sp t ^ "=" ^ Options_boot.string_of_option k)
                                      (Options_boot.list_options (TacticInternal.get_options a)))

(* run f with stderr sent to a file, and give back what it wrote *)
let capture_stderr f =
  let file = Filename.temp_file "tbm" ".err" in
  flush stderr;
  let saved = Unix.dup Unix.stderr in
  let fd = Unix.openfile file [ Unix.O_WRONLY; Unix.O_TRUNC ] 0o600 in
  Unix.dup2 fd Unix.stderr; Unix.close fd;
  let restore () = flush stderr; Unix.dup2 saved Unix.stderr; Unix.close saved in
  (try f () with e -> restore (); raise e);
  restore ();
  let ic = open_in_bin file in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic; Sys.remove file; s
let shape s =
  String.concat " " (List.map (fun w -> if w <> "" && (match w.[0] with '0' .. '9' | '-' -> true | _ -> false) then "N" else w)
                       (String.split_on_char ' ' (String.trim s)))

let () =
  say "== set_concl\n";
  let s = mk_sequent_term { sequent_args = at "arg"; sequent_hyps = SeqHyp.of_list [ Hypothesis (Lm_symbol.add "x", at "H") ]; sequent_concl = at "C" } in
  let a = { (base ()) with TacticInternalType.ref_goal = Refine.mk_msequent s [ at "A" ] } in
  let a' = TacticInternal.set_concl a (at "D") in
  say "goal %s, after set_concl D: %s, assumptions kept %d\n" (goal_of a) (goal_of a')
    (List.length (snd (Refine.dest_msequent a'.TacticInternalType.ref_goal)));
  say "== attribute printers (width 100)\n";
  let show name tac =
    match TacticInternal.refine tac (base ()) with
    | exception e -> say "%s: raised %s\n" name (Printexc.to_string e)
    | _, e -> say "-- %s\n%s\n" name (print 100 (fun buf -> TacticInternal.format_extract Dform.null_base buf e)) in
  show "addTermListT e []" (TacticInternal.addTermListT "e" []);
  show "addTermListT o [T]" (TacticInternal.addTermListT "o" [ at "T" ]);
  show "addBoolT f false" (TacticInternal.addBoolT "f" false);
  say "== prefix_thenFLT\n";
  ignore (refine "idT, then [idT]" (prefix_thenFLT idT (fun _ -> [ idT ])) (base ()));
  ignore (refine "idT, then [idT; idT]" (prefix_thenFLT idT (fun _ -> [ idT; idT ])) (base ()));
  ignore (refine "idT, then []" (prefix_thenFLT idT (fun _ -> [])) (base ()));
  ignore (refine "idT, then [cutT B]" (prefix_thenFLT idT (fun _ -> [ cutT (at "B") ])) (base ()));
  ignore (refine "cutT B, then one idT per subgoal" (prefix_thenFLT (cutT (at "B")) (List.map (fun _ -> idT))) (base ()));
  ignore (refine "cutT B, then [idT]" (prefix_thenFLT (cutT (at "B")) (fun _ -> [ idT ])) (base ()));
  say "== removeOptionT\n";
  (match refine "addOptionT pa allow; pe exclude" (prefix_thenT (TacticInternal.addOptionT (lab "pa") Options_boot.OptionAllow)
                                                     (TacticInternal.addOptionT (lab "pe") Options_boot.OptionExclude)) (base ()) with
   | Some ([ a ], _) ->
       say "options [%s]\n" (opts a);
       (match refine "removeOptionT pa" (TacticInternal.removeOptionT (lab "pa")) a with
        | Some ([ b ], _) -> say "options [%s]\n" (opts b)
        | _ -> ());
       (match refine "removeOptionT pz (never set)" (TacticInternal.removeOptionT (lab "pz")) a with
        | Some ([ b ], _) -> say "options [%s]\n" (opts b)
        | _ -> ())
   | _ -> ());
  say "== finalT\n";
  ignore (refine "finalT h1 then finalT h2"
            (prefix_thenT (TacticInternal.finalT (fun () -> say "  hook h1 ran\n")) (TacticInternal.finalT (fun () -> say "  hook h2 ran\n"))) (base ()));
  ignore (refine "idT (the hooks do not run again)" idT (base ()));
  ignore (refine "finalT h3, then a refusal"
            (prefix_thenT (TacticInternal.finalT (fun () -> say "  hook h3 ran\n")) (prefix_thenFLT idT (fun _ -> []))) (base ()));
  ignore (refine "idT (after the refusal)" idT (base ()));
  say "== timingT\n";
  let err = capture_stderr (fun () -> ignore (refine "timingT (cutT B)" (TacticInternal.timingT (cutT (at "B"))) (base ()))) in
  say "stderr: %s\n" (shape err)
