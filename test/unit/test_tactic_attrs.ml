(* Tactic_boot's attribute and option tacticals, which the proof census
   runs and no unit test did (2026-11-11 reach census: of tactic_boot.ml's
   57 census-only lines, the getters get_type / get_int / get_bool /
   get_options and the tacticals withTermListT, withTypeT, withIntT,
   withBoolT, withOptionT and addOptionT).  A recorder tactic reads every
   kind of argument under one name and the option table, and is idT; each
   case prints what it read, then the option table of the subgoal left.
   The expected file is the output of the code as written (2026-11-11),
   never typed.  Not covered here, and theory-bound: rule compilation
   (compile_rule, compile_ml_rule) and the lazy subgoal machinery. *)
open Refiner.Refiner
open Refiner.Refiner.Term
open Tactic_boot
open Tacticals_boot.Tacticals
open Sequent_boot

let op s = Opname.make_opname [ s ]
let t name = mk_simple_term (op name) []
let sp = Simple_print.SimplePrint.string_of_term
(* an option key is a label: a token term with the opname Perv!select *)
let key s = TermOp.mk_token_term (Opname.make_opname [ "select"; "Perv" ]) (Opname.make_opname [ s ])

let arg () =
  { (TacticInternal.debug_arg Mp_resource.empty_bookmark (t "A")) with
    TacticInternalType.ref_goal = Refine.mk_msequent (t "C") [] }

let opts tbl =
  "[" ^ String.concat "; " (List.map (fun (k, i) -> sp k ^ "=" ^ Options_boot.string_of_option i) (Options_boot.list_options tbl)) ^ "]"

let log = ref []
let read name = funT (fun p ->
    let o f = match f with Some x -> x | None -> "-" in
    log := Printf.sprintf "term=%s terms=%s type=%s int=%s bool=%s opts=%s"
        (o (Option.map sp (Sequent.get_term_arg p name)))
        (o (Option.map (fun l -> String.concat "," (List.map sp l)) (Sequent.get_term_list_arg p name)))
        (o (Option.map sp (Sequent.get_type_arg p name)))
        (o (Option.map string_of_int (Sequent.get_int_arg p name)))
        (o (Option.map string_of_bool (Sequent.get_bool_arg p name)))
        (opts (Sequent.get_option_args p)) :: !log;
    idT)

let run name tac =
  log := [];
  let r =
    match TacticInternal.refine tac (arg ()) with
    | gs, _ -> String.concat " | " (List.map (fun (g : TacticInternalType.tactic_arg) -> opts (TacticInternal.get_options g)) gs)
    | exception RefineError.RefineError (s, _) -> "refused (" ^ s ^ ")"
  in
  Printf.printf "%-34s read [%s]  left %s\n" name (String.concat "; " (List.rev !log)) r

let () =
  run "nothing" (read "k");
  run "withTermT k X" (withTermT "k" (t "X") (read "k"));
  run "withTermListT k [X; Y]" (withTermListT "k" [ t "X"; t "Y" ] (read "k"));
  run "withTypeT k T" (withTypeT "k" (t "T") (read "k"));
  run "withIntT k 4" (withIntT "k" 4 (read "k"));
  run "withBoolT k false" (withBoolT "k" false (read "k"));
  run "withBoolT k true, read j" (withBoolT "k" true (read "j"));
  run "withIntT k 1 (withIntT k 2)" (withIntT "k" 1 (withIntT "k" 2 (read "k")));
  run "withTermT k X (withIntT k 2)" (withTermT "k" (t "X") (withIntT "k" 2 (read "k")));
  run "withOptionT o allow" (withOptionT (key "o") Options_boot.OptionAllow (read "k"));
  run "withOptionT o exclude" (withOptionT (key "o") Options_boot.OptionExclude (read "k"));
  run "addOptionT o ignore, then read" (prefix_thenT (addOptionT (key "o") Options_boot.OptionIgnore) (read "k"));
  run "addOptionT o allow (left)" (addOptionT (key "o") Options_boot.OptionAllow);
  run "addOptionT twice, two keys" (prefix_thenT (addOptionT (key "o") Options_boot.OptionAllow) (addOptionT (key "p") Options_boot.OptionExclude));
  run "addOptionT o twice" (prefix_thenT (addOptionT (key "o") Options_boot.OptionAllow) (addOptionT (key "o") Options_boot.OptionExclude))
