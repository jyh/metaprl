(* Options_boot.rule_labels_of_opt_terms (tactics/proof), which the proof
   census reaches and no unit test did (2026-11-12 census, 3 lines): a
   rule's optional labels, read against an option table that excludes or
   allows label a.  A rule with no labels (None, or Some []) is allowed
   by default.  The expected file is the output of the code as written
   (2026-11-12), never typed. *)
open Refiner.Refiner
open Options_boot

let select_opname = Opname.make_opname [ "select"; "Perv" ]
let mk_label_term = TermOp.mk_token_term select_opname
let lab s = mk_label_term (Opname.make_opname [ s ])

let () =
  let excl_a = add_option options_empty (lab "a") OptionExclude in
  let allow_a = add_option options_empty (lab "a") OptionAllow in
  let show name opts labels =
    Printf.printf "%-34s %b\n" name (rule_labels_are_allowed opts (rule_labels_of_opt_terms labels))
  in
  show "exclude a; rule labelled a" excl_a (Some [ lab "a" ]);
  show "exclude a; rule labelled b" excl_a (Some [ lab "b" ]);
  show "exclude a; rule with no labels" excl_a None;
  show "exclude a; rule with Some []" excl_a (Some []);
  show "allow a; rule labelled a" allow_a (Some [ lab "a" ]);
  show "allow a; rule with no labels" allow_a None;
  show "allow a; rule labelled a and b" allow_a (Some [ lab "a"; lab "b" ])
