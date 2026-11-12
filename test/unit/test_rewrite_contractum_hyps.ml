(* Rewrite_build_contractum (refiner/rewrite), the hypotheses of a matched
   context rebuilt in a contractum that gives the context other arguments:
   the branches the proof census runs and no unit test did (2026-11-11
   reach census, 10 lines).  A redex <H>; x: 'A; y: 'B; <J['x; 'y]> >- 'C
   matches a target whose J holds hypotheses mentioning x and y, one of
   them itself a context with arguments; the contractum keeps H, x and y
   and re-instantiates J with new arguments, so J's hypotheses are
   rebuilt with x and y replaced (hyp_subst, subst_hyp on a Context
   hypothesis, subst_filter when an argument is kept as it was).  Each
   line prints the rewritten sequent, or the RefineError.  H is passed
   as arg_ints 2: the 1-based position of the first hypothesis after H,
   so H holds p.  The expected
   file is the output of the code as written (2026-11-11). *)
open Term_sig
open Refiner.Refiner
open TermType
open Term
open TermMan
open RefineError
open Rewrite_sig

let op s = Opname.make_opname [ s; "Bc" ]
let v = Lm_symbol.add
let app o ts = mk_term (mk_op (op o) []) (List.map (fun t -> mk_bterm [] t) ts)
let c0 o = app o []
let var x = mk_var_term (v x)
let so name conts args = mk_so_var_term (v name) (List.map v conts) args
let seq hyps concl = mk_sequent_term { sequent_args = c0 "arg"; sequent_hyps = SeqHyp.of_list hyps; sequent_concl = concl }
let sp = Simple_print.SimplePrint.string_of_term

let redex =
  seq [ Context (v "H", [], []); Hypothesis (v "x", so "A" [ "H" ] []); Hypothesis (v "y", so "B" [ "H" ] []);
        Context (v "J", [ v "H" ], [ var "x"; var "y" ]) ] (so "C" [ "H"; "J" ] [])
let contractum args =
  seq [ Context (v "H", [], []); Hypothesis (v "x", so "A" [ "H" ] []); Hypothesis (v "y", so "B" [ "H" ] []);
        Context (v "J", [ v "H" ], args) ] (so "C" [ "H"; "J" ] [])

let target =
  seq [ Hypothesis (v "p", c0 "P"); Hypothesis (v "x", c0 "A"); Hypothesis (v "y", c0 "B");
        Hypothesis (v "z", app "g" [ var "x"; var "y" ]); Context (v "K", [], [ var "y"; var "x" ]); Hypothesis (v "w", app "h" [ var "y" ]) ]
    (c0 "C")

let case args =
  let r =
    try
      let rw = Rewrite.term_rewrite Strict { spec_ints = [| v "H" |]; spec_addrs = [||] } [ redex ] [ contractum args ] in
      match Rewrite.apply_rewrite rw ({ arg_ints = [| 2 |]; arg_addrs = [||] }, Lm_symbol.SymbolSet.empty) target [] with
      | [ r ] -> sp r
      | l -> Printf.sprintf "%d results" (List.length l)
    with RefineError (s, _) -> "REFUSED: " ^ s | Invalid_argument s -> "INVALID_ARGUMENT: " ^ s
  in
  Printf.printf "== J[%s]\n%s\n" (String.concat "; " (List.map sp args)) r

let () =
  case [ var "x"; var "y" ];
  case [ var "x"; c0 "c" ];
  case [ c0 "c"; var "y" ];
  case [ c0 "c"; c0 "d" ];
  case [ var "y"; var "x" ];
  case [ app "k" [ var "x" ]; var "y" ]
