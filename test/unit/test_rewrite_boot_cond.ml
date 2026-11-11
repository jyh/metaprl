(* Rewrite_boot.Rewrite on CONDITIONAL rewrites and the conversions no
   other unit test builds (2026-11-11 reach census: 18 lines of
   rewrite_boot.ml reached by the proof census and by no unit test):
   rewrite_of_pre_rewrite on a conditional rewrite (and on a primitive one
   given arguments), thenC / orelseC joining two conditional rewrites,
   addrLiteralC on one, rw applying one, withoutOptionC, thenTC after a
   conditional rewrite with conditions, create_ml_iform, and
   redex_and_conv_of_rw_annotation.
   Goals are sequents  <x0: h0; ...> >- concl  over f{_;_}, g{_} and the
   atoms a, b, c, run under the any-sentinel argument debug_arg; a
   conditional rewrite is put at the conclusion (clause address 0).  Each
   case prints the subgoals (label: hypotheses |- conclusion) or the
   refusal; every outcome is the code's own (measured 2026-11-11).
   Conditional rewrites:
     cung   g{'a} --> 'a        no conditions
     cswap  f{'a;'b} --> f{'b;'a}   if  'a  (one condition)
   Not covered: the debug_rewrite prints, FunConv / ChooseConv over
   conditional rewrites. *)
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.Refine
open Tactic_boot
open Rewrite_boot.Rewrite

let op s = Opname.make_opname [ s ]
let mk s ts = mk_simple_term (op s) ts
let a = mk "a" [] and b = mk "b" [] and c = mk "c" []
let g x = mk "g" [ x ]
let f x y = mk "f" [ x; y ]
let sov x = mk_so_var_term (Lm_symbol.add x) [] []
let flat s = String.concat " " (List.filter (( <> ) "") (List.map String.trim (String.split_on_char '\n' s)))
let sp t = flat (Simple_print.SimplePrint.string_of_term t)
let seq hyps concl =
  mk_sequent_term { TermType.sequent_args = mk_xlist_term [];
                    sequent_hyps = SeqHyp.of_list (List.mapi (fun k h -> Term_sig.Hypothesis (Lm_symbol.add ("x" ^ string_of_int k), h)) hyps);
                    sequent_concl = concl }
let show_seq t =
  if is_sequent_term t then
    let e = explode_sequent t in
    String.concat ", " (List.map (function Term_sig.Hypothesis (_, h) -> sp h | Term_sig.Context (v, _, _) -> "<" ^ Lm_symbol.to_string v ^ ">") (SeqHyp.to_list e.sequent_hyps))
    ^ " |- " ^ sp e.sequent_concl
  else sp t

let build = null_refiner "test_rewrite_boot_cond"
let pre name subgoals redex contractum = create_cond_rewrite build name Rewrite.empty_args_spec [] subgoals redex contractum
let cung = rewrite_of_pre_rewrite (pre "cung" [] (g (sov "a")) (sov "a")) Rewrite.empty_rw_args []
let cswap = rewrite_of_pre_rewrite (pre "cswap" [ sov "a" ] (f (sov "a") (sov "b")) (f (sov "b") (sov "a"))) Rewrite.empty_rw_args []
let ung = create_iform "ung" false (g (sov "a")) (sov "a")
(* an option key, as test_tactic_attrs makes one *)
let key s = TermOp.mk_token_term (Opname.make_opname [ "select"; "Perv" ]) (Opname.make_opname [ s ])
let concl = TermAddr.make_address [ Term_addr_sig.ClauseAddr 0 ]

let p0 = TacticInternal.debug_arg Mp_resource.empty_bookmark a
let arg goal = { p0 with TacticInternalType.ref_goal = mk_msequent goal [] }
let run tac goal =
  match TacticInternal.refine tac (arg goal) with
  | gs, _ ->
     String.concat " || " (List.map (fun (p : TacticInternalType.tactic_arg) ->
         let m, _ = dest_msequent p.ref_goal in p.ref_label ^ ": " ^ show_seq m) gs)
  | exception RefineError.RefineError (n, e) ->
     let buf = Lm_rformat.new_buffer () in
     Refine_exn.format_refine_error Dform.null_base buf n e;
     "refused (" ^ flat (Lm_rformat_text.print_text_string 200 buf) ^ ")"
  | exception e -> "EXCEPTION " ^ Printexc.to_string e
let case label tac goal = Printf.printf "%-48s on %-22s -> %s\n" label (show_seq goal) (run tac goal)
let attempt label fn = Printf.printf "%-48s %s\n" label (try fn () with Invalid_argument s -> "Invalid_argument " ^ s)

let () =
  let g1 = seq [ b ] (g (f a b)) and g2 = seq [] (f a (g c)) in
  case "rw cung" (rw cung 0 concl) g1;
  case "rw cung (no g at the conclusion)" (rw cung 0 concl) g2;
  case "rw cswap (one condition)" (rw cswap 0 concl) g2;
  case "rw (cung thenC cswap)" (rw (prefix_thenC cung cswap) 0 concl) g1;
  case "rw (cswap thenC cung) (cung fails after)" (rw (prefix_thenC cswap cung) 0 concl) g2;
  case "rw (cung orelseC cswap)" (rw (prefix_orelseC cung cswap) 0 concl) g2;
  case "rw (cswap orelseC cung)" (rw (prefix_orelseC cswap cung) 0 concl) g1;
  case "rw ((cung thenC cswap) thenC idC)" (rw (prefix_thenC (prefix_thenC cung cswap) idC) 0 concl) g1;
  case "rw (cung thenC ung)  (mixed kinds)" (rw (prefix_thenC cung ung) 0 concl) (seq [] (g (g c)));
  let at2 = TermAddr.make_address [ Term_addr_sig.ClauseAddr 0; Term_addr_sig.Subterm 2 ] in
  case "rw (addrLiteralC [concl; 2] cung)" (rw (addrLiteralC at2 cung) 0 (TermAddr.make_address [])) g2;
  case "rw (withoutOptionC opt cung)" (rw (withoutOptionC (key "opt") cung) 0 concl) g1;
  case "rw (withoutOptionC opt ung)" (rw (withoutOptionC (key "opt") ung) 0 concl) g1;
  case "rw (withOptionC opt OptionAllow cung)" (rw (withOptionC (key "opt") Options_boot.OptionAllow cung) 0 concl) g1;
  case "rw (cswap thenTC idT)" (rw (prefix_thenTC cswap TacticInternal.idT) 0 concl) g2;
  case "rw (cswap thenTC cutT c)" (rw (prefix_thenTC cswap (Tacticals_boot.Tacticals.cutT c)) 0 concl) g2;
  let ml = create_ml_iform "mlung" (fun t -> match subterms_of_term t with [ x ] when Opname.eq (opname_of_term t) (op "g") -> x | _ -> raise (RefineError.RefineError ("mlung", RefineError.StringError "not g"))) in
  case "rw (create_ml_iform mlung)" (rw ml 0 concl) g1;
  case "rw (create_ml_iform mlung) (no g)" (rw ml 0 concl) g2;
  attempt "rewrite_of_pre_rewrite PrimRW with a parameter" (fun () ->
      ignore (rewrite_of_pre_rewrite (create_rewrite build "p" (g (sov "a")) (sov "a")) Rewrite.empty_rw_args [ c ]); "accepted");
  let loc = Ploc.dummy in
  attempt "redex_and_conv_of_rw_annotation, no arguments" (fun () ->
      match redex_and_conv_of_rw_annotation "res" "q" (g (sov "a")) (sov "a") [] Rewrite.empty_args_spec [] loc
              (create_rewrite build "q" (g (sov "a")) (sov "a")) with
      | [ r, conv ] -> sp r ^ ", then " ^ run (rw conv 0 (TermAddr.make_address [])) (g (f a b))
      | l -> string_of_int (List.length l) ^ " entries");
  attempt "  with a parameter" (fun () ->
      ignore (redex_and_conv_of_rw_annotation "res" "q2" (g (sov "a")) (sov "a") [] Rewrite.empty_args_spec [ c ] loc
                (create_rewrite build "q2" (g (sov "a")) (sov "a"))); "accepted")
