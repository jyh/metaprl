(* Sequent_boot.Sequent, the accessors every clause tactic reads its goal
   through, which no unit test named (coverage recount 11-10).  Random
   sequents (0-6 entries, each a hypothesis x_k : A_k or a context J_k,
   and 0-3 sequent arguments) are wrapped in a tactic argument, and the
   accessors are compared with a list model:
     hyp_count            every entry, contexts included
     get_pos_hyp_num i    i when i >= 0, else hyp_count + i + 1
     nth_hyp / nth_binding at that 1-based position: the hypothesis'
                          type / variable; a context there, position 0 or
                          a position past the end is refused
     all_hyps             the hypotheses' types in order, contexts skipped
     get_decl_number x    the 1-based position of the hypothesis declaring x;
                          a context's variable and an absent name are refused
     get_hyp_number A     the 1-based position of the hypothesis A; absent, refused
     args / concl         the sequent's argument list and conclusion
   The generator is a fixed linear congruential sequence, not Random. *)
open Refiner.Refiner
open Refiner.Refiner.TermType
open Tactic_boot
open Sequent_boot

let state = ref 1111
let next () = state := (!state * 1103515245 + 12345) land 0x7fffffff; !state lsr 8
let pick n = next () mod n

type e = H of int | X of int  (* H k: hypothesis x_k : A_k;  X k: context J_k *)

let op s = Opname.make_opname [ s ]
let t name = Term.mk_simple_term (op name) []
let v = Lm_symbol.add
let ty k = t (Printf.sprintf "A%d" k)
let mkseq es nargs =
  TermMan.mk_sequent_term
    { sequent_args = TermMan.mk_xlist_term (List.init nargs (fun i -> t (Printf.sprintf "arg%d" i)));
      sequent_hyps = Term.SeqHyp.of_list (List.map (function
          | H k -> Term_sig.Hypothesis (v (Printf.sprintf "x%d" k), ty k)
          | X k -> Term_sig.Context (v (Printf.sprintf "J%d" k), [], [])) es);
      sequent_concl = t "C" }
let arg goal = { TacticInternalType.ref_goal = Refine.mk_msequent goal []; ref_label = "main";
                 ref_attributes = TacticInternal.attribute_info_of_raw_attributes [];
                 ref_bookmark = Mp_resource.empty_bookmark; ref_sentinal = Tactic.null_sentinal }
let s t = Simple_print.SimplePrint.string_of_term t
let opt f = try Some (f ()) with RefineError.RefineError _ -> None

let () =
  let n = 500 and good = ref 0 and checks = ref 0 in
  for _ = 1 to n do
    let len = pick 7 and nargs = pick 4 in
    let es = List.init len (fun k -> if pick 3 = 0 then X k else H k) in
    let p = arg (mkseq es nargs) in
    let ok = ref true in
    let chk b = incr checks; if not b then ok := false in
    chk (Sequent.hyp_count p = len);
    for i = -len - 1 to len + 1 do
      let pos = if i < 0 then len + i + 1 else i in
      chk (Sequent.get_pos_hyp_num p i = pos);
      let want = if pos >= 1 && pos <= len then (match List.nth es (pos - 1) with H k -> Some k | X _ -> None) else None in
      chk (opt (fun () -> s (Sequent.nth_hyp p i)) = Option.map (fun k -> s (ty k)) want);
      chk (opt (fun () -> Lm_symbol.string_of_symbol (Sequent.nth_binding p i)) = Option.map (Printf.sprintf "x%d") want)
    done;
    chk (List.map s (Sequent.all_hyps p) = List.filter_map (function H k -> Some (s (ty k)) | X _ -> None) es);
    List.iteri (fun j e ->
        let x, h = match e with H k -> Printf.sprintf "x%d" k, Some (ty k) | X k -> Printf.sprintf "J%d" k, None in
        chk (opt (fun () -> Sequent.get_decl_number p (v x)) = (if h = None then None else Some (j + 1)));
        match h with Some h -> chk (opt (fun () -> Sequent.get_hyp_number p h) = Some (j + 1)) | None -> ()) es;
    chk (opt (fun () -> Sequent.get_decl_number p (v "absent")) = None && opt (fun () -> Sequent.get_hyp_number p (t "Absent")) = None);
    chk (List.map s (Sequent.args p) = List.init nargs (Printf.sprintf "arg%d"));
    chk (s (Sequent.concl p) = "C" && Sequent.num_assums p = 0 && Sequent.label p = "main");
    if !ok then incr good
  done;
  Printf.printf "sequents agreeing with the model on every accessor: %d/%d (%d checks)\n" !good n !checks;
  (* One sequent, printed: x : A0; J1; y : A2 >- C *)
  let p = arg (mkseq [ H 0; X 1; H 2 ] 2) in
  for i = -4 to 4 do
    Printf.printf "i=%2d pos=%d nth_hyp=%s\n" i (Sequent.get_pos_hyp_num p i)
      (match opt (fun () -> s (Sequent.nth_hyp p i)) with Some x -> x | None -> "refused")
  done;
  Printf.printf "all_hyps %s; args %s\n" (String.concat "," (List.map s (Sequent.all_hyps p))) (String.concat "," (List.map s (Sequent.args p)))
