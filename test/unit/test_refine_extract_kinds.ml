(* Refine.term_of_extract (refiner/refiner/refine.ml) on the extract kinds
   that test_refine_extract's proofs never contain (2026-11-14 rank: its
   Identity, CutJust and MLJust arms were reached by nothing): a step by
   cut, a step by identity, and a step by an ML rule.  In a null refiner
   with the primitives
     ax  |- c               extract k
     gi  'a |- g{'a}        extract q{'x}
   and an ML rule  wr  (any goal; one subgoal c; extract w{<the subgoal's>}),
   three theorems are justified with derived_rule and their extracts read
   back with extract_term.  The model is written from the rules:
     t_cut   |- g{c}  by cut c: the lemma c by ax, then g{c} by gi with its
             subgoal c closed by the cut's assumption: q{k};
     t_id    |- c     by identity, then ax: k;
     t_ml    |- d     by wr, then ax: w{k};
     t_both  |- g{d}  by cut d (proved by wr then ax), then gi closed by the
             assumption: q{w{k}}.
   Each line prints the extract, the model and whether they agree; the
   expected file is the output of the code as written (2026-11-14). *)
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.Refine

let op s = Opname.make_opname [ s ]
let t0 s = mk_simple_term (op s) []
let t1 s a = mk_simple_term (op s) [ a ]
let sv x = mk_so_var_term (Lm_symbol.add x) [] []
let show_t t = Simple_print.SimplePrint.string_of_term t

let name = "test_refine_extract_kinds"
let build = null_refiner name
let es = Rewrite.empty_args_spec
let ra = Rewrite.empty_rw_args
let mterm subs goal = List.fold_right (fun s acc -> Term_sig.MetaImplies (Term_sig.MetaTheorem s, acc)) subs (Term_sig.MetaTheorem goal)
let opname n = Opname.mk_opname n (op name)
let prim n subs goal args ext =
  let tac = create_rule build n es [] (mterm subs goal) in
  prim_rule build n es [] (mterm subs goal) args ext; tac
let ax = prim "ax" [] (t0 "c") [] (t0 "k")
let gi = prim "gi" [ sv "a" ] (t1 "g" (sv "a")) [ sv "x" ] (t1 "q" (sv "x"))
let wr = create_ml_rule build "wr" (fun _ _ _ ->
    [ mk_msequent (t0 "c") [] ], (fun _ _ _ _ args fs -> match fs with [ f ] -> t1 "w" (f args) | _ -> t0 "bad"))

(* one sentinel per theorem, taken after its create_rule (compose refuses two) *)
let cur = ref None
let sent () = match !cur with Some s -> s | None -> failwith "no sentinel"
let goal ?(hyps = []) t = mk_msequent t hyps
let by tac g = snd (refine (sent ()) tac g)
let step tac g = refine (sent ()) tac g

(* proofs, each an extract for its goal *)
let prove_c hyps = by (ax ra []) (goal ~hyps (t0 "c"))
let prove_cut () =
  let g = goal (t1 "g" (t0 "c")) in
  let subs, e = step (cut (t0 "c")) g in
  Printf.printf "cut c on g{c}: %d subgoals: %s\n" (List.length subs)
    (String.concat " | " (List.map (fun s -> let c, hs = dest_msequent s in show_t c ^ (if hs = [] then "" else " given " ^ String.concat ", " (List.map show_t hs))) subs));
  let lemma = prove_c [] in
  let main_g = List.nth subs 1 in
  let subs2, e2 = step (gi ra []) main_g in
  let closes = List.map (fun s -> by (nth_hyp 0) s) subs2 in
  compose e [ lemma; compose e2 closes ]
let prove_id () =
  let g = goal (t0 "c") in
  compose (identity (sent ()) g) [ prove_c [] ]
let prove_ml t =
  let g = goal t in
  let subs, e = step (wr ra []) g in
  compose e (List.map (fun s -> let c, hs = dest_msequent s in ignore c; prove_c hs) subs)
let prove_both () =
  let g = goal (t1 "g" (t0 "d")) in
  let subs, e = step (cut (t0 "d")) g in
  let lemma = prove_ml (t0 "d") in
  let subs2, e2 = step (gi ra []) (List.nth subs 1) in
  compose e [ lemma; compose e2 (List.map (fun s -> by (nth_hyp 0) s) subs2) ]

let theorem n stmt prove model =
  let line = try
      ignore (create_rule build n es [] (mterm [] stmt));
      cur := Some (sentinal_of_refiner (refiner_of_build build));
      derived_rule build n es [] (mterm [] stmt) () (prove ());
      let got = show_t (extract_term (refiner_of_build build) (opname n) []) in
      Printf.sprintf "extract %s, model %s: %s" got (show_t model) (if got = show_t model then "agree" else "DIFFER")
    with Invalid_argument s -> "Invalid_argument " ^ s
       | RefineError.RefineError (s, _) -> "refused (" ^ s ^ ")" in
  Printf.printf "%-8s |- %-6s %s\n" n (show_t stmt) line

let () =
  theorem "t_cut" (t1 "g" (t0 "c")) prove_cut (t1 "q" (t0 "k"));
  theorem "t_id" (t0 "c") prove_id (t0 "k");
  theorem "t_ml" (t0 "d") (fun () -> prove_ml (t0 "d")) (t1 "w" (t0 "k"));
  theorem "t_both" (t1 "g" (t0 "d")) prove_both (t1 "q" (t1 "w" (t0 "k")))
