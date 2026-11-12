(* term_ds against term_std on the remaining branches of term_base_ds.ml
   that the proof census runs and no unit test did (2026-11-11 reach
   census, 10 lines, with every open test PR): destructors applied to a
   term whose substitution is still pending (term_ds substitutes lazily:
   dest_var, dest_term and opname_of_term force it), the operator name of
   a context term, a substitution under a binder that shadows some of its
   variables (filter_sub_vars), a context term rebuilt by mk_term from its
   destructed form with its binder renamed (collect_context), and level
   expressions (make_level, make_level_var).  Same harness as
   test_term_subst_ds_rest: both implementations, terms built separately
   in each, one printer, "agree" or "DIFFER"; term_std is the model.  The
   expected file is the output of the code as written (2026-11-11). *)
open Term_sig

module Ops (R : Refiner_sig.RefinerSig) = struct
  open R.TermType
  open R.Term
  open R.TermMan
  open R.TermOp
  let v = Lm_symbol.add
  let op s = Opname.make_opname [ s ]
  let app o ts = mk_term (mk_op (op o) []) (List.map (fun t -> mk_bterm [] t) ts)
  let c0 o = app o []
  let var x = mk_var_term (v x)
  let lam x t = mk_term (mk_op (op "lam") []) [ mk_bterm [ v x ] t ]
  let ctx name hole args = mk_context_term (v name) hole [ v "H" ] args
  let seq hyps concl = mk_sequent_term { sequent_args = c0 "arg"; sequent_hyps = SeqHyp.of_list hyps; sequent_concl = concl }

  (* one printer for both implementations *)
  let rec show t =
    if is_var_term t then Lm_symbol.to_string (dest_var t)
    else if is_so_var_term t then
      let x, cs, ts = dest_so_var t in
      Printf.sprintf "'%s<%s>[%s]" (Lm_symbol.to_string x) (String.concat "," (List.map Lm_symbol.to_string cs)) (String.concat ";" (List.map show ts))
    else if is_context_term t then
      let x, h, cs, ts = dest_context t in
      Printf.sprintf "%s<%s>[[%s]][%s]" (Lm_symbol.to_string x) (String.concat "," (List.map Lm_symbol.to_string cs)) (show h) (String.concat ";" (List.map show ts))
    else if is_sequent_term t then
      let e = explode_sequent t in
      Printf.sprintf "{%s >- %s}"
        (String.concat "; " (List.map (function
             | Hypothesis (x, h) -> Lm_symbol.to_string x ^ ":" ^ show h
             | Context (x, cs, ts) -> Printf.sprintf "<%s<%s>[%s]>" (Lm_symbol.to_string x) (String.concat "," (List.map Lm_symbol.to_string cs)) (String.concat ";" (List.map show ts)))
             (SeqHyp.to_list e.sequent_hyps)))
        (show e.sequent_concl)
    else
      let { term_op = o; term_terms = bts } = dest_term t in
      let name = Opname.string_of_opname (dest_op o).op_name in
      if bts = [] then name
      else name ^ "{" ^ String.concat "; " (List.map (fun bt ->
          let { bvars = vs; bterm = b } = dest_bterm bt in
          (if vs = [] then "" else String.concat "," (List.map Lm_symbol.to_string vs) ^ ". ") ^ show b) bts) ^ "}"

  let guard f = try f () with R.RefineError.RefineError (s, _) -> "refused (" ^ s ^ ")" | Failure s -> "failure (" ^ s ^ ")" | Invalid_argument s -> "refused (Invalid_argument " ^ s ^ ")"
  (* subst1 t x y, compared with the capture-free answer *)
  let semantic t want =
    let r = R.TermSubst.subst1 t (v "x") (var "y") in
    Printf.sprintf "alpha_equal to the capture-free answer %b, free vars [%s]" (R.TermSubst.alpha_equal r want)
      (String.concat "," (List.map Lm_symbol.to_string (R.TermSubst.free_vars_list r)))
  let addr p = R.TermAddr.make_address (List.map (fun i -> Term_addr_sig.Subterm i) p)

  (* f{ C<H>[[g{x}]][a; b] } and a sequent with a context carrying arguments *)
  let t1 = app "f" [ ctx "C" (app "g" [ var "x" ]) [ c0 "a"; c0 "b" ] ]
  let t2 = seq [ Context (v "H", [], []); Hypothesis (v "x", c0 "A"); Context (v "J", [ v "H" ], [ var "x" ]); Hypothesis (v "y", app "g" [ var "x" ]) ]
      (app "g" [ app "f" [ var "x"; var "y" ] ])
  let t3 = lam "x" (ctx "C" (app "g" [ var "x" ]) [ var "x" ])
  let t3' = lam "z" (ctx "C" (app "g" [ var "z" ]) [ var "z" ])

  let show_subst l = String.concat ", " (List.map (fun (x, t) -> Lm_symbol.to_string x ^ " := " ^ show t) l)
  let lam2 x y t = mk_term (mk_op (op "lam2") []) [ mk_bterm [ v x; v y ] t ]
  let b = R.TermSubst.alpha_equal
  let sb x = string_of_bool x
  let ctxc name hole conts args = mk_context_term (v name) hole (List.map v conts) args
  let ctxc name hole conts args = mk_context_term (v name) hole (List.map v conts) args
  let sub1 t x s = R.TermSubst.subst1 t (v x) s
  (* the context term C<H>[[g{C}]][a] destructed, its binder renamed to D, rebuilt *)
  let rebuilt body_of =
    let t = dest_term (ctxc "C" (app "g" [ var "C" ]) [ "H" ] [ c0 "a" ]) in
    let bts = List.map (fun bt -> let { bvars = vs; bterm = b } = dest_bterm bt in
                         if vs = [] then mk_bterm [] b else mk_bterm [ v "D" ] (body_of b)) t.term_terms in
    show (mk_term t.term_op bts)
  let results () = [
    "dest_var of the body of (lam x. z)[y/z]", guard (fun () ->
        let t = sub1 (lam "x" (var "z")) "z" (var "y") in
        let bt = dest_bterm (List.hd (dest_term t).term_terms) in Lm_symbol.to_string (dest_var bt.bterm));
    "dest_term of f{z}[g{y}/z]", guard (fun () ->
        let t = sub1 (app "f" [ var "z" ]) "z" (app "g" [ var "y" ]) in
        let d = dest_term t in Opname.string_of_opname (dest_op d.term_op).op_name ^ "/" ^ string_of_int (List.length d.term_terms));
    "opname_of_term of h{z}[c/z]", guard (fun () -> Opname.string_of_opname (opname_of_term (sub1 (app "h" [ var "z" ]) "z" (c0 "c"))));
    "opname_of_term of a context", guard (fun () -> Opname.string_of_opname (opname_of_term (ctxc "C" (c0 "g") [ "H" ] [])));
    "opname_of_term of a sequent", guard (fun () -> Opname.string_of_opname (opname_of_term (seq [] (c0 "c"))));
    "subst lam z. g{z; w} [y/z; c/w]", guard (fun () -> show (R.TermSubst.subst (lam "z" (app "g" [ var "z"; var "w" ])) [ v "z"; v "w" ] [ var "y"; c0 "c" ]));
    "subst lam z. g{z; w} [c/w; y/z]", guard (fun () -> show (R.TermSubst.subst (lam "z" (app "g" [ var "z"; var "w" ])) [ v "w"; v "z" ] [ c0 "c"; var "y" ]));
    "subst lam z. g{z} [y/z; c/w]", guard (fun () -> show (R.TermSubst.subst (lam "z" (app "g" [ var "z" ])) [ v "z"; v "w" ] [ var "y"; c0 "c" ]));
    "subst lam2 z w. g{z; w; u} [y/z; c/w; d/u]", guard (fun () ->
        show (R.TermSubst.subst (mk_term (mk_op (op "lam2") []) [ mk_bterm [ v "z"; v "w" ] (app "g" [ var "z"; var "w"; var "u" ]) ])
                [ v "z"; v "w"; v "u" ] [ var "y"; c0 "c"; c0 "d" ]));
    "subst f{lam z. g{z; w}; z} [y/z; c/w]", guard (fun () ->
        show (R.TermSubst.subst (app "f" [ lam "z" (app "g" [ var "z"; var "w" ]); var "z" ]) [ v "z"; v "w" ] [ var "y"; c0 "c" ]));
    "subst f{lam z. g{z}; z} [y/z]", guard (fun () -> show (R.TermSubst.subst (app "f" [ lam "z" (app "g" [ var "z" ]); var "z" ]) [ v "z" ] [ var "y" ]));
    "subst f{lam2 z w. g{z; w; u}; z; w} [y/z; c/w; d/u]", guard (fun () ->
        show (R.TermSubst.subst (app "f" [ mk_term (mk_op (op "lam2") []) [ mk_bterm [ v "z"; v "w" ] (app "g" [ var "z"; var "w"; var "u" ]) ]; var "z"; var "w" ])
                [ v "z"; v "w"; v "u" ] [ var "y"; c0 "c"; c0 "d" ]));
    "context rebuilt, binder renamed C to D", guard (fun () -> rebuilt (fun b -> R.TermSubst.subst1 b (v "C") (var "D")));
    "context rebuilt, body unchanged (mentions C)", guard (fun () -> rebuilt (fun b -> b));
    "context rebuilt, body mentions C and D", guard (fun () -> rebuilt (fun b -> app "k" [ b; var "D" ]));
    "level 2 + i, j+1", guard (fun () ->
        let l = mk_level 2 [ mk_level_var (v "i") 0; mk_level_var (v "j") 1 ] in
        let d = dest_level l in
        string_of_int d.le_const ^ " " ^ String.concat " " (List.map (fun lv -> let x = dest_level_var lv in Lm_symbol.to_string x.le_var ^ "+" ^ string_of_int x.le_offset) d.le_vars));
    "make_level of dest_level", guard (fun () ->
        let l = mk_level 1 [ mk_level_var (v "k") 2 ] in
        let l' = make_level (dest_level l) in
        let lv' = make_level_var (dest_level_var (List.hd (dest_level l').le_vars)) in
        string_of_int (dest_level l').le_const ^ " " ^ Lm_symbol.to_string (dest_level_var lv').le_var ^ "+" ^ string_of_int (dest_level_var lv').le_offset);
  ]
end

module S = Ops (Refiner_std.Refiner)
module D = Ops (Refiner_ds.Refiner)

let () =
  List.iter2 (fun (name, s) (_, d) ->
      let refused x = String.length x >= 7 && String.sub x 0 7 = "refused" in
      if s = d then Printf.printf "%-40s agree  %s\n" name s
      else if refused s && refused d then Printf.printf "%-40s agree  both refused (std %s, ds %s)\n" name s d
      else Printf.printf "%-40s DIFFER std %s | ds %s\n" name s d)
    (S.results ()) (D.results ())
