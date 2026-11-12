(* term_ds against term_std on context terms and sequents: the branches of
   term_addr_ds.ml and term_subst_ds.ml that the proof census runs and no
   unit test did (2026-11-11 reach census, 45 lines): addresses into a
   context term with arguments, apply_fun_higher over a context term and a
   sequent, alpha_equal on context terms, subst that must rename a binder
   (a lambda and a sequent hypothesis), and var_subst into a context term.
   Each operation runs in both implementations on terms built separately in
   each; the results are printed with one structural printer (so the two
   lines are comparable), and "agree" or "DIFFER" beside them.  term_std
   is the model: the TERMS = both census differential is clean (2026-11-11,
   264 / 264).  The expected file is the output of the code as written
   (2026-11-11), never typed. *)
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

  let guard f = try f () with R.RefineError.RefineError (s, _) -> "refused (" ^ s ^ ")" | Failure s -> "failure (" ^ s ^ ")"
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

  let results () = [
    "term_subterm t1 [1;1]", guard (fun () -> show (R.TermAddr.term_subterm t1 (addr [ 1; 1 ])));
    "term_subterm t1 [1;2]", guard (fun () -> show (R.TermAddr.term_subterm t1 (addr [ 1; 2 ])));
    "term_subterm t1 [1;3] (the hole)", guard (fun () -> show (R.TermAddr.term_subterm t1 (addr [ 1; 3 ])));
    "term_subterm t1 [1;4]", guard (fun () -> show (R.TermAddr.term_subterm t1 (addr [ 1; 4 ])));
    "subterm_addresses t1", guard (fun () -> string_of_int (List.length (R.TermAddr.subterm_addresses t1)));
    "subterm_addresses t2", guard (fun () -> string_of_int (List.length (R.TermAddr.subterm_addresses t2)));
    "apply_fun_higher (g -> h) t1", guard (fun () ->
        let r, l = R.TermAddr.apply_fun_higher (fun t -> if is_dep0_term (op "g") t then app "h" [ one_subterm t ], 1 else raise (R.RefineError.RefineError ("x", R.RefineError.StringError "no"))) t1 in
        show r ^ " count " ^ string_of_int (List.length l));
    "apply_fun_higher (g -> h) t2", guard (fun () ->
        let r, l = R.TermAddr.apply_fun_higher (fun t -> if is_dep0_term (op "g") t then app "h" [ one_subterm t ], 1 else raise (R.RefineError.RefineError ("x", R.RefineError.StringError "no"))) t2 in
        show r ^ " count " ^ string_of_int (List.length l));
    "apply_fun_higher (nothing) t2", guard (fun () ->
        let r, l = R.TermAddr.apply_fun_higher (fun _ -> raise (R.RefineError.RefineError ("x", R.RefineError.StringError "no"))) t2 in
        show r ^ " count " ^ string_of_int (List.length l));
    "alpha_equal t3 t3' (binder renamed)", string_of_bool (R.TermSubst.alpha_equal t3 t3');
    "alpha_equal t3 (C -> D)", string_of_bool (R.TermSubst.alpha_equal t3 (lam "x" (mk_context_term (v "D") (app "g" [ var "x" ]) [ v "H" ] [ var "x" ])));
    "alpha_equal t3 (conts H -> K)", string_of_bool (R.TermSubst.alpha_equal t3 (lam "x" (mk_context_term (v "C") (app "g" [ var "x" ]) [ v "K" ] [ var "x" ])));
    (* a substitution is checked by alpha_equal against the capture-free
       answer and by its free variables: the printer reads binders with
       dest_bterm, which does not rename, so a printed result can look
       captured when it is not *)
    "subst lam y. f{x;y}, x := y", semantic (lam "y" (app "f" [ var "x"; var "y" ])) (lam "z" (app "f" [ var "y"; var "z" ]));
    "subst lam y. C[[f{x;y}]][y], x := y", semantic (lam "y" (ctx "C" (app "f" [ var "x"; var "y" ]) [ var "y" ])) (lam "z" (ctx "C" (app "f" [ var "y"; var "z" ]) [ var "z" ]));
    "subst lam y. f{x; C[[y]][]}, x := y", semantic (lam "y" (app "f" [ var "x"; ctx "C" (var "y") [] ])) (lam "z" (app "f" [ var "y"; ctx "C" (var "z") [] ]));
    "subst {y: A >- f{x;y}}, x := y", semantic (seq [ Hypothesis (v "y", c0 "A") ] (app "f" [ var "x"; var "y" ])) (seq [ Hypothesis (v "z", c0 "A") ] (app "f" [ var "y"; var "z" ]));
    "subst t1, x := c", guard (fun () -> show (R.TermSubst.subst1 t1 (v "x") (c0 "c")));
    "var_subst t1, g{x} -> z", guard (fun () -> show (R.TermSubst.var_subst t1 (app "g" [ var "x" ]) (v "z")));
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
