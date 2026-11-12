(* term_ds against term_std on the remaining branches of term_subst_ds.ml
   that the proof census runs and no unit test did (2026-11-11 reach
   census, 16 lines, with every open test PR): renaming a binder list that
   repeats a variable or that clashes with the substituted term
   (compute_renames), alpha_equal on binders that are renamed back and
   forth (remove_var, eq_filt_vars) and on binder lists of different
   lengths (join_vars' Failure), alpha_equal_vars, var_subst into a
   sequent whose hypothesis binds a free variable of the substituted term,
   alpha_equal of second-order contexts, and match_terms failing.  The
   harness is test_term_ds_contexts': each operation runs in both
   implementations on terms built separately in each, printed with one
   printer, and "agree" or "DIFFER" beside them; term_std is the model.
   Substitution results are reported semantically (alpha_equal to the
   capture-free answer, free variables), because dest_bterm does not
   rename: a printed result can look captured when it is not.
   PINNED AS FOUND, not changed: match_terms of C<H>[[x]] against
   C<J>[[g]] (the same context, different context lists) binds x := g and
   H := J in term_std and is refused in term_ds, which requires equal
   context lists.  The TERMS = both census differential is clean, so the
   census never meets this shape.
   The expected file is the output of the code as written (2026-11-11). *)
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

  let show_subst l = String.concat ", " (List.map (fun (x, t) -> Lm_symbol.to_string x ^ " := " ^ show t) l)
  let lam2 x y t = mk_term (mk_op (op "lam2") []) [ mk_bterm [ v x; v y ] t ]
  let b = R.TermSubst.alpha_equal
  let sb x = string_of_bool x
  let ctxc name hole conts args = mk_context_term (v name) hole (List.map v conts) args
  (* subst1 t z s, compared with the capture-free answer; and var_subst t
     t' z, whose result is reported by its free variables and by whether
     substituting t' back for z gives t again (alpha_equal) *)
  let fvs r = String.concat "," (List.sort compare (List.map Lm_symbol.to_string (R.TermSubst.free_vars_list r)))
  let fsem t s want =
    let r = R.TermSubst.subst1 t (v "z") s in
    Printf.sprintf "alpha_equal to the capture-free answer %b, free vars [%s]" (R.TermSubst.alpha_equal r want) (fvs r)
  let vsem t t' =
    let r = R.TermSubst.var_subst t t' (v "z") in
    Printf.sprintf "free vars [%s], substituting back gives t %b" (fvs r) (R.TermSubst.alpha_equal (R.TermSubst.subst1 r (v "z") t') t)
  let results () = [
    "subst lam2 x x. g{x;z} [y/z]", guard (fun () -> fsem (lam2 "x" "x" (app "g" [ var "x"; var "z" ])) (var "y") (lam2 "u" "u" (app "g" [ var "u"; var "y" ])));
    "subst lam2 x y. g{x;y;z} [x/z] (clash)", guard (fun () -> fsem (lam2 "x" "y" (app "g" [ var "x"; var "y"; var "z" ])) (var "x") (lam2 "u" "w" (app "g" [ var "u"; var "w"; var "x" ])));
    "subst lam2 x x. g{x;z} [x/z] (repeat+clash)", guard (fun () -> fsem (lam2 "x" "x" (app "g" [ var "x"; var "z" ])) (var "x") (lam2 "u" "u" (app "g" [ var "u"; var "x" ])));
    "alpha lam2 x y. g{x;y} = lam2 y x. g{y;x}", guard (fun () -> sb (b (lam2 "x" "y" (app "g" [ var "x"; var "y" ])) (lam2 "y" "x" (app "g" [ var "y"; var "x" ]))));
    "alpha lam2 x y. g{x;y} = lam2 y x. g{x;y}", guard (fun () -> sb (b (lam2 "x" "y" (app "g" [ var "x"; var "y" ])) (lam2 "y" "x" (app "g" [ var "x"; var "y" ]))));
    "alpha lam x. lam y. g{x;y} = lam y. lam x. g{y;x}", guard (fun () -> sb (b (lam "x" (lam "y" (app "g" [ var "x"; var "y" ]))) (lam "y" (lam "x" (app "g" [ var "y"; var "x" ])))));
    "alpha lam x. lam x. x = lam y. lam x. x", guard (fun () -> sb (b (lam "x" (lam "x" (var "x"))) (lam "y" (lam "x" (var "x")))));
    "alpha lam x. lam x. x = lam y. lam x. y", guard (fun () -> sb (b (lam "x" (lam "x" (var "x"))) (lam "y" (lam "x" (var "y")))));
    "alpha lam x. g{lam y. x; y} = lam y. g{lam y. y; y}", guard (fun () -> sb (b (lam "x" (app "g" [ lam "y" (var "x"); var "y" ])) (lam "y" (app "g" [ lam "y" (var "y"); var "y" ]))));
    (* a third binder that repeats the FIRST name, under two renamed ones: remove_var finds
       the pair below the head and rebuilds the list; eq_filt_vars filters two pairs *)
    "alpha lam x. lam y. lam x. g{x;y} = lam a. lam b. lam x. g{x;b}", guard (fun () ->
        sb (b (lam "x" (lam "y" (lam "x" (app "g" [ var "x"; var "y" ])))) (lam "a" (lam "b" (lam "x" (app "g" [ var "x"; var "b" ]))))));
    "alpha lam x. lam y. lam x. g{x;y} = lam a. lam b. lam x. g{a;b}", guard (fun () ->
        sb (b (lam "x" (lam "y" (lam "x" (app "g" [ var "x"; var "y" ])))) (lam "a" (lam "b" (lam "x" (app "g" [ var "a"; var "b" ]))))));
    "is_some_var_free [] g{x}", guard (fun () -> sb (R.TermSubst.is_some_var_free [] (app "g" [ var "x" ])));
    "is_some_var_free [y; x] g{x}", guard (fun () -> sb (R.TermSubst.is_some_var_free [ v "y"; v "x" ] (app "g" [ var "x" ])));
    "alpha f{x. a} = f{x,y. a} (binder lengths)", guard (fun () -> sb (b (mk_term (mk_op (op "f") []) [ mk_bterm [ v "x" ] (c0 "a") ]) (mk_term (mk_op (op "f") []) [ mk_bterm [ v "x"; v "y" ] (c0 "a") ])));
    "alpha_equal_vars g{x} x / g{y} y", guard (fun () -> sb (R.TermSubst.alpha_equal_vars (app "g" [ var "x" ]) [ v "x" ] (app "g" [ var "y" ]) [ v "y" ]));
    "alpha_equal_vars g{x} x / g{y} y,z (lengths)", guard (fun () -> sb (R.TermSubst.alpha_equal_vars (app "g" [ var "x" ]) [ v "x" ] (app "g" [ var "y" ]) [ v "y"; v "z" ]));
    "var_subst g{y} by z in {y: A >- h{g{y}}}", guard (fun () ->
        vsem (seq [ Hypothesis (v "y", c0 "A") ] (app "h" [ app "g" [ var "y" ] ])) (app "g" [ var "y" ]));
    "var_subst g{y} by z in {y: g{y} >- g{y}}", guard (fun () ->
        vsem (seq [ Hypothesis (v "y", app "g" [ var "y" ]) ] (app "g" [ var "y" ])) (app "g" [ var "y" ]));
    "var_subst g{y} by z in {x: g{y}; y: A >- g{y}}", guard (fun () ->
        vsem (seq [ Hypothesis (v "x", app "g" [ var "y" ]); Hypothesis (v "y", c0 "A") ] (app "g" [ var "y" ])) (app "g" [ var "y" ]));
    "alpha C<H>[[x]][a] = C<H>[[x]][a]", guard (fun () -> sb (b (ctxc "C" (var "x") [ "H" ] [ c0 "a" ]) (ctxc "C" (var "x") [ "H" ] [ c0 "a" ])));
    "alpha C<H>[[x]][a] = C<J>[[x]][a]", guard (fun () -> sb (b (ctxc "C" (var "x") [ "H" ] [ c0 "a" ]) (ctxc "C" (var "x") [ "J" ] [ c0 "a" ])));
    "alpha C<H>[[C]][a] = C<H>[[C]][b]", guard (fun () -> sb (b (ctxc "C" (var "C") [ "H" ] [ c0 "a" ]) (ctxc "C" (var "C") [ "H" ] [ c0 "b" ])));
    "alpha C<H>[[g]] = D<H>[[g]]", guard (fun () -> sb (b (ctxc "C" (c0 "g") [ "H" ] []) (ctxc "D" (c0 "g") [ "H" ] [])));
    "alpha lam x. C<H>[[x]][x] = lam y. C<H>[[y]][y]", guard (fun () -> sb (b (lam "x" (ctxc "C" (var "x") [ "H" ] [ var "x" ])) (lam "y" (ctxc "C" (var "y") [ "H" ] [ var "y" ]))));
    "alpha {x: A; y: g{x} >- f{x;y}} = {u: A; w: g{u} >- f{u;w}}", guard (fun () ->
        sb (b (seq [ Hypothesis (v "x", c0 "A"); Hypothesis (v "y", app "g" [ var "x" ]) ] (app "f" [ var "x"; var "y" ]))
              (seq [ Hypothesis (v "u", c0 "A"); Hypothesis (v "w", app "g" [ var "u" ]) ] (app "f" [ var "u"; var "w" ]))));
    "alpha {x: A; <K>; y: x >- y} = {u: A; <K>; y: u >- y}", guard (fun () ->
        sb (b (seq [ Hypothesis (v "x", c0 "A"); Context (v "K", [], []); Hypothesis (v "y", var "x") ] (var "y"))
              (seq [ Hypothesis (v "u", c0 "A"); Context (v "K", [], []); Hypothesis (v "y", var "u") ] (var "y"))));
    "alpha lam C. C<H>[[C]][C] = lam D. C<H>[[D]][D]", guard (fun () ->
        sb (b (lam "C" (ctxc "C" (var "C") [ "H" ] [ var "C" ])) (lam "D" (ctxc "C" (var "D") [ "H" ] [ var "D" ]))));
    "alpha lam C. C<H>[[C]] = lam D. C<H>[[C]]", guard (fun () ->
        sb (b (lam "C" (ctxc "C" (var "C") [ "H" ] [])) (lam "D" (ctxc "C" (var "C") [ "H" ] []))));
    "alpha lam x. lam y. C<H>[[g{x;y}]] = lam y. lam x. C<H>[[g{y;x}]]", guard (fun () ->
        sb (b (lam "x" (lam "y" (ctxc "C" (app "g" [ var "x"; var "y" ]) [ "H" ] []))) (lam "y" (lam "x" (ctxc "C" (app "g" [ var "y"; var "x" ]) [ "H" ] [])))));
    "var_subst h{y} by z in lam2 y w. g{h{y}; w}", guard (fun () -> vsem (lam2 "y" "w" (app "g" [ app "h" [ var "y" ]; var "w" ])) (app "h" [ var "y" ]));
    "var_subst h{y} by z in lam3 y w u. g{h{y}; w; u}", guard (fun () ->
        vsem (mk_term (mk_op (op "lam3") []) [ mk_bterm [ v "y"; v "w"; v "u" ] (app "g" [ app "h" [ var "y" ]; var "w"; var "u" ]) ]) (app "h" [ var "y" ]));
    "var_subst h{y} by z in lam2 w y. g{h{y}; w}", guard (fun () -> vsem (lam2 "w" "y" (app "g" [ app "h" [ var "y" ]; var "w" ])) (app "h" [ var "y" ]));
    "var_subst h{y} by z in lam2 y y. g{h{y}}", guard (fun () -> vsem (lam2 "y" "y" (app "g" [ app "h" [ var "y" ] ])) (app "h" [ var "y" ]));
    "alpha_equal_fun C<H>[[z]] / C<H>[[a]] (z ~ a)", guard (fun () ->
        sb (R.TermSubst.alpha_equal_fun R.TermSubst.alpha_equal (ctxc "C" (var "z") [ "H" ] []) [ v "z" ] (ctxc "C" (c0 "a") [ "H" ] []) [ c0 "a" ]));
    "alpha_equal_fun C<H>[[z]][z] / C<H>[[a]][a] (z ~ a)", guard (fun () ->
        sb (R.TermSubst.alpha_equal_fun R.TermSubst.alpha_equal (ctxc "C" (var "z") [ "H" ] [ var "z" ]) [ v "z" ] (ctxc "C" (c0 "a") [ "H" ] [ c0 "a" ]) [ c0 "a" ]));
    "alpha_equal_fun C<H>[[z]] / C<J>[[a]] (z ~ a)", guard (fun () ->
        sb (R.TermSubst.alpha_equal_fun R.TermSubst.alpha_equal (ctxc "C" (var "z") [ "H" ] []) [ v "z" ] (ctxc "C" (c0 "a") [ "J" ] []) [ c0 "a" ]));
    "alpha_equal_fun C<H>[[C]] / C<H>[[a]] (C ~ a)", guard (fun () ->
        sb (R.TermSubst.alpha_equal_fun R.TermSubst.alpha_equal (ctxc "C" (var "C") [ "H" ] []) [ v "C" ] (ctxc "C" (c0 "a") [ "H" ] []) [ c0 "a" ]));
    "match_terms f{x} with g{x}", guard (fun () -> try ignore (R.TermSubst.match_terms [] (app "f" [ var "x" ]) (app "g" [ var "x" ])); "matched" with R.RefineError.RefineError (s, _) -> "refused (" ^ s ^ ")");
    "match_terms C<H>[[x]] with C<H>[[g]]", guard (fun () -> show_subst (R.TermSubst.match_terms [] (ctxc "C" (var "x") [ "H" ] []) (ctxc "C" (c0 "g") [ "H" ] [])));
    "match_terms C<H>[[x]] with C<J>[[g]]", guard (fun () -> show_subst (R.TermSubst.match_terms [] (ctxc "C" (var "x") [ "H" ] []) (ctxc "C" (c0 "g") [ "J" ] [])));
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
