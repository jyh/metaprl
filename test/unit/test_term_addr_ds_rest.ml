(* term_ds against term_std on the remaining branches of term_addr_ds.ml
   that the proof census runs and no unit test did (2026-11-11 reach
   census, 5 lines): the subterm addresses of a context term and a
   second-order variable at the top, an address that does not exist given
   to apply_fun_at_addr and replace_subterm (refused in both; in term_ds
   by getnth, before the AddressError helper fail_addr is reached), and
   apply_fun_higher over a second-order variable's arguments and over a
   context term whose arguments change while its hole does not.  Same
   harness as test_term_subst_ds_rest: both implementations, terms built
   separately in each, one printer, "agree" or "DIFFER"; term_std is the
   model.  The expected file is the output of the code as written
   (2026-11-11). *)
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
  let so name args = mk_so_var_term (v name) [] args
  let addrs t = String.concat " " (List.map R.TermAddr.string_of_address (R.TermAddr.subterm_addresses t))
  (* apply_fun_higher with f replacing c by d, counting replacements *)
  let higher t =
    let f t = if is_var_term t then raise (R.RefineError.RefineError ("f", R.RefineError.StringError "var")) else
      match dest_term t with { term_op = o; term_terms = [] } when Opname.string_of_opname (dest_op o).op_name = "c" -> c0 "d", 1
      | _ -> raise (R.RefineError.RefineError ("f", R.RefineError.StringError "no")) in
    let t', l = R.TermAddr.apply_fun_higher f t in
    show t' ^ " (" ^ string_of_int (List.length l) ^ " replaced)"
  let results () = [
    "subterm_addresses C<H>[[g{c}]][a; b]", guard (fun () -> addrs (ctxc "C" (app "g" [ c0 "c" ]) [ "H" ] [ c0 "a"; c0 "b" ]));
    "subterm_addresses 'a[c; d]", guard (fun () -> addrs (so "a" [ c0 "c"; c0 "d" ]));
    "subterm_addresses C<H>[[g]]", guard (fun () -> addrs (ctxc "C" (c0 "g") [ "H" ] []));
    "apply_fun_at_addr f{c} at [3]", guard (fun () -> show (R.TermAddr.apply_fun_at_addr (fun t -> t) (addr [ 3 ]) (app "f" [ c0 "c" ])));
    "replace_subterm f{c} at [2]", guard (fun () -> show (R.TermAddr.replace_subterm (app "f" [ c0 "c" ]) (addr [ 2 ]) (c0 "d")));
    "apply_fun_at_addr 'a[c] at [2]", guard (fun () -> show (R.TermAddr.apply_fun_at_addr (fun t -> t) (addr [ 2 ]) (so "a" [ c0 "c" ])));
    "apply_fun_higher 'a[c; e]", guard (fun () -> higher (so "a" [ c0 "c"; c0 "e" ]));
    "apply_fun_higher 'a[e; c]", guard (fun () -> higher (so "a" [ c0 "e"; c0 "c" ]));
    "apply_fun_higher 'a[e; c; e]", guard (fun () -> higher (so "a" [ c0 "e"; c0 "c"; c0 "e" ]));
    "apply_fun_higher 'a[e]", guard (fun () -> higher (so "a" [ c0 "e" ]));
    "apply_fun_higher C<H>[[e]][c]", guard (fun () -> higher (ctxc "C" (c0 "e") [ "H" ] [ c0 "c" ]));
    "apply_fun_higher C<H>[[c]][e]", guard (fun () -> higher (ctxc "C" (c0 "c") [ "H" ] [ c0 "e" ]));
    "apply_fun_higher C<H>[[c]][c]", guard (fun () -> higher (ctxc "C" (c0 "c") [ "H" ] [ c0 "c" ]));
    "apply_fun_higher C<H>[[e]][e]", guard (fun () -> higher (ctxc "C" (c0 "e") [ "H" ] [ c0 "e" ]));
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
