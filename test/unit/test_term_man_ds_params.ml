(* term_ds against term_std on the remaining branches of term_man_ds.ml
   that the proof census runs and no unit test did (2026-11-11 reach
   census, 8 lines): explode_term's view of each parameter kind
   (dest_match_param: numbers (Lm_num.div_num is integer division, so
   every number here is an integer), a string, a
   token, a level, a variable, and the meta-parameters, which it does
   not support), and the parameter variables param_vars_info and
   all_vars_info collect from terms carrying numbers, levels and
   meta-parameters.  Same harness as test_term_subst_ds_rest: both
   implementations, terms built separately in each, one printer, "agree"
   or "DIFFER"; term_std is the model.  The expected file is the output of
   the code as written (2026-11-11). *)
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
  let p_num n = make_param (Number (Lm_num.num_of_int n))
  let p_frac a b = make_param (Number (Lm_num.div_num (Lm_num.num_of_int a) (Lm_num.num_of_int b)))
  let p_lvl k xs = make_param (MLevel (mk_level k (List.map (fun (x, o) -> mk_level_var (v x) o) xs)))
  let pt params = mk_term (mk_op (op "p") params) []
  let mp = function
    | MatchNumber (n, i) -> "num " ^ Lm_num.string_of_num n ^ (match i with Some k -> " int " ^ string_of_int k | None -> " not int")
    | MatchString s -> "string " ^ s
    | MatchToken (_, l) -> "token " ^ String.concat "!" l
    | MatchVar x -> "var " ^ Lm_symbol.to_string x
    | MatchLevel _ -> "level"
    | MatchShape _ -> "shape" | MatchOperator _ -> "operator"
    | MatchUnsupported -> "unsupported"
  let explode t = match explode_term t with
    | MatchTerm (name, ps, _) -> String.concat "!" name ^ "[" ^ String.concat "; " (List.map mp ps) ^ "]"
    | MatchSequent _ -> "sequent"
  let vset s = "{" ^ String.concat "," (List.sort compare (List.map Lm_symbol.to_string (Lm_symbol.SymbolSet.elements s))) ^ "}"
  let vinfo m = "{" ^ String.concat ", " (List.sort compare (Lm_symbol.SymbolTable.fold (fun acc x i ->
      (Lm_symbol.to_string x ^ ":" ^ (match i with Term_man_sig.ParamVar -> "param" | FirstOrderVar -> "fo" | SecondOrderVar (a, b) -> Printf.sprintf "so%d/%d" a b
        | ContextVar (a, b) -> Printf.sprintf "ctx%d/%d" a b | SequentContextVar (a, b) -> Printf.sprintf "sctx%d/%d" a b)) :: acc) [] m)) ^ "}"
  let mixed = pt [ p_num 3; make_param (MNumber (v "n")); p_lvl 1 [ "i", 0 ]; make_param (MString (v "s")); make_param (MToken (v "t")) ]
  let results () = [
    "explode p[3]", guard (fun () -> explode (pt [ p_num 3 ]));
    "explode p[div_num 1 2]", guard (fun () -> explode (pt [ p_frac 1 2 ]));
    "explode p[div_num 4 2]", guard (fun () -> explode (pt [ p_frac 4 2 ]));
    "explode p[\"s\"; tok; level 1|i; 'x]", guard (fun () ->
        explode (pt [ make_param (String "s"); make_param (Token (Opname.make_opname [ "tok"; "M" ])); p_lvl 1 [ "i", 0 ]; make_param (Var (v "x")) ]));
    "explode p[@n; @s; @t]", guard (fun () -> explode (pt [ make_param (MNumber (v "n")); make_param (MString (v "s")); make_param (MToken (v "t")) ]));
    "param_vars_info p[3; @n; level; @s; @t]", guard (fun () -> vset (param_vars_info Lm_symbol.SymbolSet.empty mixed));
    "param_vars_info f{p[3]; p[@m]; x}", guard (fun () ->
        vset (param_vars_info Lm_symbol.SymbolSet.empty (app "f" [ pt [ p_num 3 ]; pt [ make_param (MNumber (v "m")) ]; var "x" ])));
    "all_vars_info p[3; @n; level; @s; @t]", guard (fun () -> vinfo (all_vars_info Lm_symbol.SymbolTable.empty mixed));
    "all_vars_info f{p[3]; 'a['x]; x}", guard (fun () ->
        vinfo (all_vars_info Lm_symbol.SymbolTable.empty (app "f" [ pt [ p_num 3 ]; mk_so_var_term (v "a") [] [ var "x" ]; var "x" ])));
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
