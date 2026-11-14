(* The branches of refiner/term_gen/term_man_gen.ml (term_std's TermMan)
   that no unit test, theory build or proof replay reached (2026-11-13
   rank of the three coverage reports), with term_ds beside it:
     - a context term C<|H|>[[t]][args] that is not a sequent hypothesis,
       in param_vars_info, context_vars_info (marked false: not a sequent
       context), so_vars_info, all_vars_info and all_vars_terms (the names
       of its contexts list count as variables);
     - every parameter kind in param_vars_info and all_vars_info: the
       meta-parameters and a Var name a variable, a parameter list and an
       object id are looked inside, an operator parameter is not, the
       rest name nothing;
     - explode_term's view of a shape, an operator parameter, a quote and
       the meta-parameters it does not support;
     - the refusals of the sequent operations reachable from a well-formed
       sequent: nth_hyp at 0, past the last hypothesis and at a context;
       nth_binding at 0 and past the end; get_decl_number of an undeclared
       variable; get_hyp_number of a type no hypothesis has.
   Same harness as test_term_man_ds_params: both implementations, terms
   built separately in each, one printer, "agree" or "DIFFER".  The
   expected file is the output of the code as written (2026-11-14). *)
open Term_sig

module Ops (R : Refiner_sig.RefinerSig) = struct
  open R.TermType
  open R.Term
  open R.TermMan
  let v = Lm_symbol.add
  let op s = Opname.make_opname [ s ]
  let app o ts = mk_term (mk_op (op o) []) (List.map (fun t -> mk_bterm [] t) ts)
  let c0 o = app o []
  let var x = mk_var_term (v x)
  let lam x t = mk_term (mk_op (op "lam") []) [ mk_bterm [ v x ] t ]
  let pt params = mk_term (mk_op (op "p") params) []
  let seq hyps concl = mk_sequent_term { sequent_args = c0 "arg"; sequent_hyps = SeqHyp.of_list hyps; sequent_concl = concl }

  let rec show t =
    if is_var_term t then Lm_symbol.to_string (dest_var t)
    else if is_so_var_term t then
      let x, cs, ts = dest_so_var t in
      Printf.sprintf "'%s<%s>[%s]" (Lm_symbol.to_string x) (String.concat "," (List.map Lm_symbol.to_string cs)) (String.concat ";" (List.map show ts))
    else if is_context_term t then
      let x, h, cs, ts = dest_context t in
      Printf.sprintf "%s<%s>[[%s]][%s]" (Lm_symbol.to_string x) (String.concat "," (List.map Lm_symbol.to_string cs)) (show h) (String.concat ";" (List.map show ts))
    else
      let { term_op = o; term_terms = bts } = dest_term t in
      let name = Opname.string_of_opname (dest_op o).op_name in
      if bts = [] then name
      else name ^ "{" ^ String.concat "; " (List.map (fun bt ->
          let { bvars = vs; bterm = b } = dest_bterm bt in
          (if vs = [] then "" else String.concat "," (List.map Lm_symbol.to_string vs) ^ ". ") ^ show b) bts) ^ "}"

  let guard f = try f () with
    | R.RefineError.RefineError (s, e) ->
        "refused (" ^ s ^ (match e with R.RefineError.StringError m -> ": " ^ m | R.RefineError.TermMatchError (_, m) -> ": " ^ m | _ -> "") ^ ")"
    | Failure s -> "failure (" ^ s ^ ")"
    | Invalid_argument s -> "refused (Invalid_argument " ^ s ^ ")"
    | Not_found -> "Not_found"
  let vset s = "{" ^ String.concat "," (List.sort compare (List.map Lm_symbol.to_string (Lm_symbol.SymbolSet.elements s))) ^ "}"
  let tbl f m = "{" ^ String.concat ", " (List.sort compare (Lm_symbol.SymbolTable.fold (fun acc x i -> (Lm_symbol.to_string x ^ ":" ^ f i) :: acc) [] m)) ^ "}"
  let vinfo = tbl (function Term_man_sig.ParamVar -> "param" | FirstOrderVar -> "fo" | SecondOrderVar (a, b) -> Printf.sprintf "so%d/%d" a b
                   | ContextVar (a, b) -> Printf.sprintf "ctx%d/%d" a b | SequentContextVar (a, b) -> Printf.sprintf "sctx%d/%d" a b)
  let cinfo = tbl (fun (s, a, b) -> Printf.sprintf "%b/%d/%d" s a b)
  let sinfo = tbl (fun (a, b) -> Printf.sprintf "%d/%d" a b)
  let mp = function
    | MatchNumber (n, i) -> "num " ^ Lm_num.string_of_num n ^ (match i with Some k -> " int " ^ string_of_int k | None -> " not int")
    | MatchString s -> "string " ^ s
    | MatchToken (_, l) -> "token " ^ String.concat "!" l
    | MatchVar x -> "var " ^ Lm_symbol.to_string x
    | MatchLevel _ -> "level"
    | MatchShape s -> "shape " ^ Opname.string_of_opname s.shape_opname ^ "/" ^ string_of_int (List.length s.shape_params)
    | MatchOperator o -> "operator " ^ Opname.string_of_opname o.opparam_name ^ "/" ^ string_of_int (List.length o.opparam_params)
    | MatchUnsupported -> "unsupported"
  let explode t = match explode_term t with
    | MatchTerm (name, ps, _) -> String.concat "!" name ^ "[" ^ String.concat "; " (List.map mp ps) ^ "]"
    | MatchSequent _ -> "sequent"

  (* parameters *)
  let mnum x = make_param (MNumber (v x))
  let shape = make_param (Shape { shape_opname = op "sh"; shape_params = [ ShapeNumber; ShapeVar ]; shape_arities = [ 0 ] })
  let oper = make_param (Operator { opparam_name = op "o"; opparam_params = [ mnum "inop" ]; opparam_arities = [] })
  let plain = pt [ make_param (Number (Lm_num.num_of_int 3)); make_param (String "s"); make_param (Token (op "tok"));
                   shape; oper; make_param Quote ]
  let metas = pt [ make_param (Var (v "pv")); mnum "n"; make_param (MString (v "ms")); make_param (MToken (v "mt"));
                   make_param (MShape (v "msh")); make_param (MOperator (v "mo")) ]
  let lists = pt [ make_param (ObId [ mnum "oid"; make_param (String "x") ]); make_param (ParamList [ mnum "lone"; make_param (ParamList [ mnum "ltwo" ]) ]) ]
  let all_kinds = app "f" [ plain; metas; lists ]

  (* a context term that is not a hypothesis: f{ C<|H; K|>[[ g{p[@hole]; 'a['x]; x} ]][ p[@arg]; 'b[] ] } *)
  let hole = app "g" [ pt [ mnum "hole" ]; mk_so_var_term (v "a") [] [ var "x" ]; var "x" ]
  let ctxt = app "f" [ mk_context_term (v "C") hole [ v "H"; v "K" ] [ pt [ mnum "arg" ]; mk_so_var_term (v "b") [] [] ] ]
  (* nested: D<|H|>[[ E<||>[[ y ]][] ]][ z; w ] under a binder z (one context, two arguments) *)
  let nested = lam "z" (mk_context_term (v "D") (mk_context_term (v "E") (var "y") [] []) [ v "H" ] [ var "z"; c0 "w" ])

  (* x: A; <J>; y: B{x} >- C *)
  let s = seq [ Hypothesis (v "x", c0 "A"); Context (v "J", [], []); Hypothesis (v "y", app "B" [ var "x" ]) ] (c0 "C")

  let results () = [
    "param_vars_info plain params", guard (fun () -> vset (param_vars_info Lm_symbol.SymbolSet.empty plain));
    "param_vars_info meta params", guard (fun () -> vset (param_vars_info Lm_symbol.SymbolSet.empty metas));
    "param_vars_info obid/list", guard (fun () -> vset (param_vars_info Lm_symbol.SymbolSet.empty lists));
    "all_vars_info every kind", guard (fun () -> vinfo (all_vars_info Lm_symbol.SymbolTable.empty all_kinds));
    "all_vars every kind", guard (fun () -> vset (all_vars all_kinds));
    "explode plain params", guard (fun () -> explode plain);
    "explode meta params", guard (fun () -> explode metas);
    "explode obid/list", guard (fun () -> explode lists);
    "context term shown", guard (fun () -> show ctxt);
    "param_vars_info context term", guard (fun () -> vset (param_vars_info Lm_symbol.SymbolSet.empty ctxt));
    "context_vars_info context term", guard (fun () -> cinfo (context_vars_info Lm_symbol.SymbolTable.empty ctxt));
    "so_vars_info context term", guard (fun () -> sinfo (so_vars_info Lm_symbol.SymbolTable.empty ctxt));
    "all_vars_info context term", guard (fun () -> vinfo (all_vars_info Lm_symbol.SymbolTable.empty ctxt));
    "all_vars_terms [context term]", guard (fun () -> vset (all_vars_terms [ ctxt ]));
    "all_vars_terms [context; nested]", guard (fun () -> vset (all_vars_terms [ ctxt; nested ]));
    "context_vars_info nested", guard (fun () -> cinfo (context_vars_info Lm_symbol.SymbolTable.empty nested));
    "all_vars_info nested", guard (fun () -> vinfo (all_vars_info Lm_symbol.SymbolTable.empty nested));
    "context_vars nested (seq, normal)", guard (fun () -> let a, b = context_vars nested in vset a ^ " " ^ vset b);
    "all_contexts nested", guard (fun () -> vset (all_contexts nested));
    "num_hyps", guard (fun () -> string_of_int (num_hyps s));
    "nth_hyp 1", guard (fun () -> show (nth_hyp s 1));
    "nth_hyp 3", guard (fun () -> show (nth_hyp s 3));
    "nth_hyp 0", guard (fun () -> show (nth_hyp s 0));
    "nth_hyp -1", guard (fun () -> show (nth_hyp s (-1)));
    "nth_hyp 2 (a context)", guard (fun () -> show (nth_hyp s 2));
    "nth_hyp 4 (past the end)", guard (fun () -> show (nth_hyp s 4));
    "nth_binding 3", guard (fun () -> Lm_symbol.to_string (nth_binding s 3));
    "nth_binding 0", guard (fun () -> Lm_symbol.to_string (nth_binding s 0));
    "nth_binding 2 (a context)", guard (fun () -> Lm_symbol.to_string (nth_binding s 2));
    "nth_binding 4 (past the end)", guard (fun () -> Lm_symbol.to_string (nth_binding s 4));
    "get_decl_number y", guard (fun () -> string_of_int (get_decl_number s (v "y")));
    "get_decl_number J (a context)", guard (fun () -> string_of_int (get_decl_number s (v "J")));
    "get_decl_number w (undeclared)", guard (fun () -> string_of_int (get_decl_number s (v "w")));
    "get_hyp_number B{x}", guard (fun () -> string_of_int (get_hyp_number s (app "B" [ var "x" ])));
    "get_hyp_number D (no such hyp)", guard (fun () -> string_of_int (get_hyp_number s (c0 "D")));
  ]
end

module S = Ops (Refiner_std.Refiner)
module D = Ops (Refiner_ds.Refiner)

let () =
  List.iter2 (fun (name, s) (_, d) ->
      let refused x = String.length x >= 7 && String.sub x 0 7 = "refused" in
      if s = d then Printf.printf "%-36s agree  %s\n" name s
      else if refused s && refused d then Printf.printf "%-36s agree  both refused (std %s, ds %s)\n" name s d
      else Printf.printf "%-36s DIFFER std %s | ds %s\n" name s d)
    (S.results ()) (D.results ())
