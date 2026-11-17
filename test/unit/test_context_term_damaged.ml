(* TermMan.is_context_term and dest_context (refiner/refbase/term_man_gen.ml)
   on context terms that are not well formed, in term_std and term_ds.  A
   context <v> t [args] is the term context[v:v]{args; v. t; xlist of its
   context variables}; mk_context_term builds only well-formed ones, so
   the refusals were unvisited (2026-11-15 profile).  Each damaged term is
   built from Opname.context_opname by hand and the line prints what
   is_context_term says and what dest_context returns or raises.
   Pinned as found: term_ds refuses to BUILD a damaged context term
   (make_term: "does not look like a context"), so only term_std reaches
   the refusals; std and ds agree on the well-formed ones.
   Not reached, and why: dest_context's collect arms for no or one
   subterm; the outer match needs at least two subterms and the recursion
   stops at the last two.
   The expected file is the output of the code as written, never typed. *)
module T (R : Refiner_sig.RefinerSig) = struct
  open R.Term
  open R.TermMan
  let v = Lm_symbol.add
  let c s = mk_simple_term (Opname.make_opname [ s ]) []
  let conts l = mk_simple_bterm (mk_xlist_term (List.map (fun s -> mk_var_term (v s)) l))
  let ctx param bterms = mk_term (mk_op Opname.context_opname [ make_param param ]) bterms
  let rec exn = function
    | R.RefineError.RefineError (s, R.RefineError.TermMatchError (_, m)) -> s ^ " (" ^ m ^ ")"
    | R.RefineError.RefineError (s, _) -> s
    | Invalid_argument s -> "Invalid_argument " ^ s
    | e -> Printexc.to_string e
  let show mk =
    match mk () with
    | exception e -> "the term is not built: " ^ exn e
    | t ->
    let d = match dest_context t with
      | (x, body, cs, args) ->
          Printf.sprintf "v=%s, %d args, %d context vars, body %s" (Lm_symbol.to_string x) (List.length args) (List.length cs)
            (if is_var_term body then "a variable" else "a term")
      | exception e -> "refused: " ^ exn e in
    Printf.sprintf "is_context_term %-5b dest_context %s" (is_context_term t) d
  let cases = [
    "well formed: <H> t", (fun () -> mk_context_term (v "H") (c "t") [] []);
    "well formed, one arg: <H> t [a]", (fun () -> mk_context_term (v "H") (c "t") [ v "J" ] [ c "a" ]);
    "the main term binds nothing", (fun () -> ctx (Term_sig.Var (v "H")) [ mk_simple_bterm (c "t"); conts [] ]);
    "the main term binds two", (fun () -> ctx (Term_sig.Var (v "H")) [ mk_bterm [ v "H"; v "K" ] (c "t"); conts [] ]);
    "the parameter is a string", (fun () -> ctx (Term_sig.String "H") [ mk_bterm [ v "H" ] (c "t"); conts [] ]);
    "one subterm only", (fun () -> ctx (Term_sig.Var (v "H")) [ mk_bterm [ v "H" ] (c "t") ]);
    "no parameter", (fun () -> mk_term (mk_op Opname.context_opname []) [ mk_bterm [ v "H" ] (c "t"); conts [] ]);
    "the binder is another name, unused", (fun () -> ctx (Term_sig.Var (v "H")) [ mk_bterm [ v "K" ] (c "t"); conts [] ]);
  ]
end

module Std = T (Refiner_std.Refiner)
module Ds = T (Refiner_ds.Refiner)

let () =
  List.iter2 (fun (name, s) (_, d) ->
      Printf.printf "%s\n  std: %s\n  ds:  %s\n" name (Std.show s) (Ds.show d)) Std.cases Ds.cases
