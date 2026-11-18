(* Term_man_gen.match_hyp and match_hyp_all (refiner/term_gen/term_man_gen.ml),
   the std sequent's hypothesis destructors: a hyp{A; x. rest} node must
   have exactly two subterms, the first binding nothing and the second
   one variable.  Their refusals ("malformed hypothesis") were reached by
   no unit test, theory build or proof census (2026-11-15 rank).  A std
   sequent x: A; y: B >- C is built, its first hyp node is replaced by
   three malformed shapes (no binder, one subterm, a binder on the
   first), and each sequent destructor that reads hypotheses is asked;
   it prints its answer or the name of the RefineError it raises.  The
   expected file is the output of the code as written (2026-11-15).
   Pinned as found: nth_binding refuses under the name "nth_hyp". *)
open Term_sig
module R = Refiner_std.Refiner
open R.Term
open R.TermMan

let op s = Opname.make_opname [ s ]
let c s = mk_simple_term (op s) []
let v = Lm_symbol.add
let hyp_op = Opname.mk_opname "hyp" Opname.xperv
let good =
  mk_sequent_term { sequent_args = c "arg"; sequent_hyps = SeqHyp.of_list [ Hypothesis (v "x", c "A"); Hypothesis (v "y", c "B") ];
                    sequent_concl = c "C" }

(* replace the first hyp node's subterms *)
let rec damage f t =
  if is_var_term t || is_so_var_term t then t
  else
    let { term_op; term_terms } = dest_term t in
    if Opname.eq (dest_op term_op).op_name hyp_op then mk_term term_op (f term_terms)
    else mk_term term_op (List.map (fun bt -> let { bvars; bterm } = dest_bterm bt in mk_bterm bvars (damage f bterm)) term_terms)

let first_term bts = (dest_bterm (List.hd bts)).bterm
let second_term bts = (dest_bterm (List.nth bts 1)).bterm
let shapes = [
  "well formed", (fun bts -> bts);
  "hyp{A; rest} (no binder)", (fun bts -> [ mk_bterm [] (first_term bts); mk_bterm [] (second_term bts) ]);
  "hyp{A} (one subterm)", (fun bts -> [ mk_bterm [] (first_term bts) ]);
  "hyp{z. A; x. rest}", (fun bts -> [ mk_bterm [ v "z" ] (first_term bts); List.nth bts 1 ]) ]

let ans f = try f () with R.RefineError.RefineError (s, _) -> "refused " ^ s
let ops = [
  "explode_sequent", (fun t -> string_of_int (SeqHyp.length (explode_sequent t).sequent_hyps) ^ " hyps");
  "num_hyps", (fun t -> string_of_int (num_hyps t));
  "nth_hyp 1", (fun t -> ignore (nth_hyp t 1); "a term");
  "nth_binding 1", (fun t -> Lm_symbol.string_of_symbol (nth_binding t 1));
  "hyps", (fun t -> string_of_int (List.length (hyps t)) ^ " terms");
  "concl", (fun t -> ignore (concl t); "a term");
  "declared_vars", (fun t -> String.concat "," (List.map Lm_symbol.string_of_symbol (declared_vars t)));
  "get_decl_number y", (fun t -> string_of_int (get_decl_number t (v "y")));
  "get_hyp_number B", (fun t -> string_of_int (get_hyp_number t (c "B")));
  "replace_concl", (fun t -> ignore (replace_concl t (c "D")); "a term") ]

let () =
  List.iter (fun (sname, f) ->
      let t = damage f good in
      Printf.printf "== %s\n" sname;
      List.iter (fun (oname, g) -> Printf.printf "  %-18s %s\n" oname (ans (fun () -> g t))) ops) shapes
