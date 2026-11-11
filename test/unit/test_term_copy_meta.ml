(* Term_header_constr (refiner/term_gen), through Term_copy_weak: the
   conversion of terms and meta-terms from one term implementation into
   another's hash table, used when a term crosses implementations.  The
   proof census runs two of its branches no unit test did (2026-11-11
   reach census, 9 lines): a level-expression parameter (MLevel) and a
   MetaFunction meta-term.  Each term here is built in term_std, converted
   into Refiner.Refiner's terms (term_ds in the default build), and
   converted back; the line prints the term_ds result
   and whether the round trip is alpha-equal to the original (terms) or
   structurally equal with alpha-equal leaves (meta-terms).  The cases:
   level parameters (constant, variables with offsets), other parameter
   kinds, a binder, a sequent, and each meta-term form (MetaTheorem,
   MetaImplies, MetaFunction, MetaIff), nested. *)
open Term_sig

module S = Refiner_std.Refiner
module D = Refiner.Refiner
module S2D = Term_copy_weak.TermCopyWeak (S) (D)
module D2S = Term_copy_weak.TermCopyWeak (D) (S)

let v = Lm_symbol.add
let op s = Opname.make_opname [ s ]
let mk o params ts = S.Term.mk_term (S.Term.mk_op (op o) params) (List.map (fun t -> S.Term.mk_bterm [] t) ts)
let c s = mk s [] []
let lvl k vars = S.Term.make_param (MLevel (S.Term.mk_level k (List.map (fun (x, o) -> S.Term.mk_level_var (v x) o) vars)))
let lam x t = S.Term.mk_term (S.Term.mk_op (op "lam") []) [ S.Term.mk_bterm [ v x ] t ]

let dinfo = D.TermHash.p_create 17
let sinfo = S.TermHash.p_create 17
let dshow = Simple_print.SimplePrint.string_of_term

let term name t =
  let d = S2D.p_convert dinfo t in
  let back = D2S.p_convert sinfo d in
  Printf.printf "%-34s %s\n   round trip alpha-equal %b\n" name (dshow d) (S.TermSubst.alpha_equal t back)

let rec meq a b = match a, b with
  | MetaTheorem t1, MetaTheorem t2 -> S.TermSubst.alpha_equal t1 t2
  | MetaImplies (a1, b1), MetaImplies (a2, b2) | MetaIff (a1, b1), MetaIff (a2, b2) -> meq a1 a2 && meq b1 b2
  | MetaFunction (t1, a1, b1), MetaFunction (t2, a2, b2) -> S.TermSubst.alpha_equal t1 t2 && meq a1 a2 && meq b1 b2
  | MetaLabeled (l1, a1), MetaLabeled (l2, a2) -> l1 = l2 && meq a1 a2
  | _ -> false
let rec mshow = function
  | MetaTheorem t -> dshow t
  | MetaImplies (a, b) -> "(" ^ mshow a ^ " --> " ^ mshow b ^ ")"
  | MetaFunction (t, a, b) -> "(" ^ dshow t ^ ": " ^ mshow a ^ " -> " ^ mshow b ^ ")"
  | MetaIff (a, b) -> "(" ^ mshow a ^ " <--> " ^ mshow b ^ ")"
  | MetaLabeled (l, a) -> l ^ ": " ^ mshow a

let meta name mt =
  let d = S2D.p_convert_meta dinfo mt in
  let back = D2S.p_convert_meta sinfo d in
  Printf.printf "%-34s %s\n   round trip equal %b\n" name (mshow d) (meq mt back)

let () =
  term "f[level 1]" (mk "f" [ lvl 1 [] ] []);
  term "f[level 0 | i]" (mk "f" [ lvl 0 [ "i", 0 ] ] []);
  term "f[level 2 | i+1, j]" (mk "f" [ lvl 2 [ "i", 1; "j", 0 ] ] []);
  term "f[level 1 | i+3]{g[level i]}" (mk "f" [ lvl 1 [ "i", 3 ] ] [ mk "g" [ lvl 0 [ "i", 0 ] ] [] ]);
  term "f[3; \"s\"; tok]" (mk "f" [ S.Term.make_param (Number (Lm_num.num_of_int 3)); S.Term.make_param (String "s"); S.Term.make_param (Token (op "tok")) ] []);
  term "lam x. f{x; c}" (lam "x" (mk "f" [] [ S.Term.mk_var_term (v "x"); c "c" ]));
  let a = MetaTheorem (c "A") and b = MetaTheorem (mk "B" [ lvl 1 [ "i", 0 ] ] []) in
  meta "A" a;
  meta "A --> B" (MetaImplies (a, b));
  meta "x: A -> B" (MetaFunction (S.Term.mk_var_term (v "x"), a, b));
  meta "x: A -> (y: B -> A)" (MetaFunction (S.Term.mk_var_term (v "x"), a, MetaFunction (S.Term.mk_var_term (v "y"), b, a)));
  meta "A <--> (A --> B)" (MetaIff (a, MetaImplies (a, b)));
  meta "(x: A -> B) --> B" (MetaImplies (MetaFunction (S.Term.mk_var_term (v "x"), a, b), b))
