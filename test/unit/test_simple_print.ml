(* Simple_print (refiner/reflib), the refiner's plain-text term printer,
   used for error messages and debugging; no unit test called it (the 11-02
   reflib coverage page). Each line prints one value as string_of_* gives
   it: variables (dstring_of_var on plain, indexed and empty names),
   opnames, level expressions, one parameter of each kind but Shape and
   Operator, terms with second-order variables and contexts, binders,
   sequents with hypotheses and contexts, meta-terms, and
   short_string_of_term on a long term. Pinned as it prints today. No name
   holds a backslash: libmojave's quoting of those changed (libmojave #177)
   and metaprl's CI builds against libmojave master. *)
open Refiner.Refiner
open Term
open TermMan
open Term_sig
module P = Simple_print.SimplePrint

let v = Lm_symbol.add
let op l = Opname.make_opname (List.rev l)
let c s = mk_simple_term (op [ s ]) []
let show name s = Printf.printf "%-34s %s\n" name s

let () =
  show "dstring_of_var x" (Simple_print.dstring_of_var (v "x"));
  show "dstring_of_var x, index 3" (Simple_print.dstring_of_var (Lm_symbol.make "x" 3));
  show "dstring_of_var empty" (Simple_print.dstring_of_var (v ""));
  show "string_of_opname Itt_int!add" (P.string_of_opname (op [ "Itt_int"; "add" ]));
  show "string_of_opname two words" (P.string_of_opname (op [ "two words" ]));
  let l1 = mk_const_level_exp 2 and lk = mk_var_level_exp (v "k") in
  show "level 2" (P.string_of_level_exp l1);
  show "level k+1" (P.string_of_level_exp (incr_level_exp lk));
  show "level max(k, 2)" (P.string_of_level_exp (max_level_exp lk l1 0));
  List.iter (fun (name, p) -> show ("param " ^ name) (P.string_of_param (make_param p)))
    [ "Number 42", Number (Lm_num.num_of_int 42);
      "Number 2^70", Number (Lm_num.num_of_string "1180591620717411303424");
      "String s", String "s";
      "String two words", String "two words";
      "String q\"uote", String "q\"uote";
      "String empty", String "";
      "Token", Token (op [ "Itt_int"; "add" ]);
      "Var", Var (v "x");
      "MNumber", MNumber (v "n");
      "MString", MString (v "s");
      "MToken", MToken (v "t");
      "MLevel k+1", MLevel (incr_level_exp lk);
      "Quote", Quote;
      "ObId [1]", ObId [ make_param (Number (Lm_num.num_of_int 1)) ];
      "ParamList [1; a]", ParamList [ make_param (Number (Lm_num.num_of_int 1)); make_param (String "a") ] ];
  let x = v "x" in
  let f a = mk_simple_term (op [ "f" ]) a in
  let lam y t = mk_term (mk_op (op [ "lam" ]) []) [ mk_bterm [ y ] t ] in
  let terms = [
    "var x", mk_var_term x;
    "constant c", c "c";
    "f{x; c}", f [ mk_var_term x; c "c" ];
    "op with params", mk_term (mk_op (op [ "p" ]) [ make_param (Number (Lm_num.num_of_int 3)); make_param (String "two words") ]) [];
    "SO var A<H;S>[x; c]", mk_so_var_term (v "A") [ v "H"; v "S" ] [ mk_var_term x; c "c" ];
    "SO var B (no args)", mk_so_var_term (v "B") [] [];
    "lam x. f{x}", lam x (f [ mk_var_term x ]);
    "two binders", mk_term (mk_op (op [ "spread" ]) []) [ mk_bterm [ v "a"; v "b" ] (f [ mk_var_term (v "a") ]) ];
    "sequent", mk_sequent_term
      { sequent_args = c "sa";
        sequent_hyps = SeqHyp.of_list [ Hypothesis (v "h", c "T"); Context (v "K", [ v "H" ], [ mk_var_term (v "h") ]) ];
        sequent_concl = f [ mk_var_term (v "h") ] } ] in
  List.iter (fun (name, t) -> show name (P.string_of_term t)) terms;
  let rec deep n = if n = 0 then c "z" else f [ deep (n - 1); deep (n - 1) ] in
  let long = deep 7 in
  show "short_string_of_term, 2^7 leaves" (P.short_string_of_term long);
  show "string_of_term, same: length" (string_of_int (String.length (P.string_of_term long)));
  let t1 = c "A" and t2 = c "B" in
  List.iter (fun (name, m) -> show name (P.string_of_mterm m))
    [ "MetaTheorem", MetaTheorem t1;
      "MetaImplies", MetaImplies (MetaTheorem t1, MetaTheorem t2);
      "MetaFunction", MetaFunction (mk_var_term x, MetaTheorem t1, MetaTheorem t2);
      "MetaIff", MetaIff (MetaTheorem t1, MetaTheorem t2);
      "MetaLabeled", MetaLabeled ("lbl", MetaTheorem t1) ]
