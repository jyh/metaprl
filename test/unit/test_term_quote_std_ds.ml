(* quote_term, is_quoted_term and unquote_term (TermOp) in term_std and
   term_ds, side by side: an operator term, one with parameters and a
   subterm, a variable, a sequent, and unquote_term of a term that is not
   quoted.  term_ds's refusals were unreached (bisect at a45cd0437:
   Term_op_ds.quote_term's variable/sequent arm and unquote_term's).  Each line prints, for one input, what term_std and
   term_ds give: the quoted term (Simple_print) with is_quoted_term and
   the term unquote_term gives back, or the exception.
   Pinned as found: the two disagree on a variable and on a sequent.
   term_std holds both as ordinary terms and quotes them; term_ds refuses
   with Invalid_argument.  Their unquote_term refusals are worded
   differently ("not a quoted term" in term_std, "not a quote term" in
   term_ds).  term_ds cannot build the quoted variable term_std makes
   (var[@, v:x]): its make_term refuses a var operator that does not look
   like a variable, so unquote_term's own refusal of a quoted variable or
   sequent (term_op_ds.ml, "not implementes") is unreachable from here. *)
open Term_sig
let v = Lm_symbol.add
module S (R : Refiner_sig.RefinerSig) = struct
  open R.Term
  open R.TermMan
  open R.TermOp
  let op s = Opname.make_opname [ s ]
  (* the operator, its parameters and the number of subterms *)
  let param p = match dest_param p with
    | Number n -> Lm_num.string_of_num n | String s -> Printf.sprintf "%S" s | Var x -> "v:" ^ Lm_symbol.string_of_symbol x
    | Quote -> "@" | _ -> "?"
  let show t =
    if is_var_term t then "'" ^ Lm_symbol.string_of_symbol (dest_var t)
    else if is_sequent_term t then "a sequent term"
    else
      let { term_op = o; term_terms = bts } = dest_term t in
      let { op_name = n; op_params = ps } = dest_op o in
      Printf.sprintf "%s[%s]{%d}" (Opname.string_of_opname n) (String.concat "," (List.map param ps)) (List.length bts)
  let exn = function
    | R.RefineError.RefineError (n, R.RefineError.TermMatchError (_, s)) -> "RefineError (" ^ n ^ ": " ^ s ^ ")"
    | Invalid_argument s -> "Invalid_argument " ^ s
    | e -> Printexc.to_string e
  let inputs () =
    [ "an operator", mk_simple_term (op "f") [];
      "parameters and a subterm", mk_term (mk_op (op "g") [ make_param (Number (Lm_num.num_of_int 3)); make_param (String "s") ]) [ mk_bterm [ v "x" ] (mk_var_term (v "x")) ];
      "a variable", mk_var_term (v "x");
      "a sequent", mk_sequent_term { sequent_args = mk_simple_term (op "sa") []; sequent_hyps = R.Term.SeqHyp.of_list [ Hypothesis (v "y", mk_simple_term (op "a") []) ]; sequent_concl = mk_simple_term (op "b") [] } ]
  let quote_line t =
    match quote_term t with
    | q -> Printf.sprintf "%s (quoted %b), unquoted %s" (show q) (is_quoted_term q) (try show (unquote_term q) with e -> exn e)
    | exception e -> exn e
  let unquote_plain () = try show (unquote_term (mk_simple_term (op "f") [])) with e -> exn e
  let unquote_var () = try show (unquote_term (mk_var_term (v "x"))) with e -> exn e
  (* the form term_std's quote_term gives a variable, built by hand *)
  let unquote_qvar () =
    try show (unquote_term (mk_term (mk_op (op "var") [ make_param Quote; make_param (Var (v "x")) ]) [])) with e -> exn e
end
module Std = S (Refiner_std.Refiner)
module Ds = S (Refiner_ds.Refiner)
let () =
  List.iter2 (fun (name, ts) (_, td) ->
      Printf.printf "quote_term, %s:\n  std: %s\n  ds:  %s\n" name (Std.quote_line ts) (Ds.quote_line td))
    (Std.inputs ()) (Ds.inputs ());
  Printf.printf "unquote_term of f (not quoted):\n  std: %s\n  ds:  %s\n" (Std.unquote_plain ()) (Ds.unquote_plain ());
  Printf.printf "unquote_term of a variable:\n  std: %s\n  ds:  %s\n" (Std.unquote_var ()) (Ds.unquote_var ());
  Printf.printf "unquote_term of var[@,v:x] (a quoted variable as term_std quotes it):\n  std: %s\n  ds:  %s\n" (Std.unquote_qvar ()) (Ds.unquote_qvar ())
