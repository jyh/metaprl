(* TermMan.dest_so_var (std: refiner/term_gen/term_man_gen.ml, ds:
   refiner/term_ds/term_man_ds.ml) on terms that are not second-order
   variables: std's refusals were reached by no unit test, theory build
   or proof census (2026-11-15 rank).  Each case is asked of both
   implementations and prints the answer (the variable, its contexts
   and its argument count) or the RefineError's name.  std also builds a
   var-opname term by hand whose parameter is not a variable, and one
   with no subterms.  The expected file is the output of the code as
   written (2026-11-15). *)
module Check (R : Refiner_sig.RefinerSig) = struct
  open R.Term
  open R.TermMan
  let op s = Opname.make_opname [ s ]
  let v = Lm_symbol.add
  let c = mk_simple_term (op "c") []
  let ans t =
    try
      let x, cs, ts = dest_so_var t in
      Printf.sprintf "%s<%s>[%d]" (Lm_symbol.string_of_symbol x) (String.concat "," (List.map Lm_symbol.string_of_symbol cs)) (List.length ts)
    with
    | R.RefineError.RefineError (s, R.RefineError.TermMatchError (_, m)) -> "refused " ^ s ^ " (" ^ m ^ ")"
    | R.RefineError.RefineError (s, _) -> "refused " ^ s
  let cases = [
    "'a['x]<|H|>", mk_so_var_term (v "a") [ v "H" ] [ mk_var_term (v "x") ];
    "'a", mk_so_var_term (v "a") [] [];
    "'x (first-order)", mk_var_term (v "x");
    "c", c;
    "C[c]", mk_context_term (v "C") c [] [];
    "sequent", mk_sequent_term { sequent_args = c; sequent_hyps = SeqHyp.of_list []; sequent_concl = c } ]
  let answers () = List.map (fun (n, t) -> n, ans t) cases
end

module S = Check (Refiner_std.Refiner)
module D = Check (Refiner_ds.Refiner)

(* the two refusals differ only in their module's name *)
let norm s =
  let strip p s =
    let lp = String.length p and ls = String.length s in
    let b = Buffer.create ls in
    let i = ref 0 in
    while !i < ls do
      if !i + lp <= ls && String.sub s !i lp = p then i := !i + lp
      else (Buffer.add_char b s.[!i]; incr i)
    done;
    Buffer.contents b in
  strip "Term_man_ds." (strip "Term_man_gen." s)

let () =
  List.iter2 (fun (n, s) (_, d) ->
      Printf.printf "%-22s std %s | ds %s%s\n" n s d (if norm s = norm d then "" else "  DIFFER"))
    (S.answers ()) (D.answers ());
  (* std only: a var-opname term with a non-variable parameter, and with no subterms *)
  let module T = Refiner_std.Refiner.Term in
  let var_op = Opname.var_opname in
  let num = T.make_param (Term_sig.Number (Lm_num.num_of_int 1)) in
  let c = T.mk_simple_term (Opname.make_opname [ "c" ]) [] in
  let conts = Refiner_std.Refiner.TermMan.mk_xlist_term [] in
  List.iter (fun (n, t) -> Printf.printf "std %-28s %s\n" n (S.ans t))
    [ "var[1:n]{c; conts}", T.mk_term (T.mk_op var_op [ num ]) [ T.mk_bterm [] c; T.mk_bterm [] conts ];
      "var[x:v]{} (no subterms)", T.mk_term (T.mk_op var_op [ T.make_param (Term_sig.Var (Lm_symbol.add "x")) ]) [] ]
