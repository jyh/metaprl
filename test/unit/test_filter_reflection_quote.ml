(* unit-link: filter *)
(*
 * Filter_reflection.quote_term: a term quoted into the reflected
 * syntax, without a depth (sweep_quote0_term, Reflect!mk_term) and with
 * one (sweep_quote_term, Reflect!mk_bterm{'d; ...}).  Their sweeps had
 * arms that nothing reached (2026-11-15 rank: unit tests, theory build,
 * proof census): a second-order variable's arguments, the refusal of a
 * context, an unquote, a binding of more than one variable, and a
 * sequent's hypotheses; with a depth, a second-order variable, a
 * context, a sequent and its refusal of hypotheses.
 *
 * The parse state names every reflected operator Reflect!<name> and
 * refuses everything else (quote_term asks it for opnames only).  Each
 * line prints the quoted term (Simple_print, whitespace collapsed to
 * one space) or the refusal.
 *
 * Pinned as found: with a depth a second-order variable is returned
 * as it is, its arguments not quoted ('a['x; c] gives 'a['x; Test!c]),
 * where without a depth they are.  A quoted sequent without a depth is a
 * sequent whose argument is Reflect!bsequent{arg}; with a depth, any
 * hypothesis is refused ("hypotheses not supported yet").
 *
 * The expected file is the output of the code as written (2026-11-15),
 * never typed.
 *)
open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermOp
open Refiner.Refiner.RefineError

let v = Lm_symbol.add
let op s = Opname.make_opname [ s; "Test" ]
let k s = mk_simple_term (op s) []
let var x = mk_var_term (v x)
let lam x b = mk_term (mk_op (op "lam") []) [ mk_bterm [ v x ] b ]
let lam2 x y b = mk_term (mk_op (op "lam2") []) [ mk_bterm [ v x; v y ] b ]
let pair a b = mk_simple_term (op "pair") [ a; b ]
let sov x conts args = mk_so_var_term (v x) (List.map v conts) args
let seq hyps concl = mk_sequent_term { sequent_args = k "sa"; sequent_hyps = SeqHyp.of_list hyps; sequent_concl = concl }
let unq t = mk_dep0_term (Opname.mk_opname "xunquote" (Opname.mk_opname "Perv" Opname.nil_opname)) t

let state = {
  Filter_base_type.parse_quotation = (fun _ _ -> failwith "parse_quotation");
  parse_opname = (fun _ names _ _ -> Opname.make_opname (List.rev names @ [ "Reflect" ]));
  parse_shape = (fun _ -> failwith "parse_shape");
  parse_param = (fun _ -> failwith "parse_param");
}
let info = Filter_reflection.create_parse_info state

let show name f =
  let r =
    try String.concat " " (List.filter (( <> ) "") (String.split_on_char ' ' (String.map (fun c -> if c = '\n' then ' ' else c) (Simple_print.SimplePrint.string_of_term (f ()))))) with
    | RefineForceError (_, s, StringTermError (m, _)) -> "refused (" ^ s ^ ": " ^ m ^ ")"
    | RefineError (s, _) -> "RefineError " ^ s
    | Failure s -> "Failure " ^ s
    | Invalid_argument s -> "Invalid_argument " ^ s
  in
    Printf.printf "%-26s %s\n" name r

let cases = [
  "a constant", k "c";
  "a variable", var "x";
  "pair{x; c}", pair (var "x") (k "c");
  "lam{x. x}", lam "x" (var "x");
  "lam{x. pair{x; y}}", lam "x" (pair (var "x") (var "y"));
  "lam2{x, y. pair{x; y}}", lam2 "x" "y" (pair (var "x") (var "y"));
  "'a['x]", sov "a" [] [ var "x" ];
  "'a['x; c]", sov "a" [] [ var "x"; k "c" ];
  "a context <H>", mk_context_term (v "H") (k "c") [] [];
  "xunquote{c}", unq (k "c");
  "pair{xunquote{x}; c}", pair (unq (var "x")) (k "c");
  "sequent >- c", seq [] (k "c");
  "sequent x: c >- x", seq [ Term_sig.Hypothesis (v "x", k "c") ] (var "x");
  "sequent <J>; x: c >- x", seq [ Term_sig.Context (v "J", [], []); Term_sig.Hypothesis (v "x", k "c") ] (var "x");
  "sequent <J['c]> >- c", seq [ Term_sig.Context (v "J", [], [ pair (k "c") (k "c") ]) ] (k "c");
]

let () =
  print_endline "quote_term, no depth (sweep_quote0_term):";
  List.iter (fun (n, t) -> show n (fun () -> Filter_reflection.quote_term info t)) cases;
  print_endline "quote_term ~depth:d (sweep_quote_term):";
  List.iter (fun (n, t) -> show n (fun () -> Filter_reflection.quote_term info ~depth:(var "d") t)) cases
