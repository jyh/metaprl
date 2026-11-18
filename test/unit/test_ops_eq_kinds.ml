(* Term.ops_eq on the parameter kinds test_ops_eq's generator never builds:
   an object id (ObId), meta-strings, meta-tokens and meta-operators
   (term_ds's ops_eq_params arms for them were unvisited, 2026-11-15
   profile).  Each pair is compared in term_std and term_ds, by ops_eq and
   by alpha_equal of the two operators applied to no subterms; a number
   inside a parameter is built either directly or as 40000 * 3 (a big
   integer, see test_ops_eq), which equal_num says is the same value.
   The expected file is the output of the code as written, never typed. *)
type pd =
  | N of int * bool          (* value, built as a product *)
  | Id of pd list | MS of string | MT of string | MO of string | S of string
and pair = string * pd list * pd list

module T (R : Refiner_sig.RefinerSig) = struct
  open R.Term
  let op s = Opname.make_opname [ s ]
  let sym = Lm_symbol.add
  let number v as_product =
    if as_product then Lm_num.mult_num (Lm_num.num_of_int (v / 3)) (Lm_num.num_of_int 3) else Lm_num.num_of_int v
  let rec mk_p = function
    | N (v, b) -> make_param (Term_sig.Number (number v b))
    | Id l -> make_param (Term_sig.ObId (make_object_id (List.map mk_p l)))
    | MS v -> make_param (Term_sig.MString (sym v))
    | MT v -> make_param (Term_sig.MToken (sym v))
    | MO v -> make_param (Term_sig.MOperator (sym v))
    | S s -> make_param (Term_sig.String s)
  let mk ps = mk_op (op "f") (List.map mk_p ps)
  let cmp a b =
    let oa = mk a and ob = mk b in
    Printf.sprintf "ops_eq %-5b alpha_equal %-5b" (ops_eq oa ob) (R.TermSubst.alpha_equal (mk_term oa []) (mk_term ob []))
end

module Std = T (Refiner_std.Refiner)
module Ds = T (Refiner_ds.Refiner)

let cases : pair list = [
  "ObId [3; a] vs ObId [3; a]", [ Id [ N (3, false); S "a" ] ], [ Id [ N (3, false); S "a" ] ];
  "ObId [3] vs ObId [4]", [ Id [ N (3, false) ] ], [ Id [ N (4, false) ] ];
  "ObId [3] vs ObId [3; 3]", [ Id [ N (3, false) ] ], [ Id [ N (3, false); N (3, false) ] ];
  "ObId [120000] vs ObId [40000*3]", [ Id [ N (120000, false) ] ], [ Id [ N (120000, true) ] ];
  "120000 vs 40000*3 (not in an ObId)", [ N (120000, false) ], [ N (120000, true) ];
  "MString a vs MString a", [ MS "a" ], [ MS "a" ];
  "MString a vs MString b", [ MS "a" ], [ MS "b" ];
  "MToken a vs MToken a", [ MT "a" ], [ MT "a" ];
  "MToken a vs MToken b", [ MT "a" ], [ MT "b" ];
  "MOperator a vs MOperator a", [ MO "a" ], [ MO "a" ];
  "MOperator a vs MOperator b", [ MO "a" ], [ MO "b" ];
  "MString a vs MToken a", [ MS "a" ], [ MT "a" ];
  "MToken a vs MOperator a", [ MT "a" ], [ MO "a" ];
]

let () =
  List.iter (fun (name, a, b) ->
      Printf.printf "%-36s std: %s  ds: %s\n" name (Std.cmp a b) (Ds.cmp a b)) cases
