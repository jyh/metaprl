(* TermOp.is_five_subterm (refiner/term_std/term_op_std.ml,
   refiner/term_ds/term_op_ds.ml): true for a term of the given opname
   with exactly five subterms, none binding a variable.  Nothing in the
   tree calls it (only Refiner_debug's wrapper), and no unit test, theory
   build or proof census reached it (2026-11-15 rank).  Each case is
   asked of both implementations and printed with their answers; the
   expected file is the output of the code as written (2026-11-15). *)
module Check (R : Refiner_sig.RefinerSig) = struct
  open R.Term
  let op s = Opname.make_opname [ s ]
  let c = mk_simple_term (op "c") []
  let five o = mk_simple_term (op o) [ c; c; c; c; c ]
  let cases =
    [ "f{c; c; c; c; c}", five "f";
      "f{c; c; c; c}", mk_simple_term (op "f") [ c; c; c; c ];
      "f{c; c; c; c; c; c}", mk_simple_term (op "f") [ c; c; c; c; c; c ];
      "g{c; c; c; c; c}", five "g";
      "f{c; c; x. c; c; c}",
        mk_term (mk_op (op "f") [])
          (List.map (fun vs -> mk_bterm (List.map Lm_symbol.add vs) c) [ []; []; [ "x" ]; []; [] ]);
      "f[1:n]{c; c; c; c; c}",
        mk_term (mk_op (op "f") [ make_param (Term_sig.Number (Lm_num.num_of_int 1)) ])
          (List.map (fun t -> mk_bterm [] t) [ c; c; c; c; c ]) ]
  let answers () = List.map (fun (n, t) -> n, R.TermOp.is_five_subterm (op "f") t) cases
end

module S = Check (Refiner_std.Refiner)
module D = Check (Refiner_ds.Refiner)

let () =
  List.iter2 (fun (n, s) (_, d) ->
      Printf.printf "%-26s std %b  ds %b%s\n" n s d (if s = d then "" else "  DIFFER"))
    (S.answers ()) (D.answers ())
