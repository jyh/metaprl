(* Term.dest_simple_term_opname (refiner/term_std, refiner/term_ds): the
   subterms of a term with the given opname and no parameters.  Its two
   refusals were unvisited in term_ds (2026-11-15 profile).  Each case
   runs in term_std and term_ds; a refusal prints its first string and the
   TermMatchError message.  Pinned as found: on a bound subterm the two
   refuse from different places (std "binding vars exist" in
   dest_simple_term_opname, ds in dest_simple_bterm).
   The expected file is the output of the code as written, never typed. *)
module T (R : Refiner_sig.RefinerSig) = struct
  open R.Term
  let op s = Opname.make_opname [ s ]
  let c s = mk_simple_term (op s) []
  let show name t =
    match dest_simple_term_opname (op "f") t with
    | l -> Printf.sprintf "%d subterms" (List.length l)
    | exception R.RefineError.RefineError (s, R.RefineError.TermMatchError (_, m)) -> "refused: " ^ s ^ " (" ^ m ^ ")"
    | exception R.RefineError.RefineError (s, _) -> "refused: " ^ s
  let cases = [
    "f{a; b}", mk_simple_term (op "f") [ c "a"; c "b" ];
    "f", c "f";
    "g{a} (another opname)", mk_simple_term (op "g") [ c "a" ];
    "f[1]{a} (a parameter)", mk_term (mk_op (op "f") [ make_param (Term_sig.Number (Lm_num.num_of_int 1)) ]) [ mk_simple_bterm (c "a") ];
    "f{x. a} (a bound subterm)", mk_term (mk_op (op "f") []) [ mk_bterm [ Lm_symbol.add "x" ] (c "a") ];
  ]
  let run () = List.map (fun (name, t) -> name, (try show name t with e -> "raised " ^ Printexc.to_string e)) cases
end

module Std = T (Refiner_std.Refiner)
module Ds = T (Refiner_ds.Refiner)

let () =
  List.iter2 (fun (name, s) (_, d) -> Printf.printf "%s\n  std: %s\n  ds:  %s\n" name s d) (Std.run ()) (Ds.run ())
