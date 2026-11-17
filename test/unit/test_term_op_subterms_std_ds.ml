(* TermOp's subterm-shape functions in term_std and term_ds, side by side:
   is_three_subterm and is_five_subterm (a test), one_subterm_opname and
   two_subterms_opname (the subterms, or a refusal), on terms that match,
   that have another operator, another number of subterms, or a subterm
   with a binder.  Bisect at a45cd0437 left Term_op_ds's two tests and
   Term_op_std's two destructors unreached.  Each line prints what term_std
   and term_ds give.
   Pinned as found: they agree on every test and every success, and
   differ in the refusals: term_std's one_subterm_opname says "not a
   single subterm" where term_ds says "bad arity", and on a subterm with a
   binder term_ds refuses from dest_simple_bterm, term_std by arity.  The
   expected file is the output of the code. *)
open Term_sig
let v = Lm_symbol.add
module S (R : Refiner_sig.RefinerSig) = struct
  open R.Term
  open R.TermMan
  open R.TermOp
  let op s = Opname.make_opname [ s ]
  let c s = mk_simple_term (op s) []
  let name t = if is_var_term t then "'" ^ Lm_symbol.string_of_symbol (dest_var t) else Opname.string_of_opname (opname_of_term t)
  let f n = mk_simple_term (op "f") (List.init n (fun i -> c (Printf.sprintf "a%d" (i + 1))))
  let bound n = mk_term (mk_op (op "f") []) (List.init n (fun i -> mk_bterm (if i = 0 then [ v "x" ] else []) (c "a")))
  let inputs = [ "f{a1} (1 subterm)", f 1; "f{a1; a2}", f 2; "f{a1; a2; a3}", f 3; "f with 5", f 5;
                 "g{a1; a2; a3}", mk_simple_term (op "g") [ c "a1"; c "a2"; c "a3" ];
                 "f{x. a; a; a} (a binder)", bound 3; "f{x. a; a}", bound 2; "f{x. a}", bound 1 ]
  (* by name: Printexc's text for a functor's exception differs between compilers *)
  let refused = function
    | R.RefineError.RefineError (n, R.RefineError.TermMatchError (_, s)) -> "refused (" ^ n ^ ": " ^ s ^ ")"
    | R.RefineError.RefineError (n, _) -> "refused (" ^ n ^ ")"
    | e -> Printexc.to_string e
  let answers t =
    [ "is_three_subterm f", string_of_bool (is_three_subterm (op "f") t);
      "is_five_subterm f", string_of_bool (is_five_subterm (op "f") t);
      "one_subterm_opname f", (try name (one_subterm_opname (op "f") t) with e -> refused e);
      "two_subterms_opname f", (try let a, b = two_subterms_opname (op "f") t in name a ^ ", " ^ name b with e -> refused e) ]
  let lines () = List.map (fun (n, t) -> n, answers t) inputs
end
module Std = S (Refiner_std.Refiner)
module Ds = S (Refiner_ds.Refiner)
let () =
  List.iter2 (fun (n, ls) (_, ld) ->
      Printf.printf "%s:\n" n;
      List.iter2 (fun (f, a) (_, b) -> Printf.printf "  %-22s std %s%s\n" f a (if a = b then "" else "  | ds " ^ b)) ls ld)
    (Std.lines ()) (Ds.lines ())
