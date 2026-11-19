(* Dform's default display of a bound term with two or more bound
   variables (format_bterm' in refiner/reflib/dform.ml: its list of
   variables, "x, y. t"), which no unit test, theory build or proof census
   reached (2026-11-18 rank737).  Each term has no display form, so
   Dform.string_of_term on the null base prints it by the default form.
   Stated, not reached: format_bvars' [] arm (the [h] arm matches first,
   so the recursion never reaches the empty list), and the dform_depth
   check around slot, which default printing does not call (a form with
   slots does: test_dform's harness, with the flag on).
   The expected file is the output of the code as written (2026-11-18),
   never typed.  Mutants (2026-11-18, each rebuilt and relinked; an
   identity control unchanged): the ", " separator changed, and every
   variable after the first dropped: 2 of 2 RED. *)
open Refiner.Refiner.Term
let op s = Opname.make_opname [ s; "Dfb" ]
let v = Lm_symbol.add
let bt vars t = mk_bterm (List.map v vars) t
let tm o bts = mk_term (mk_op (op o) []) bts
let a = tm "a" []
let cases = [
  "f{a}", tm "f" [ bt [] a ];
  "f{x. a}", tm "f" [ bt [ "x" ] a ];
  "f{x, y. a}", tm "f" [ bt [ "x"; "y" ] a ];
  "f{x, y, z. 'x}", tm "f" [ bt [ "x"; "y"; "z" ] (mk_var_term (v "x")) ];
  "f{x. a; y, z. a}", tm "f" [ bt [ "x" ] a; bt [ "y"; "z" ] a ];
]
let () =
  List.iter (fun (name, t) -> Printf.printf "%-20s %s\n%!" name (Dform.string_of_term Dform.null_base t)) cases
