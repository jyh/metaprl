(*
 * Manifest terms.
 *)

open Term_simple_sig
open Term_op_sig
open Term_subst_sig
open Term_man_sig

module TermMan (**)
   (Term : TermSimpleSig)
   (TermOp : TermOpSig
    with type term = Term.term)
   (TermSubst : TermSubstSig
    with type term = Term.term
    with type param = Term.param)
: TermManSig
  with type term = Term.term
  with type operator = Term.operator
  with type level_exp = Term.level_exp

(*
 * $Log$
 * Revision 1.1  1998/06/03 15:23:45  jyh
 * Generalized many the term_addr, term_man, and term_shape modules.
 *
 * Revision 1.1  1998/05/28 15:02:08  jyh
 * Partitioned refiner into subdirectories.
 *
 * Revision 1.1  1998/05/28 02:53:09  nogin
 * Splitted Term_ds and Term_ds_simple modules into a smaller modules
 * for use in the functorized refiner
 *
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
