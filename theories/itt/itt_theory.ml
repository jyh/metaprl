(*
 * All the parts of ITT.
 *
 *)

include Base_theory
include Itt_equal
include Itt_void
include Itt_atom
include Itt_bool
include Itt_int
include Itt_int_bool
include Itt_arith
include Itt_rfun
include Itt_dfun
include Itt_fun
include Itt_dprod
include Itt_prod
include Itt_union
include Itt_struct
include Itt_set
include Itt_isect
include Itt_subtype
include Itt_w
include Itt_prec
include Itt_srec
include Itt_quotient
include Itt_list

open Itt_equal
open Itt_rfun
open Itt_logic
open Itt_w

(*
 * Combine the precedences.
 *)
prec prec_equal < prec_apply
prec prec_type = prec_apply
prec prec_and < prec_apply
prec prec_w = prec_quant
prec prec_tree_ind < prec_quant

(*
 * $Log$
 * Revision 1.1  1998/07/05 01:47:36  jyh
 * Itt_theory.ml{,i} are now different.
 *
 * Revision 1.4  1998/06/15 22:33:37  jyh
 * Added CZF.
 *
 * Revision 1.3  1998/06/12 18:36:46  jyh
 * Working factorial proof.
 *
 * Revision 1.2  1998/06/12 13:47:42  jyh
 * D tactic works, added itt_bool.
 *
 * Revision 1.1  1997/04/28 15:52:30  jyh
 * This is the initial checkin of Nuprl-Light.
 * I am porting the editor, so it is not included
 * in this checkin.
 *
 * Directories:
 *     refiner: logic engine
 *     filter: front end to the Ocaml compiler
 *     editor: Emacs proof editor
 *     util: utilities
 *     mk: Makefile templates
 *
 * Revision 1.6  1996/09/02 19:37:46  jyh
 * Semi working package management.
 * All _univ version removed.
 *
 * Revision 1.5  1996/05/21 02:17:23  jyh
 * This is a semi-working version before Wisconsin vacation.
 *
 * Revision 1.4  1996/04/11 13:34:26  jyh
 * This is the final version with the old syntax for terms.
 *
 * Revision 1.3  1996/03/30 01:37:21  jyh
 * Initial version of ITT.
 *
 * Revision 1.2  1996/03/28 02:51:34  jyh
 * This is an initial version of the type theory.
 *
 * Revision 1.1  1996/03/05 19:59:50  jyh
 * Version just before LogicalFramework.
 *
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
