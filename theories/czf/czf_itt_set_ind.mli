(*
 * These are the axioms of CZF set theory.
 *)

include Czf_itt_and
include Czf_itt_or
include Czf_itt_implies
include Czf_itt_all
include Czf_itt_exists
include Czf_itt_dall
include Czf_itt_dexists

(*
 * Set induction.
 *
 * H >- all x. P(x)
 * by set_induction
 * H; x: set; w: (all y: x. P(y)) >- P(x)
 * H >- P(x) wf
 *)
axiom set_induction 'H 'x 'y 'w :
   sequent ['ext] { 'H; x: set; w: (all y: 'x. 'P['y]) => 'P['x] >- 'P['x] } -->
   sequent ['ext] { 'H; x: set >- wf{'P['x]} } -->
   sequent ['ext] { 'H >- "all"{z. 'P['z]} }

(*
 * $Log$
 * Revision 1.1  1998/07/08 15:41:52  jyh
 * Pushed higherC into the refiner for efficiency.
 *
 * Revision 1.1  1998/06/23 22:12:21  jyh
 * Improved rewriter speed with conversion tree and flist.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
