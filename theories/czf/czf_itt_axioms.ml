(*
 * These are the axioms of CZF set theory.
 *)

include Itt_theory
include Czf_itt_and
include Czf_itt_or
include Czf_itt_implies
include Czf_itt_all
include Czf_itt_exists
include Czf_itt_dall
include Czf_itt_dexists

(*
 * Make forula concise.
 *)
declare "iff"{'a; 'b}
primrw unfold_iff : "iff"{'a; 'b} <--> "and"{.'a => 'b; .'b => 'a}

(*
 * Set induction.
 *
 * H >- all x. P(x)
 * by set_induction
 * H; x: set; w: (all y: x. P(y)) >- P(x)
 * H >- P(x) wf
 *)
prim set_induction 'H 'x 'y 'w :
   sequent ['ext] { 'H; x: set; w: (all y: 'x. 'P['y]) => 'P['x] >- 'P['x] } -->
   sequent ['ext] { 'H; x: set >- wf{'P['x]} } -->
   sequent ['ext] { 'H >- "all"{z. 'P['z]} } =
   it

(*
 * Restricted separation.
 *)
prim res_separation 'H 'w :
   sequent ['ext] { 'H; w: set >- restricted{'P['x]} } -->
   sequent ['ext] { 'H >- "all"{a. "exists"{b. "all"{x. "iff"{member{'x; 'b}; ."and"{member{'x; 'a}; 'P['x]}}}}} } =
   it

(*
 * Strong collection.
 *)
prim strong_collection_left 'H 'a 'z (lambda{x1. lambda{x2. 'P['x1; 'x2]}}) :
   sequent ['ext] { 'H >- member{'a; set} } -->
   sequent ['ext] { 'H >- all z: 'a. "exists"{y. 'P['z; 'y]} } -->
   sequent ['ext] { 'H >- "exists"{b. "exists"{'b; y. 'P['x; 'y]}} } =
   it

(*
 * Subset collection.
 *)
prim subset_collection_left 'H :
   sequent ['ext] { 'H >- member{'a1; set} } -->
   sequent ['ext] { 'H >- member{'a2; set} } -->
   sequent ['ext] { 'H >- "exists"{c. "all"{u. ("all"{'a1; x. "exists"{'a2; y. 'P['x; 'y; 'u]}}) => ("exists"{'c; b. "all"{'a1; x. "exists"{'b; y. 'P['x; 'y; 'u]}}})}} } =
   it

(*
 * $Log$
 * Revision 1.1  1998/06/23 22:12:20  jyh
 * Improved rewriter speed with conversion tree and flist.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
