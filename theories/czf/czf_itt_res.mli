(*
 * Restricted propositions have the separation property.
 *)

(*
 * Equality is restricted.
 *)
axiom eq_res 'H :
   sequent ['ext] { 'H >- fun_set{z. 's1['z]} } -->
   sequent ['ext] { 'H >- fun_set{z. 's2['z]} } -->
   sequent ['ext] { 'H >- restricted{z. eq{'s1['z]; 's2['z]}} }

axiom member_res 'H :
   sequent ['ext] { 'H >- fun_set{z. 's1['z]} } -->
   sequent ['ext] { 'H >- fun_set{z. 's2['z]} } -->
   sequent ['ext] { 'H >- restricted{z. member{'s1['z]; 's2['z]}} }

(*
 * $Log$
 * Revision 1.1  1998/07/14 15:43:23  jyh
 * Intermediate version with auto tactic.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
