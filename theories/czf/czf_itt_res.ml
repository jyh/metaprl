(*
 * Restricted propositions have the separation property.
 *)

(*
 * Equality is restricted.
 *)
interactive eq_res 'H :
   sequent ['ext] { 'H >- fun_set{z. 's1['z]} } -->
   sequent ['ext] { 'H >- fun_set{z. 's2['z]} } -->
   sequent ['ext] { 'H >- restricted{z. eq{'s1['z]; 's2['z]}} }

interactive member_res 'H :
   sequent ['ext] { 'H >- fun_set{z. 's1['z]} } -->
   sequent ['ext] { 'H >- fun_set{z. 's2['z]} } -->
   sequent ['ext] { 'H >- restricted{z. member{'s1['z]; 's2['z]}} }

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
