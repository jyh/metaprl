(*
 * Helpful rules about induction combinator.
 *)

include Czf_itt_sep

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Dependent function types.
 *)
axiom set_ind_dfun_type 'H (bind{u. 'B['u]}) :
   sequent [squash] { 'H >- isset{'s} } -->
   sequent [squash] { 'H; u: set >- "type"{'B['u]} } -->
   sequent [squash] { 'H >- fun_prop{u. 'B['u]} } -->
   sequent ['ext] { 'H >- "type"{set_ind{'s; T, f, g. x: 'T -> 'B['f 'x]}} }

axiom set_ind_dfun_fun 'H (bind{x. bind{y. 'B['x; 'y]}}) 'u 'v :
   sequent ['ext] { 'H >- fun_set{z. 'A['z]} } -->
   sequent [squash] { 'H; u: set; v: set >- "type"{'B['u; 'v]} } -->
   sequent ['ext] { 'H; u: set >- fun_prop{z. 'B['u; 'z]} } -->
   sequent ['ext] { 'H; v: set >- fun_prop{z. 'B['z; 'v]} } -->
   sequent ['ext] { 'H >- fun_prop{z. set_ind{'A['z]; T, f, g. x: 'T -> 'B['z; 'f 'x]}} }

(*
 * Dependent product types.
 *)
axiom set_ind_dprod_type 'H (bind{u. 'B['u]}) :
   sequent [squash] { 'H >- isset{'s} } -->
   sequent [squash] { 'H; u: set >- "type"{'B['u]} } -->
   sequent [squash] { 'H >- fun_prop{u. 'B['u]} } -->
   sequent ['ext] { 'H >- "type"{set_ind{'s; T, f, g. x: 'T * 'B['f 'x]}} }

axiom set_ind_dprod_fun 'H (bind{x. bind{y. 'B['x; 'y]}}) 'u 'v :
   sequent ['ext] { 'H >- fun_set{z. 'A['z]} } -->
   sequent [squash] { 'H; u: set; v: set >- "type"{'B['u; 'v]} } -->
   sequent ['ext] { 'H; u: set >- fun_prop{z. 'B['u; 'z]} } -->
   sequent ['ext] { 'H; v: set >- fun_prop{z. 'B['z; 'v]} } -->
   sequent ['ext] { 'H >- fun_prop{z. set_ind{'A['z]; T, f, g. x: 'T * 'B['z; 'f 'x]}} }

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
