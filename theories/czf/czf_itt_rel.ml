(*
 * Assert a relation between two sets.
 *)

include Czf_itt_dall
include Czf_itt_dexists

open Refiner.Refiner.RefineError
open Nl_resource

open Sequent
open Var

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*
 * Relation P holds between the two sets.
 *)
declare rel{a, b. 'P['a; 'b]; 's1; 's2}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

primrw unfold_rel : rel{a, b. 'P['a; 'b]; 's1; 's2} <-->
   (dall{'s1; x. dexists{'s2; y. 'P['x; 'y]}} & dall{'s2; y. dexists{'s1; x. 'P['x; 'y]}})

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Typehood.
 *)
interactive rel_type 'H 'u 'v :
   sequent [squash] { 'H; u: set; v: set >- "type"{'P['u; 'v]} } -->
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- "type"{rel{x, y. 'P['x; 'y]; 's1; 's2}} }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Typehood.
 *)
let d_rel_typeT i p =
   if i = 0 then
      let u, v = maybe_new_vars2 p "u" "v" in
         rel_type (hyp_count_addr p) u v p
   else
      raise (RefineError ("d_rel_typeT", StringError "no elimination form"))

let rel_type_term = << "type"{rel{a, b. 'P['a; 'b]; 's1; 's2}} >>

let d_resource = d_resource.resource_improve d_resource (rel_type_term, d_rel_typeT)

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
