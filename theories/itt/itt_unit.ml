(*
 * Although unit is not strictly necessary,
 * we define it anyway, so we can use it before numbers
 * are defined.
 *
 * Type unit contains one element, it.
 *)

open Debug
open Sequent
open Term
open Resource

include Tactic_type
include Itt_equal

(*
 * incr_debug_level DebugMessage
 * debug_string DebugLoad "Loading itt_void..."
 *)

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare unit

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform mode[prl] :: unit = `"Unit"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext Unit
 * by unitFormation
 *)
prim unitFormation 'H : : sequent ['ext] { 'H >- univ[@i:l] } = unit

(*
 * H >- Unit = Unit in Ui ext Ax
 * by unitEquality
 *)
prim unitEquality 'H : : sequent ['ext] { 'H >- unit = unit in univ[@i:l] } = it

(*
 * H >- Ui ext Unit
 * by unitFormation
 *)
prim unit_memberFormation 'H : : sequent ['ext] { 'H >- unit } = it

(*
 * H >- Unit = Unit in Ui ext Ax
 * by unitEquality
 *)
prim unit_memberEquality 'H : : sequent ['ext] { 'H >- it = it in unit } = it

(*
 * H; i:x:Unit; J >- C
 * by unitElimination i
 * H; i:x:Unit; J[it / x] >- C[it / x]
 *)
prim unitElimination 'H 'J :
   ('t : sequent['ext] { 'H; x: unit; 'J[it] >- 'C[it] }) -->
   sequent ['ext] { 'H; x: unit; 'J['x] >- 'C['x] } =
   't

(*
 * Squash elimination.
 *)
prim unit_squashElimination 'H :
   sequent [squash] { 'H >- unit } -->
   sequent ['ext] { 'H >- unit } =
   it

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Standard term.
 *)
let unit_term = << unit >>

(*
 * D
 *)
let d_unitT i p =
   let t = goal p in
   let count = num_hyps t in
      (if i = 0 then
          unit_memberFormation count
       else
          let i = get_pos_hyp_index i count in
             unitElimination (i - 1) (count - i - 1)) p

let d_resource = d_resource.resource_improve d_resource (unit_term, d_unitT)
let dT = d_resource.resource_extract d_resource

(*
 * EqCD.
 *)
let eqcd_unitT p =
   let count = num_hyps (goal p) in
      unitEquality count p

let eqcd_itT p =
   let count = num_hyps (goal p) in
      unit_memberEquality count p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (unit_term, eqcd_unitT)
let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (it_term, eqcd_itT)
let eqcdT = eqcd_resource.resource_extract eqcd_resource

(************************************************************************
 * SQUASH STABILITY                                                     *
 ************************************************************************)

(*
 * Unit is squash stable.
 *)
let squash_unit p =
   unit_squashElimination (hyp_count p) p

let squash_resource = squash_resource.resource_improve squash_resource (unit_term, squash_unit)

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of unit.
 *)
let inf_unit _ decl _ = decl, univ1_term

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (unit_term, inf_unit)

(*
 * Type of an equality is the type of the equality type.
 *)
let inf_it _ decl _ = decl, unit_term

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (it_term, inf_it)

(*
 * $Log$
 * Revision 1.2  1998/04/09 18:26:11  jyh
 * Working compiler once again.
 *
 * Revision 1.1  1997/08/06 16:18:47  jyh
 * This is an ocaml version with subtyping, type inference,
 * d and eqcd tactics.  It is a basic system, but not debugged.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
