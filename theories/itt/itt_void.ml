(*
 * Here are rules for the Void base type.
 * Void has no elements.  Its propositional
 * interpretation is "False".
 *
 *)

open Debug
open Sequent
open Term
open Resource

include Tactic_type
include Itt_equal
include Itt_subtype

(*
 * incr_debug_level DebugMessage
 * debug_string DebugLoad "Loading itt_void..."
 *)

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare void

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform mode[prl] :: void = `"Void"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext Void
 * by voidFormation
 *)
prim voidFormation 'H : : sequent ['ext] { 'H >- univ[@i:l] } = void

(*
 * H >- Void = Void in Ui ext Ax
 * by voidEquality
 *)
prim voidEquality 'H : : sequent ['ext] { 'H >- void = void in univ[@i:l] } = it

(*
 * H, i:x:Void, J >- C
 * by voidElimination i
 *)
prim voidElimination 'H 'J : : sequent ['ext] { 'H; x: void; 'J['x] >- 'C['x] } = it

(*
 * Squash stability.
 *)
prim void_squashElimination 'H : sequent [squash] { 'H >- void } :
   sequent ['ext] { 'H >- void } = it

(*
 * Subtyping.
 *)
prim void_subtype 'H : :
   sequent ['ext] { 'H >- subtype{void; 'T} } =
   it

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Standard term.
 *)
let void_term = << void >>

(*
 * D
 *)
let d_voidT i p =
   if i = 0 then
      failwith "can't prove void"
   else
      let t = goal p in
      let count = num_hyps t in
      let i = get_pos_hyp_index i count in
         voidElimination (i - 1) (count - i - 1) p

let d_resource = d_resource.resource_improve d_resource (void_term, d_voidT)
let dT = d_resource.resource_extract d_resource

(*
 * EqCD.
 *)
let eqcd_voidT p =
   let count = num_hyps (goal p) in
      voidEquality count p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (void_term, eqcd_voidT)
let eqcdT = eqcd_resource.resource_extract eqcd_resource

(************************************************************************
 * SQUASH STABILITY                                                     *
 ************************************************************************)

(*
 * Void is squash stable.
 *)
let squash_void p =
   void_squashElimination (hyp_count p) p

let squash_resource = squash_resource.resource_improve squash_resource (void_term, squash_void)

(************************************************************************
 * SUBTYPING                                                            *
 ************************************************************************)

let void_sub p =
   void_subtype (hyp_count p) p

let sub_resource =
   sub_resource.resource_improve
   sub_resource
   (RLSubtype ([void_term, << 'a >>], void_sub))

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of void.
 *)
let inf_void _ decl _ = decl, univ1_term

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (void_term, inf_void)

(*
 * $Log$
 * Revision 1.3  1998/04/09 18:26:11  jyh
 * Working compiler once again.
 *
 * Revision 1.2  1997/08/06 16:18:48  jyh
 * This is an ocaml version with subtyping, type inference,
 * d and eqcd tactics.  It is a basic system, but not debugged.
 *
 * Revision 1.1  1997/04/28 15:52:31  jyh
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
 * Revision 1.8  1996/09/25 22:52:14  jyh
 * Initial "tactical" commit.
 *
 * Revision 1.7  1996/05/21 02:18:33  jyh
 * This is a semi-working version before Wisconsin vacation.
 *
 * Revision 1.6  1996/04/11 13:34:53  jyh
 * This is the final version with the old syntax for terms.
 *
 * Revision 1.5  1996/03/28 02:51:47  jyh
 * This is an initial version of the type theory.
 *
 * Revision 1.4  1996/03/05 19:59:54  jyh
 * Version just before LogicalFramework.
 *
 * Revision 1.3  1996/02/15 20:36:45  jyh
 * Upgrading prlcomp.
 *
 * Revision 1.2  1996/02/13 21:36:13  jyh
 * Intermediate checkin while matching is bing added to the refiner.
 *
 * Revision 1.1  1996/02/10 20:18:18  jyh
 * Initiali checking for base+itt refiners.
 *
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
