(*
 * Equality type.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/index.html for information on Nuprl,
 * OCaml, and more information about this system.
 *
 * Copyright (C) 1998 Jason Hickey, Cornell University
 * 
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
 * 
 * Author: Jason Hickey
 * jyh@cs.cornell.edu
 *
 *)

include Tacticals
include Base_theory
include Itt_squash

open Printf
open Mp_debug
open Opname
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermType
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan
open Refiner.Refiner.RefineError
open Rformat
open Simple_print
open Term_stable
open Mp_resource

open Tacticals
open Sequent
open Mptop

open Base_auto_tactic

(*
 * Show that the file is loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Itt_equal%t" eflush

let debug_eqcd =
   create_debug (**)
      { debug_name = "eqcd";
        debug_description = "display eqcd operations";
        debug_value = false
      }

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "type"{'a}
declare univ[@i:l]
declare equal{'T; 'a; 'b}
declare it

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

prec prec_type
prec prec_equal

dform equal_df1 : parens :: "prec"[prec_equal] :: equal{'T; 'a; 'b} =
   szone pushm slot{'a} space `"= " slot{'b} space `"in " slot{'T} popm ezone
dform it_df1 : mode[prl] :: it = cdot

dform type_prl_df1 : parens :: "prec"[prec_type] :: mode[prl] :: "type"{'a} =
   slot{'a} " " `"Type"

dform term_df2 : mode[prl] :: univ[@i:l] =
   mathbbU `"[" slot[@i:l] `"]"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Typehood is equality.
 *)
prim equalityAxiom 'H 'J : :
   sequent ['ext] { 'H; x: 'T; 'J['x] >- 'x = 'x in 'T } =
   it

(*
 * Reflexivity.
 *)
prim equalityRef 'H 'y :
   sequent ['ext] { 'H >- 'x = 'y in 'T } -->
   sequent ['ext] { 'H >- 'x = 'x in 'T } =
   it

(*
 * Symettry.
 *)
prim equalitySym 'H :
   sequent ['ext] { 'H >- 'y = 'x in 'T } -->
   sequent ['ext] { 'H >- 'x = 'y in 'T } =
   it

(*
 * Transitivity.
 *)
prim equalityTrans 'H 'z :
   sequent ['ext] { 'H >- 'x = 'z in 'T } -->
   sequent ['ext] { 'H >- 'z = 'y in 'T } -->
   sequent ['ext] { 'H >- 'x = 'y in 'T } =
   it

(*
 * H >- Ui ext a = b in T
 * by equalityFormation T
 *
 * H >- T ext a
 * H >- T ext b
 *)
prim equalityFormation 'H 'T :
   ('a : sequent ['ext] { 'H >- 'T }) -->
   ('b : sequent ['ext] { 'H >- 'T }) -->
   sequent ['ext] { 'H >- univ[@i:l] } =
   'a = 'b in 'T

(*
 * H >- (a1 = b1 in T1) = (a2 = b2 in T2)
 * by equalityEquality
 *
 * H >- T1 = T2 in Ui
 * H >- a1 = a2 in T1
 * H >- b1 = b2 in T1
 *)
prim equalityEquality 'H :
   sequent [squash] { 'H >- 'T1 = 'T2 in univ[@i:l] }
   sequent [squash] { 'H >- 'a1 = 'a2 in 'T1 }
   sequent [squash] { 'H >- 'b1 = 'b2 in 'T2 } :
   sequent ['ext] { 'H >- ('a1 = 'b1 in 'T1) = ('a2 = 'b2 in 'T2) in univ[@i:l] } =
   it

(*
 * Typehood.
 *)
prim equalityType 'H :
   sequent [squash] { 'H >- 'a = 'a in 'T } -->
   sequent [squash] { 'H >- 'b = 'b in 'T } -->
   sequent ['ext] { 'H >- "type"{. 'a = 'b in 'T } } =
   it

interactive equalityType2 'H :
   sequent [squash] { 'H >- 'a = 'a in 'T } -->
   sequent ['ext] { 'H >- "type"{. 'a = 'a in 'T } }

(*
 * H >- it = it in (a = b in T)
 * by axiomEquality
 *
 * H >- a = b in T
 *)
prim axiomEquality 'H :
   sequent [squash] { 'H >- 'a = 'b in 'T } :
   sequent ['ext] { 'H >- it = it in ('a = 'b in 'T) } =
   it

(*
 * H, x: a = b in T, J[x] >- C[x]
 * by equalityElimination i
 *
 * H, x: a = b in T; J[it] >- C[it]
 *)
prim equalityElimination 'H 'J :
   ('t : sequent ['ext] { 'H; x: 'a = 'b in 'T; 'J[it] >- 'C[it] }) :
   sequent ['ext] { 'H; x: 'a = 'b in 'T; 'J['x] >- 'C['x] } =
   't

(*
 * H >- T = T in type
 * by typeEquality
 *
 * H >- T
 *)
prim typeEquality 'H :
   sequent [squash] { 'H >- 'T } :
   sequent ['ext] { 'H >- "type"{'T} } =
   it

(*
 * Squash elim.
 *)
prim equality_squashElimination 'H :
   sequent [squash] { 'H >- 'a = 'b in 'T } -->
   sequent ['ext] { 'H >- 'a = 'b in 'T } =
   it

prim type_squashElimination 'H :
   sequent [squash] { 'H >- "type"{'T} } -->
   sequent ['ext] { 'H >- "type"{'T} } =
   it

(*
 * There should be only one param, of String type.
 * Get it.
 *)
let dest_level_param t =
   let { term_op = op } = dest_term t in
      match dest_op op with
         { op_params = [param] } ->
            begin
               match dest_param param with
                  Level s -> s
                | _ ->
                     raise (RefineError ("dest_level_param", TermMatchError (t, "param type")))
            end
       | { op_params = [] } ->
            raise (RefineError ("dest_level_param", TermMatchError (t, "no params")))
       | _ ->
            raise (RefineError ("dest_level_param", TermMatchError (t, "too many params")))

(* Cumulativity over universes *)
mlterm cumulativity{univ[@j:l]; univ[@i:l]} =
   let i = dest_level_param <:con< univ[@i:l] >> in
   let j = dest_level_param <:con< univ[@j:l] >> in
      if level_cumulativity j i then
         []
      else
         raise (RefineError ("cumulativity", StringError "failed"))

 | fun _ extracts ->
      << it >>, extracts

(*
 * H >- Uj = Uj in Ui
 * by universeEquality (side (j < i))
 *)
prim universeEquality 'H :
   cumulativity{univ[@j:l]; univ[@i:l]} :
   sequent ['ext] { 'H >- univ[@j:l] = univ[@j:l] in univ[@i:l] } =
  it

(*
 * Universe is a type.
 *)
prim universeType 'H : :
   sequent ['ext] { 'H >- "type"{univ[@l:l]} } =
   it

(*
 * Anything in a universe is a type.
 *)
prim universeMemberType 'H univ[@i:l] :
   sequent [squash] { 'H >- 'x = 'x in univ[@i:l] } -->
   sequent ['ext] { 'H >- "type"{'x} } =
   it

(*
 * Derived form for known membership.
 *)
interactive universeAssumType 'H 'J : :
   sequent ['ext] { 'H; x: univ[@l:l]; 'J['x] >- "type"{'x} }

(*
 * H >- Ui ext Uj
 * by universeFormation
 *)
prim universeFormation 'H univ[@j:l] :
   cumulativity{univ[@j:l]; univ[@i:l]} :
   sequent ['ext] {'H >- univ[@i:l] } =
   univ[@j:l]

(*
 * Squash from any.
 *)
prim squashFromAny 'H 'ext :
   sequent ['ext] { 'H >- 'T } -->
   sequent [squash] { 'H >- 'T } =
   it

(************************************************************************
 * PRIMITIVES                                                           *
 ************************************************************************)

(*
 * Primitives.
 *)
let equal_term = << 'a = 'b in 'c >>
let equal_opname = opname_of_term equal_term
let is_equal_term = is_dep0_dep0_dep0_term equal_opname
let dest_equal = dest_dep0_dep0_dep0_term equal_opname
let mk_equal_term = mk_dep0_dep0_dep0_term equal_opname

let type_term = << "type"{'t} >>
let type_opname = opname_of_term type_term
let is_type_term = is_dep0_term type_opname
let mk_type_term = mk_dep0_term type_opname
let dest_type_term = dest_dep0_term type_opname

let univ_term = << univ[@i:l] >>
let univ1_term = << univ[1:l] >>
let univ_opname = opname_of_term univ_term
let is_univ_term = TermOp.is_univ_term univ_opname
let dest_univ = TermOp.dest_univ_term univ_opname
let mk_univ_term = TermOp.mk_univ_term univ_opname

let it_term = << it >>

(************************************************************************
 * EQCD TACTIC                                                          *
 ************************************************************************)

(*
 * EQCD resource.
 * Use simple table.
 *)
type eqcd_data = tactic term_stable

resource (term * tactic, tactic, eqcd_data) eqcd_resource

(*
 * Extract an EQCD tactic from the data.
 * The tactic checks for an optable.
 *)
let extract_data base =
   let tbl = sextract base in
   let eqcd p =
      let t = concl p in
      let _, l, _ = dest_equal t in
         try
            (* Find and apply the right tactic *)
            if !debug_eqcd then
               eprintf "Itt_equal.eqcd: looking up %s%t" (SimplePrint.string_of_opname (opname_of_term l)) eflush;
            let tac = slookup tbl l in
               if !debug_eqcd then
                  eprintf "Itt_equal.eqcd: found a tactic for %s%t" (SimplePrint.string_of_opname (opname_of_term l)) eflush;
               tac p
         with
            Not_found ->
               raise (RefineError ("eqcd", StringTermError ("EQCD tactic doesn't know about ", l)))
   in
      eqcd

(*
 * Keep a list of resources for lookup by the toploop.
 *)
let resources = ref []

let save name rsrc =
   resources := (name, rsrc) :: !resources

let get_resource name =
   let rec search = function
      (name', rsrc) :: tl ->
         if name' = name then
            rsrc
         else
            search tl
    | [] ->
         raise Not_found
   in
      search !resources

(*
 * Wrap up the joiner.
 *)
let rec join_resource { resource_data = data1 } { resource_data = data2 } =
   { resource_data = join_stables data1 data2;
     resource_join = join_resource;
     resource_extract = extract_resource;
     resource_improve = improve_resource;
     resource_close = close_resource
   }

and extract_resource { resource_data = data } =
   extract_data data

and improve_resource { resource_data = data } (t, tac) =
   { resource_data = sinsert data t tac;
     resource_join = join_resource;
     resource_extract = extract_resource;
     resource_improve = improve_resource;
     resource_close = close_resource
   }

and close_resource rsrc _ =
   rsrc

(*
 * Resource.
 *)
let eqcd_resource =
   { resource_data = new_stable ();
     resource_join = join_resource;
     resource_extract = extract_resource;
     resource_improve = improve_resource;
     resource_close = close_resource
   }

(*
 * Resource argument.
 *)
let eqcdT p =
   Sequent.get_tactic_arg p "eqcd" p

(************************************************************************
 * D TACTIC                                                             *
 ************************************************************************)

(*
 * D tactic.
 *)
let d_equalT i p =
   if i = 0 then
      eqcdT p
   else
      let j, k = hyp_indices p i in
         equalityElimination j k p

let d_resource = d_resource.resource_improve d_resource (equal_term, d_equalT)

(*
 * Typehood.
 *)
let d_equal_typeT i p =
   if i = 0 then
      let len = hyp_count_addr p in
         (equalityType2 len orelseT equalityType len) p
   else
      raise (RefineError ("d_equal_typeT", StringError "no elimination form"))

let equal_type_term = << "type"{. 'a = 'b in 'T } >>

let d_resource = d_resource.resource_improve d_resource (equal_type_term, d_equal_typeT)

(*
 * Turn a eqcd tactic into a d tactic.
 *)
let d_wrap_eqcd eqcdT i p =
   if i = 0 then
      eqcdT p
   else
      d_equalT i p

(*
 * Universe is a type.
 *)
let d_univ_typeT i p =
   if i = 0 then
      universeType (hyp_count_addr p) p
   else
      raise (RefineError ("d_univ_typeT", StringError "no elimination form"))

let univ_type_term = << "type"{univ[@l:l]} >>

let d_resource = d_resource.resource_improve d_resource (univ_type_term, d_univ_typeT)

(************************************************************************
 * EQCD                                                                 *
 ************************************************************************)

(*
 * EQCD tactic.
 *)
let eqcd_univT p =
   universeEquality (hyp_count_addr p) p

let eqcd_itT p =
   axiomEquality (hyp_count_addr p) p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (univ_term, eqcd_univT)
let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (it_term, eqcd_itT)

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of a universe is incremented by one.
 *)
let inf_univ _ decl t =
   let le = dest_univ t in
      decl, mk_univ_term (incr_level_exp le)

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (univ_term, inf_univ)

(*
 * Type of an equality is the type of the equality type.
 *)
let inf_equal inf decl t =
   let ty, _, _ = dest_equal t in
      inf decl ty

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (equal_term, inf_equal)

(************************************************************************
 * SQUASH STABILITY                                                     *
 ************************************************************************)

(*
 * Equality is squash stable.
 *)
let squash_equalT p =
   equality_squashElimination (hyp_count_addr p) p

let squash_resource = squash_resource.resource_improve squash_resource (equal_term, squash_equalT)

let squash_typeT p =
   type_squashElimination (hyp_count_addr p) p

let squash_resource = squash_resource.resource_improve squash_resource (type_term, squash_typeT)

let unsquashT v p =
   squashFromAny (Sequent.hyp_count_addr p) v p

(************************************************************************
 * OTHER TACTICS                                                        *
 ************************************************************************)

(*
 * H, x:T, J >- x = x in T
 *)
let equalAssumT i p =
   let i, j = hyp_indices p i in
      equalityAxiom i j p

(*
 * Reflexivity.
 *)
let equalRefT t p =
   equalityRef (hyp_count_addr p) t p

(*
 * Symettry.
 *)
let equalSymT p =
   equalitySym (hyp_count_addr p) p

(*
 * Transitivity.
 *)
let equalTransT t p =
   equalityTrans (hyp_count_addr p) t p

(*
 * Membership in a type.
 *)
let univTypeT t p =
   universeMemberType (hyp_count_addr p) t p

(*
 * Assumed membership.
 *)
let univAssumT i p =
   let j, k = hyp_indices p i in
      universeAssumType j k p

(*
 * Typehood from truth.
 *)
let typeAssertT p =
   typeEquality (hyp_count_addr p) p

(*
 * Automation.
 *)
let triv_equalT i =
   equalAssumT i orelseT univAssumT i

let trivial_resource =
   trivial_resource.resource_improve trivial_resource (**)
      { auto_name = "triv_equalT";
        auto_prec = trivial_prec;
        auto_tac = onSomeHypT triv_equalT
      }

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
