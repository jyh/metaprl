(*
 * Functional Intermediate Representation formalized in MetaPRL.
 *
 * Terms to represent sets used in the MC FIR.
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
 * Author: Brian Emre Aydemir
 * Email:  emre@its.caltech.edu
 *)

include Base_theory
include Itt_bool
include Itt_list
include Itt_int_ext

open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Top_conversionals

(*************************************************************************
 * Declarations.
 *************************************************************************)

(* Closed intervals. *)
declare interval{ 'left; 'right }

(* int and rawint sets. *)
declare int_set{ 'intervals }
declare rawint_set{ 'precision; 'sign; 'intervals }

(* Membership tests. *)
declare in_interval{ 'num; 'interval }
declare is_member{ 'num; 'set }

(*************************************************************************
 * Display forms.
 *************************************************************************)

(* Closed intervals. *)

dform interval_df : except_mode[src] :: interval{ 'left; 'right }  =
   lzone `"[" slot{'left} `"," slot{'right} `"]" ezone

(* int and rawint sets. *)

dform int_set_df : except_mode[src] :: int_set{ 'intervals } =
   pushm[0] szone push_indent `"int_set(" hspace
   szone slot{'intervals} ezone popm hspace
   `")" ezone popm
dform rawint_set_df : except_mode[src] ::
   rawint_set{ 'precision; 'sign; 'intervals } =
   pushm[0] szone push_indent `"rawint_set(" hspace
   szone slot{'precision} `"," hspace slot{'sign} `"," ezone popm
   push_indent hspace
   szone slot{'intervals} ezone popm hspace
   `")" ezone popm

(* Membership tests. *)

dform in_interval_df : except_mode[src] :: in_interval{'num; 'interval} =
   lzone slot{'num} Nuprl_font!member slot{'interval} ezone
dform member_df : except_mode[src] :: is_member{ 'num; 'set } =
   pushm[0] szone slot{'num} `" " Nuprl_font!member hspace
   szone slot{'set} ezone
   ezone popm

(*************************************************************************
 * Rewrites.
 *************************************************************************)

prim_rw reduce_in_interval :
   in_interval{ 'num; interval{ 'left; 'right } } <-->
   band{ le_bool{ 'left; 'num }; le_bool{ 'num; 'right } }

prim_rw reduce_is_member_int :
   is_member{ 'num; int_set{ 'intervals } } <-->
   list_ind{ 'intervals;
             bfalse;
             h, t, f. bor{ in_interval{ 'num; 'h }; 'f } }

prim_rw reduce_is_member_rawint :
   is_member{ 'num; rawint_set{ 'precision; 'sign; 'intervals } } <-->
   list_ind{ 'intervals;
             bfalse;
             h, t, f. bor{ in_interval{ 'num; 'h }; 'f } }

let reduce_is_member =
   repeatC (firstC [
      reduce_in_interval;
      reduceTopC;
      reduce_is_member_int;
      reduce_is_member_rawint
   ] )

(*************************************************************************
 * Term operations.
 *************************************************************************)

let interval_term = << interval{ 'left; 'right } >>
let interval_opname = opname_of_term interval_term
let is_interval_term = is_dep0_dep0_term interval_opname
let mk_interval_term = mk_dep0_dep0_term interval_opname
let dest_interval_term = dest_dep0_dep0_term interval_opname

let int_set_term = << int_set{ 'intervals } >>
let int_set_opname = opname_of_term int_set_term
let is_int_set_term = is_dep0_term int_set_opname
let mk_int_set_term = mk_dep0_term int_set_opname
let dest_int_set_term = dest_dep0_term int_set_opname

let rawint_set_term = << rawint_set{ 'precision; 'sign; 'intervals } >>
let rawint_set_opname = opname_of_term rawint_set_term
let is_rawint_set_term = is_dep0_dep0_dep0_term rawint_set_opname
let mk_rawint_set_term = mk_dep0_dep0_dep0_term rawint_set_opname
let dest_rawint_set_term = dest_dep0_dep0_dep0_term rawint_set_opname
