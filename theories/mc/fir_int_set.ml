(*
 * Functional Intermediate Representation formalized in MetaPRL.
 *
 * Define a limited version of the int_set type from the FIR.
 * It's limited in the sense that I don't implement all the
 *    possible operations that the FIR int_set has.
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
include Itt_theory

(*************************************************************************
 * Declarations.
 *************************************************************************)

(* Intervals. *)
declare interval{ 'left; 'right }

(* The set. *)
declare int_set{ 'intervals }

(* Short form. *)
declare int_set{ 'a; 'b }

(* Member test. *)
define unfold_in_interval :
   in_interval{ 'num; interval{'l; 'r} } <-->
   band{ le_bool{'l; 'num}; le_bool{'num; 'r} }
declare member{ 'num; 'int_set }

(*************************************************************************
 * Display.
 *************************************************************************)

(* Intervals. *)
dform interval_df : except_mode[src] :: interval{ 'l; 'r }  =
   lzone `"[" slot{'l} `"," slot{'r} `"]" ezone

(* The set. *)
dform int_set_df1 : except_mode[src] :: int_set{ 'intervals } =
   pushm[0] szone `"int_set(" slot{'intervals} `")" ezone popm

(* Short form. *)
dform int_set_df2 : except_mode[src] :: int_set{ 'a; 'b } =
   `"int_set[[" slot{'a} `", " slot{'b} `"]]"

(* Member test. *)
dform in_interval_df : except_mode[src] :: in_interval{'num; 'interval} =
   lzone slot{'num} `" " Nuprl_font!member `" " slot{'interval} ezone
dform member_df : except_mode[src] :: member{ 'num; 'int_set } =
   szone slot{'num} space Nuprl_font!member space slot{'int_set} ezone

(*************************************************************************
 * Rewrites.
 *************************************************************************)

prim_rw reduce_member_cons :
   member{ 'num; int_set{ cons{'i; 'el} } } <-->
   ifthenelse{ in_interval{ 'num; 'i }; btrue; member{ 'num; int_set{'el} } }
prim_rw reduce_member_nil : member{ 'num; int_set{ nil } } <--> bfalse

prim_rw reduce_short_int_set :
   int_set{ 'a; 'b } <-->
   int_set{ cons{ interval{'a; 'b}; nil } }

(*************************************************************************
 * Automation.
 *************************************************************************)

let resource reduce += [
   << in_interval{ 'num; interval{'l; 'r} } >>, unfold_in_interval;
   << member{ 'num; int_set{ cons{'i; 'el} } } >>, reduce_member_cons;
   << member{ 'num; int_set{ nil } } >>, reduce_member_nil;
   << int_set{ 'a; 'b } >>, reduce_short_int_set
]
