(*
 * Functional Intermediate Representation formalized in MetaPRL.
 *
 * Define terms to represent Rawint sets.
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

(*************************************************************************
 * Declarations.
 *************************************************************************)

(* Intervals. *)
declare raw_interval{ 'left; 'right }

(* The set. *)
declare rawint_set{ 'intervals }

(*************************************************************************
 * Display forms.
 *************************************************************************)

(* Intervals. *)
dform raw_interval_df : except_mode[src] :: raw_interval{ 'l; 'r } =
   lzone `"[" slot{'l} `", " slot{'r} `"]" ezone

(* The set. *)
dform rawint_set_df : except_mode[src] :: rawint_set{ 'intervals } =
   pushm[0] szone `"rawint_set(" slot{'intervals} `")" ezone popm
