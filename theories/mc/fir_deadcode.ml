(*
 * Functional Intermediate Representation formalized in MetaPRL.
 *
 * Implement deadcode elimination.
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

include Fir_exp
include Fir_eval

open Top_conversionals
open Tactic_type.Conversionals

(*************************************************************************
 * Rewrites.
 *************************************************************************)

(* Primitive operations. *)

interactive_rw reduce_letUnop_deadcode :
   letUnop{ 'op; 'ty; 'a1; v. 'exp } <-->
   'exp
interactive_rw reduce_letBinop_deadcode :
   letBinop{ 'op; 'ty; 'a1; 'a2; v. 'exp } <-->
   'exp

(* Allocation. *)

interactive_rw reduce_allocTuple_deadcode :
   letAlloc{ allocTuple{ 'ty; 'atom_list }; v. 'exp } <-->
   'exp
interactive_rw reduce_allocArray_deadcode :
   letAlloc{ allocArray{ 'ty; 'atom_list }; v. 'exp } <-->
   'exp

(* Subscripting. *)

interactive_rw reduce_letSubscript_deadcode :
   letSubscript{ 'subop; 'ty; 'var; 'index; v. 'exp } <-->
   'exp

(*************************************************************************
 * Automation.
 *************************************************************************)

let firDeadcodeElimT i =
   rwh (repeatC (applyAllC [
      reduce_letUnop_deadcode;
      reduce_letBinop_deadcode;

      reduce_allocTuple_deadcode;
      reduce_allocArray_deadcode;

      reduce_letSubscript_deadcode
   ] )) i
