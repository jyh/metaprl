(*
 * Subsets.
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
 * Author: Xin Yu
 * xiny@cs.caltech.edu
 *
 *)

extends Itt_equal
extends Itt_subtype
extends Itt_struct
extends Itt_logic
extends Itt_singleton
extends Itt_squash
extends Itt_isect
extends Itt_bool
extends Itt_int_base
extends Itt_ext_equal

open Refiner.Refiner.Term

open Tactic_type.Sequent
open Tactic_type.Tacticals

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare  "subset"{'A; 'B} 

declare  member{'a; 'A; 'B}


    
(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

topval unfold_subset : conv
topval fold_subset : conv

val is_subset_term : term -> bool
val dest_subset : term -> term * term
val mk_subset_term : term -> term -> term

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

rule subset_wf :
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent [squash] { 'H >- "type"{'B} } -->
   sequent ['ext] { 'H >- "type"{.'A subset 'B} }

rule subset_intro  :
   [wf] sequent [squash] { 'H >- 'A subtype 'B } -->
   [main] sequent [squash] {'H; a: 'A; b: 'B; u: 'a = 'b in 'B >- 'b in 'A } -->
   sequent ['ext] { 'H >- 'A subset 'B }



      
rule subset_sqstable  :
   sequent [squash] { 'H >- squash{'A subset 'B} } -->
   sequent ['ext] { 'H >- 'A subset 'B }


      
rule subset_is_subtype  :
   sequent [squash] { 'H >- 'A subset 'B } -->
   sequent ['ext] { 'H >- 'A subtype 'B }



rule use_subset  'A :
   sequent [squash] { 'H >- 'A subset 'B } -->
   sequent [squash] { 'H >- 'x = 'y in 'A } -->
   sequent ['ext] { 'H >- 'x = 'y in 'B }


rule use_superset1  'B :
   sequent [squash] { 'H >- 'A subset 'B } -->
   sequent [squash] { 'H >- 'x in 'A } -->
   sequent [squash] { 'H >- 'x = 'y in 'B } -->
   sequent ['ext] { 'H >- 'x = 'y in 'A }

rule use_superset2  'B :
   sequent [squash] { 'H >- 'A subset 'B } -->
   sequent [squash] { 'H >- 'y in 'A } -->
   sequent [squash] { 'H >- 'x = 'y in 'B } -->
   sequent ['ext] { 'H >- 'x = 'y in 'A }


rule use_superset 'B 'y:
   sequent [squash] { 'H >- 'A subset 'B } -->
   sequent [squash] { 'H >- 'y in 'A } -->
   sequent [squash] { 'H >- 'x = 'y in 'B } -->
   sequent ['ext] { 'H >- 'x  in 'A }



      
rule subsetTypeRight  'B :
   sequent [squash] { 'H >- 'A subset 'B } -->
   sequent ['ext] { 'H >- "type"{'A} }

rule subsetTypeLeft  'A :
   sequent [squash] { 'H >- 'A subset 'B }  -->
   sequent ['ext] { 'H >- "type"{'B} }



      
rule member_wf :
   sequent [squash] { 'H >- 'a in 'B } -->
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H >- "type"{'a in 'A subset 'B} }


      
rule member_intro   :
   sequent [squash] { 'H >- 'a in 'A } -->
   sequent [squash] { 'H >- 'A subset 'B } -->
   sequent ['ext] { 'H >- 'a in 'A subset 'B }

      
rule member_elim 'H :
   sequent ['ext] { 'H; u: 'a in 'A; u: 'A subset 'B; 'J >- 'C } --> 
   sequent ['ext] { 'H; u: 'a in 'A subset 'B; 'J >- 'C  }


      
