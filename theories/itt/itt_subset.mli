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
   sequent { <H> >- "type"{'A} } -->
   sequent { <H> >- "type"{'B} } -->
   sequent { <H> >- "type"{.'A subset 'B} }

rule subset_intro  :
   [wf] sequent { <H> >- 'A subtype 'B } -->
   [main] sequent { <H>; a: 'A; b: 'B; u: 'a = 'b in 'B >- 'b in 'A } -->
   sequent { <H> >- 'A subset 'B }

rule subset_sqstable  :
   sequent { <H> >- squash{'A subset 'B} } -->
   sequent { <H> >- 'A subset 'B }

rule subset_is_subtype  :
   sequent { <H> >- 'A subset 'B } -->
   sequent { <H> >- 'A subtype 'B }

rule use_subset  'A :
   sequent { <H> >- 'A subset 'B } -->
   sequent { <H> >- 'x = 'y in 'A } -->
   sequent { <H> >- 'x = 'y in 'B }

rule use_superset1  'B :
   sequent { <H> >- 'A subset 'B } -->
   sequent { <H> >- 'x in 'A } -->
   sequent { <H> >- 'x = 'y in 'B } -->
   sequent { <H> >- 'x = 'y in 'A }

rule use_superset2  'B :
   sequent { <H> >- 'A subset 'B } -->
   sequent { <H> >- 'y in 'A } -->
   sequent { <H> >- 'x = 'y in 'B } -->
   sequent { <H> >- 'x = 'y in 'A }

rule use_superset 'B 'y:
   sequent { <H> >- 'A subset 'B } -->
   sequent { <H> >- 'y in 'A } -->
   sequent { <H> >- 'x = 'y in 'B } -->
   sequent { <H> >- 'x  in 'A }

rule subsetTypeRight  'B :
   sequent { <H> >- 'A subset 'B } -->
   sequent { <H> >- "type"{'A} }

rule subsetTypeLeft  'A :
   sequent { <H> >- 'A subset 'B }  -->
   sequent { <H> >- "type"{'B} }

rule member_wf :
   sequent { <H> >- 'a in 'B } -->
   sequent { <H> >- "type"{'A} } -->
   sequent { <H> >- "type"{'a in 'A subset 'B} }

rule member_intro :
   sequent { <H> >- 'a in 'A } -->
   sequent { <H> >- 'A subset 'B } -->
   sequent { <H> >- 'a in 'A subset 'B }
      
rule member_elim 'H :
   sequent { <H>; u: 'a in 'A; v: 'A subset 'B; <J> >- 'C } --> 
   sequent { <H>; u: 'a in 'A subset 'B; <J> >- 'C  }
