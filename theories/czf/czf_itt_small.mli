(*
 * Small type is used to index the set w-type.
 * The small type is just U1.
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
 *)

include Itt_theory

open Tactic_type.Tacticals
open Tactic_type.Conversionals

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*
 * These are the small types from which sets are built.
 *    small: the type of small propositions
 *    small_type{'t}: 't = 't in small
 *)
declare small
declare small_type{'t}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

rewrite unfold_small : small <--> univ[1:l]
rewrite unfold_small_type : small_type{'t} <--> ('t = 't in small)

val fold_small : conv
val fold_small_type : conv

(************************************************************************
 * SMALL TYPE RULES                                                     *
 ************************************************************************)

rule small_type 'H :
   sequent ['ext] { 'H >- "type"{small} }

rule small_type_type 'H :
   sequent [squash] { 'H >- small_type{'x} } -->
   sequent ['ext] { 'H >- "type"{'x} }

(*
 * These are the types in the small universe.
 *)
rule void_small 'H :
   sequent ['ext] { 'H >- small_type{void} }

rule unit_small 'H :
   sequent ['ext] { 'H >- small_type{unit} }

rule int_small 'H :
   sequent ['ext] { 'H >- small_type{int} }

rule dfun_small 'H 'z :
   sequent ['ext] { 'H >- small_type{'A} } -->
   sequent ['ext] { 'H; z: 'A >- small_type{'B['z]} } -->
   sequent ['ext] { 'H >- small_type{. a: 'A -> 'B['a]} }

rule fun_small 'H :
   sequent ['ext] { 'H >- small_type{'A} } -->
   sequent ['ext] { 'H >- small_type{'B} } -->
   sequent ['ext] { 'H >- small_type{. 'A -> 'B} }

rule dprod_small 'H 'z :
   sequent ['ext] { 'H >- small_type{'A} } -->
   sequent ['ext] { 'H; z: 'A >- small_type{'B['z]} } -->
   sequent ['ext] { 'H >- small_type{. a: 'A * 'B['a]} }

rule prod_small 'H :
   sequent ['ext] { 'H >- small_type{'A} } -->
   sequent ['ext] { 'H >- small_type{'B} } -->
   sequent ['ext] { 'H >- small_type{. 'A * 'B} }

rule union_small 'H :
   sequent ['ext] { 'H >- small_type{'A} } -->
   sequent ['ext] { 'H >- small_type{'B} } -->
   sequent ['ext] { 'H >- small_type{. 'A + 'B} }

rule equal_small 'H :
   sequent ['ext] { 'H >- small_type{'A} } -->
   sequent ['ext] { 'H >- 'a = 'a in 'A } -->
   sequent ['ext] { 'H >- 'b = 'b in 'A } -->
   sequent ['ext] { 'H >- small_type{. 'a = 'b in 'A} }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * small_type{'x} => type{'x}
 *)
val smallTypeT : tactic

val smallAssumT : int -> tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
