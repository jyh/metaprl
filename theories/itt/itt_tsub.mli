(*
 * Difference of two types.
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

include Itt_equal
include Itt_logic


(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

declare tsub{'A; 'B}
declare tsub_any

prec prec_tsub

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Typehood.
 *)
rule tsubEquality 'H :
   sequent [squash] { 'H >- 'A1 = 'A2 in univ[@i:l] } -->
   sequent [squash] { 'H >- 'B1 = 'B2 in univ[@i:l] } -->
   sequent [squash] { 'H >- subtype{'B1; 'A1} } -->
   sequent ['ext] { 'H >- tsub{'A1; 'B1} = tsub{'A2; 'B2} in univ[@i:l] }

rule tsubType 'H :
   sequent [squash] { 'H >- subtype{'B; 'A} } -->
   sequent ['ext] { 'H >- "type"{tsub{'A; 'B}} }

(*
 * Membership.
 *)
rule tsubMemberEquality 'H 'x :
   sequent [squash] { 'H >- 'x1 = 'x2 in 'A } -->
   sequent [squash] { 'H >- subtype{'B; 'A} } -->
   sequent [squash] { 'H; x: 'x1 = 'x2 in 'B >- "false" } -->
   sequent ['ext] { 'H >- 'x1 = 'x2 in tsub{'A; 'B} }

(*
 * Elimination.
 *)
rule tsubElimination 'H 'J 'x 'y :
   sequent ['ext] { 'H; x: 'A; y: ('x = 'x in 'B) => "false"; 'J['x] >- 'C['x] } -->
   sequent ['ext] { 'H; x: tsub{'A; 'B}; 'J['x] >- 'C['x] }

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
