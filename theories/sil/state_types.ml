(*
 * Types for Simple Imperative Programs.
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
 * Copyright (C) 1999 Jason Hickey, Cornell University
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

extends Sil_programs

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

declare int
declare union{'A; 'B}
declare prod{'A; v. 'B['v]}
declare ref{'A}
declare fun{'A; v. 'B['v]}

declare "type"{'A}
declare program{'A; 'S1; 'S2}
declare member{'A; 'e1}
declare equal{'A; 'e1; 'e2}
declare nequal{'A; 'e1; 'e2}
declare is_val{'A; 'e; 'S1}
declare equal_val{'A; 'e1; 'v1}
declare nequal_val{'A; 'e1; 'v1}

(************************************************************************
 * TYPING JUDGMENTS                                                     *
 ************************************************************************)

(*
 * Well-formedness of programs.
 *)
prim program_type :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H >- "type"{'S1} } -->
   [wf] sequent [squash] { 'H >- "type"{'S2} } -->
   sequent ['ext] { 'H >- "type"{program{'A; 'S1; 'S2}} }

(*
 * Value judgment.
 *)
prim_rw unfold_is_val : is_val{'A; 'e; 'S} <--> member{program{'A; 'S; 'S}; 'e}

(*
 * Numbers.
 *)
prim int_program_type :
   [wf] sequent [squash] { 'H >- "type"{'S1} } -->
   [wf] sequent [squash] { 'H >- "type"{'S2} } -->
   sequent ['ext] { 'H >- "type"{program{int_type; 'S1; 'S2}} }

prim number_program :
   [wf] sequent [squash] { 'H >- "type"{'S1} } -->
   sequent ['ext] { 'H >- member{program{int_type; 'S1; 'S1}; number[i:n]} }

prim add_program :
   [main] sequent [squash] { 'H >- member{program{int_type; 'S1; 'S2}; 'e1} } -->
   [main] sequent [squash] { 'H >- member{program{int_type; 'S2; 'S3}; 'e2} } -->
   sequent ['ext] { 'H >- member{program{int_type; 'S1; 'S3}; add{'e1; 's2}} }

prim sub_program :
   [main] sequent [squash] { 'H >- member{program{int_type; 'S1; 'S2}; 'e1} } -->
   [main] sequent [squash] { 'H >- member{program{int_type; 'S2; 'S3}; 'e2} } -->
   sequent ['ext] { 'H >- member{program{int_type; 'S1; 'S3}; sub{'e1; 's2}} }

prim if_program 'u :
   [main] sequent [squash] { 'H >- member{program{int_type; 'S1; 'S2}; 'e1} } -->
   [main] sequent [squash] { 'H >- member{program{int_type; 'S2; 'S3}; 'e2} } -->
   [main] sequent [squash] { 'H; u: equal_int{'S1; 'S2; 'S3; 'e1; 'e2} >- member{'C; 'e3} } -->
   [main] sequent [squash] { 'H; u: nequal_int{'S1; 'S2; 'S3; 'e1; 'e2} >- member{'C; 'e4} } -->
   sequent ['ext] { 'H >- member{'C; "if"{'e1; 'e2; 'e3; 'e4}} }

(*
 * Union types.
 *)
prim union_type_type :
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent [squash] { 'H >- "type"{'B} } -->
   sequent ['ext] { 'H >- "type"{union{'A; 'B}} }

prim inl_member :
   [wf] sequent [squash] { 'H >- "type"{'B} } -->
   [main] sequent [squash] { 'H >- member{'A; 'e1} } -->
   sequent ['ext] { 'H >- member{union{'A; 'B}; inl{'e1}} }

prim inr_member :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [main] sequent [squash] { 'H >- member{'B; 'e1} } -->
   sequent ['ext] { 'H >- member{union{'A; 'B}; inr{'e1}} }

prim decide_member :
   [wf] sequent [squash] { 'H >- member{union{'A; 'B}; 'e1} } -->
   [wf] sequent [squash] { 'H; x: 'A; w: equal{union{'A; 'B}; 'e1; inl{'x}} >- member{'C[inl{'x}]; 'e2['x]} } -->
   [wf] sequent [squash] { 'H; y: 'B; w: equal{union{'A; 'B}; 'e1; inr{'y}} >- member{'C[inr{'y}]; 'e2['y]} } -->
   sequent ['ext] { 'H >- member{'C['e1]; decide{'e1; x, 'e2['x]; y. 'e3['y]}} }

(*
 * Tuples.
 *)
prim prod_type :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H; v:'A >- "type"{'B['v]} } -->
   sequent ['ext] { 'H >- "type"{prod{'A; v. 'B['v]}} }

prim pair_program :
   [wf] sequent [squash] { 'H >- member{'A; 'e1} } -->
   [wf] sequent [squash] { 'H; v: 'A >- "type"{'B['v]} } -->
   [wf] sequent [squash] { 'H; v: 'A; w: equal{'A; 'e1; 'v} >- member{'B['v]; 'e2['v]} } -->
   sequent ['ext] { 'H >- member{prod{'A; v. 'B['v]}; pair{'e1; 'e2}} }

prim spread_program :
   [wf] sequent [squash] { 'H >- member{prod{'A; v. 'B['v]}; 'e1} } -->
   [wf] sequent [squash] { 'H; x: 'A; y: 'B['x]; w: equal{prod{'A; v. 'B['v]}; 'e1; pair{'x; 'y}} >- member{'C[pair{'x; 'y}]; 'e2['x; 'y]} } -->
   sequent ['ext] { 'H >- member{'C['e1]; spread{'e1; x, y. 'e2['x; 'y]}} }

(*
 * References.
 *)
prim ref_type :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H >- "type"{ref_type{'A}} }

prim ref_member :
   [wf] sequent [squash] { 'H >- member{'A; 'e1} } -->
   sequent ['ext] { 'H >- member{ref_type{'A}; ref{'e1}} }

prim deref_member :
   [wf] sequent [squash] { 'H >- member{ref_type{'A}; 'e1} } -->
   sequent ['ext] { 'H >- member{'A; deref{'e1}} }

prim assign_member :
   [wf] sequent [squash] { 'H >- member{program{ref_type{'A}; 'S1; 'S2}; 'e1} } -->
   [wf] sequent [squash] { 'H >- member{program{'B; 'S2; 'S3}; 'e2} } -->
   sequent ['ext] { 'H >- member{program{dot_type; 'S1; store_type{'S3; 'l; 'B}}; assign{'e1; 'e2}} }

(*
 * Functions.
 *)
prim fun_type :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H; v: 'A >- "type"{'B['v]} } -->
   sequent ['ext] { 'H >- "type"{fun{'A; v. 'B['v]}} }

prim lambda_member :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H; v: 'A >- member{'B['v]; 'e['v]} } -->
   sequent ['ext] { 'H >- member{fun{'A; u. 'B['u]}; lambda{v. 'e['v]}} }

prim apply_member :
   [wf] sequent [squash] { 'H >- member{."fun"{'A; u. 'B['u]}; 'e1} } -->
   [wf] sequent [squash] { 'H >- member{'A; 'e2} } -->
   sequent ['ext] { 'H >- member{'B['e2]; apply{'e1; 'e2}} }
(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
