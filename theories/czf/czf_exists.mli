(*
 * Universal quantification.
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

extends Czf_wf;;
extends Czf_set;;
extends Czf_implies;;
extends Czf_member;;

declare "exists"{x. 'P};;
define bounded_exists_abs : "exists"{'y; x. 'P['x]} <--> "exists"{x. member{'x; 'y} => 'P['x]};;

(*
 * Bounded intro form.
 *
 * H >> exists x: A. B[x]
 * by bounded_exists_intro a
 * H >> B[a]
 * H >> member{a; A}
 * functionality subgoal?
 *)
rule bounded_exists_intro 'a :
   sequent { 'H >> 'B['a] } -->
   sequent { 'H >> member{'a; 'A} } -->
   sequent { 'H >> exists x: 'A. 'B['x] };;

(*
 * Bounded elim form.
 *
 * H, y: (exists x: A. B[x]), J >> T
 * by bounded_exists_elim a
 * H, y: (exists x: A. B[x]), a: A, z: B[a], J >> T
 *)
rule bounded_exists_elim 'H 'a 'z :
   sequent { 'H; y: (exists x: 'A. 'B['y]); a: 'A; b: 'B['a]; 'J['a, 'b] >> 'T['a, 'b] } -->
   sequent { 'H; y: (exists x: 'A. 'B['y]); 'J['y] >> 'T['y] };;

(*
 * Unbounded intro form.
 *
 * H >> exists x. B[x]
 * by exists_intro z
 * H >> B[z]
 * H >> member{z, set}
 *)
rule exists_intro 'z :
   sequent { 'H >> 'B['z] } -->
   sequent { 'H >> member{'z; set} } -->
   sequent { 'H >> "exists"{x. 'B['x]} };;

(*
 * Elim form.
 *
 * H, y: (exists x. B[x]), J >> T
 * by exists_elim z w
 * H, y: (exists x. B[x]), z: set, b: 'B['z], J>> T
 *)
rule all_elim 'H 'z 'b :
   sequent { 'H; y: "exists"{x. 'B['x]}; z: set; b: 'B['z]; 'J[z, b] >> 'T['z, 'b] } -->
   sequent { 'H; y: "exists"{x. 'B['x]}; 'J['y] >> 'T['y] };;

(*
 * Wellformedness.
 *)
rule bounded_exists_wf :
   sequent { 'H >> wf{'A} } --> (* should be a different judgment? *)
   sequent { 'H; x: set >> wf{'B['x]} } -->
   sequent { 'H >> wf{exists x: 'A. 'B['x] } };;

rule exists_wf :
   sequent { 'H; x: set >> wf{'B['x]} } -->
   sequent { 'H >> wf{"exists"{x. 'B['x]}} };;

(*
 * Bounded formula is restricted.
 *)
rule bounded_exists_res :
   sequent { 'H >> restricted{'A} } -->
   sequent { 'H; x: set; y: restricted{x} >> restricted{'B['x]} } -->
   sequent { 'H >> restricted{exists x: 'A. 'B['x]} };;

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
