(*
 * Definition of well-foundedness that is a little easier
 * to use than the primtive definition in Itt_rfun.
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

include Itt_fun
include Itt_logic

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

declare partial_order{'A; x, y. 'R['x; 'y]}
declare well_founded[i:l]{'A; x, y. 'R['x; 'y]}

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

dform partial_order_df : partial_order{'A; x, y. 'R} =
   szone `"partial_order(" pushm[3] slot{'x} `"," slot{'y} `":" slot{'A} `"." hspace slot{'R} `")" popm ezone

dform well_founded_df : well_founded[i:l]{'A; x, y. 'R} =
   szone `"well_founded[" slot[i:l] `"](" pushm[3] slot{'x} `"," slot{'y} `":" slot{'A} `"." hspace slot{'R} `")" popm ezone

(************************************************************************
 * DEFINITION                                                           *
 ************************************************************************)

prim_rw unfold_partial_order : partial_order{'A; x, y. 'R['x; 'y]} <-->
   ((all x: 'A. "not"{'R['x; 'x]})
    & (all x: 'A. all y: 'A. ('R['x; 'y] => "not"{'R['y; 'x]}))
    & (all x: 'A. all y: 'A. all z: 'A. ('R['x; 'y] => ('R['y; 'z] => 'R['x; 'z]))))

prim_rw unfold_well_founded : well_founded[i:l]{'A; x, y. 'R['x; 'y]} <-->
   (partial_order{'A; x, y. 'R['x; 'y]}
    & (all P: ('A -> univ[i:l]).
       ((all x: 'A. ((all y: 'A. ('R['y; 'x] => ('P 'y))) => ('P 'x))) =>
        (all x: 'A. 'P 'x))))

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Typing of definitions.
 *)
interactive partial_order_type {| intro_resource [] |} 'H 'a 'b :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H; a: 'A; b: 'A >- "type"{'R['a; 'b]} } -->
   sequent ['ext] { 'H >- "type"{partial_order{'A; x, y. 'R['x; 'y]}} }

interactive well_founded_type {| intro_resource [] |} 'H 'a 'b :
   [wf] sequent [squash] { 'H >- "type"{'A} } -->
   [wf] sequent [squash] { 'H; a: 'A; b: 'A >- "type"{'R['a; 'b]} } -->
   sequent ['ext] { 'H >- "type"{well_founded[i:l]{'A; x, y. 'R['x; 'y]}} }

(*
 * Primitive well-foundedness can be derived.
 *)
interactive well_founded_reduction 'H 'a 'b univ[i:l] :
   [wf] sequent [squash] { 'H >- 'A IN univ[i:l] } -->
   [wf] sequent [squash] { 'H; a: 'A; b: 'A >- 'R['a; 'b] IN univ[i:l] } -->
   [main] sequent ['ext] { 'H >- well_founded[i:l]{'A; x, y. 'R['x; 'y]} } -->
   sequent ['ext] { 'H >- Itt_rfun!well_founded{'A; x, y. 'R['x; 'y]} }

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
