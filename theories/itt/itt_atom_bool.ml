(*
 * Theorems about atoms.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/htmlman/default.html or visit http://metaprl.org/
 * for more information.
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

extends Itt_atom
extends Itt_bool
extends Itt_struct

open Tactic_type.Tacticals
open Tactic_type.Conversionals

open Base_meta
open Dtactic

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

prec prec_eq_atom

declare eq_atom{'x; 'y}

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

dform eq_atom_df : parens :: "prec"[prec_eq_atom] :: except_mode[src] :: eq_atom{'x; 'y} =
   slot{'x} space `"=" suba slot{'y}

(************************************************************************
 * REWRITE                                                              *
 ************************************************************************)

prim_rw reduce_eq_atom' : eq_atom{token[x:t]; token[y:t]} <-->
   meta_eq[x:t, y:t]{btrue; bfalse}

let reduce_eq_atom =
   reduce_eq_atom' thenC reduce_meta_eq_tok

let resource reduce += << eq_atom{token[x:t]; token[y:t]} >>, reduce_eq_atom

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

prim eq_atom_wf {| intro [] |} :
   [wf] sequent { <H> >- 'x in atom } -->
   [wf] sequent { <H> >- 'y in atom } -->
   sequent { <H> >- eq_atom{'x; 'y} in bool } =
   it

prim eq_atom_assert_intro {| intro [] |} :
   [wf] sequent { <H> >- 'x = 'y in atom } -->
   sequent { <H> >- "assert"{eq_atom{'x; 'y}} } =
   it

prim eq_atom_assert_elim {| elim [] |} 'H :
   [main] sequent { <H>; x: 'a = 'b in atom; <J[it]> >- 'C[it] } -->
   sequent { <H>; x: "assert"{eq_atom{'a; 'b}}; <J['x]> >- 'C['x] } =
   it

interactive eq_atom_elim 'H :
   sequent { <H>; u: meta_eq[x:t, y:t]{"true"; "false"}; <J[it]> >- 'C[it] } -->
   sequent { <H>; u: token[x:t] = token[y:t] in atom; <J['u]> >- 'C['u] }

let eq_atom_assert_elimT n = eq_atom_elim n thenT rw reduce_meta_eq_tok n thenT dT n

let resource elim += <<token[x:t] = token[y:t] in atom>>,  eq_atom_assert_elimT

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
