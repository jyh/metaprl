doc <:doc<
   @begin[doc]
   @module[Itt_synt_var]
   A deBruijn-like implementation of a type of bound variables.

   @end[doc]

   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/index.html for information on Nuprl,
   OCaml, and more information about this system.

   Copyright (C) 2005, MetaPRL Group

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License
   as published by the Free Software Foundation; either version 2
   of the License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

   Authors: Aleksey Nogin @email{nogin@cs.caltech.edu}
            Alexei Kopylov @email{kopylov@cs.caltech.edu}
            Xin Yu @email{xiny@cs.caltech.edu}

   @end[license]
>>

doc "doc"{parents}

extends Itt_int_base
extends Itt_nat

open Basic_tactics

doc "doc"{terms}

declare Var
declare var{'left; 'right} (* depth = left + right + 1 *)
declare left{'v}
declare right{'v}

define unfold_depth:
   depth{'v} <--> left{'v} +@ right{'v} +@ 1

define unfold_eq:
   is_eq{'v;'u} <--> (left{'v} =@ left{'u})

doc "doc"{rewrites}

prim_rw left_id {| reduce |} :
   left {var{'left; 'right}} <--> 'left

prim_rw right_id {| reduce |} :
   right {var{'left; 'right}} <--> 'right

interactive_rw eq_equal {| reduce |} :
   is_eq{var{'left_1; 'right_1};var{'left_2; 'right_2}} <--> ('left_1 =@ 'left_2)

interactive_rw eq_same {| reduce |} :
   ('v in Var) -->
   is_eq{'v;'v} <--> btrue


doc "doc"{rules}

prim var_univ {| intro [] |}:
   sequent { <H> >- Var in univ[l:l] } = it

interactive var_type {| intro [] |}:
   sequent { <H> >- Var Type }

prim var_wf {| intro [] |} :
   sequent { <H> >- 'left in nat } -->
   sequent { <H> >- 'right in nat } -->
   sequent { <H> >- var{'left; 'right} in Var } = it

prim var_elim {| elim [] |} 'H :
   ('ext['left; 'right]: sequent { <H>; left: nat; right: nat; <J[var{'left; 'right}]>
      >- 'C[var{'left; 'right}] }) -->
   sequent { <H>; v: Var; <J['v]> >- 'C['v] } = 'ext[left{'v}; right{'v}]

interactive left_wf {| intro [] |} :
   sequent { <H> >- 'v in Var } -->
   sequent { <H> >- left{'v} in nat }

interactive right_wf {| intro [] |} :
   sequent { <H> >- 'v in Var } -->
   sequent { <H> >- right{'v} in nat }

interactive depth_wf {| intro [] |} :
   sequent { <H> >- 'v in Var } -->
   sequent { <H> >- depth{'v} in nat }

(* XXX: TODO: arith tactics need to know abot the next 3 rules *)

interactive depth_pos {| intro [] |} :
   sequent { <H> >- 'v in Var } -->
   sequent { <H> >- depth{'v} > 0 }

interactive left_bound {| intro [] |} :
   sequent { <H> >- 'v in Var } -->
   sequent { <H> >- left{'v} < depth{'v} }

interactive right_bound {| intro [] |} :
   sequent { <H> >- 'v in Var } -->
   sequent { <H> >- right{'v} < depth{'v} }

doc <:doc< @docoff >>
