(*
 * Display forms for math mode.
 *
 * ----------------------------------------------------------------
 *
 * Copyright (C) 2000 Jason Hickey, Caltech
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
 * jyh@cs.caltech.edu
 *)

extends Itt_theory

(************************************************************************
 * SETS
 ************************************************************************)

declare math_set : Dform
declare math_isset{'s : Dform} : Dform
declare math_collect{'x : Dform; 'T; 'a : Dform} : Dform
declare math_set_ind{'s : Dform; 'T; 'f : Dform; 'g : Dform; 'b : Dform} : Dform

(************************************************************************
 * EQUALITY
 ************************************************************************)

declare math_eq{'s1 : Dform; 's2 : Dform} : Dform
declare math_equal{'s1 : Dform; 's2 : Dform} : Dform
declare math_funset{'z : Dform; 'f : Dform} : Dform
declare math_funprop{'z : Dform; 'P} : Dform
declare math_dfunprop{'x : Dform; 'A; 'B} : Dform

(************************************************************************
 * MEMBERSHIP
 ************************************************************************)

declare math_mem{'x : Dform; 'y : Dform} : Dform
declare math_member{'x : Dform; 'y : Dform} : Dform

(************************************************************************
 * LOGIC
 ************************************************************************)

declare math_strue : Dform
declare math_sfalse : Dform
declare math_sor{'A; 'B} : Dform
declare math_sand{'A; 'B} : Dform
declare math_simplies{'A; 'B} : Dform
declare math_snot{'A} : Dform
declare math_siff{'A; 'B} : Dform
declare math_sall{'x : Dform; 'A; 'B} : Dform
declare math_sall{'x : Dform; 'A} : Dform
declare math_sexists{'x : Dform; 'A; 'B} : Dform
declare math_sexists{'x : Dform; 'A} : Dform
declare math_dall{'x : Dform; 'A; 'B} : Dform
declare math_dexists{'x : Dform; 'A; 'B} : Dform

(************************************************************************
 * SEPARATION
 ************************************************************************)

declare math_sep{'x : Dform; 's : Dform; 'P} : Dform
declare math_restricted{'P} : Dform

(************************************************************************
 * EMPTY
 ************************************************************************)

declare math_empty : Dform

(************************************************************************
 * SINGLETON
 ************************************************************************)

declare math_sing{'s : Dform} : Dform

(************************************************************************
 * UNION
 ************************************************************************)

declare math_union{'s : Dform} : Dform

(************************************************************************
 * INTERSECTION
 ************************************************************************)

declare math_isect{'s1 : Dform; 's2 : Dform} : Dform
declare math_isect{'s : Dform} : Dform

(************************************************************************
 * PAIR
 ************************************************************************)

declare math_pair{'s1 : Dform; 's2 : Dform} : Dform

(************************************************************************
 * INFINITY
 ************************************************************************)

declare math_inf : Dform
declare math_zero : Dform
declare math_succ{'i : Dform} : Dform
declare math_lt{'i : Dform; 'j : Dform} : Dform

(************************************************************************
 * RELATION
 ************************************************************************)

declare math_rel{'x : Dform; 'y : Dform; 'P; 's1 : Dform; 's2 : Dform} : Dform

(************************************************************************
 * SUBSET COLLECTION
 ************************************************************************)

declare math_power{'s1 : Dform; 's2 : Dform} : Dform

(************************************************************************
 * SUBSET
 ************************************************************************)

declare math_subset{'s1 : Dform; 's2 : Dform} : Dform

(************************************************************************
 * ORDERED PAIR
 ************************************************************************)

declare math_opair{'s1 : Dform; 's2 : Dform} : Dform

(************************************************************************
 * EQUIVALENCE RELATION
 ************************************************************************)

declare math_equiv{'s : Dform; 'r : Dform; 'a : Dform; 'b : Dform} : Dform
declare math_equiv{'s : Dform; 'r : Dform} : Dform
declare math_equivfunset{'s : Dform; 'r : Dform; 'z : Dform; 'f : Dform} : Dform
declare math_equivfunprop{'s : Dform; 'r : Dform; 'z : Dform; 'P} : Dform

(************************************************************************
 * SET BUILDER
 ************************************************************************)

declare math_setbvd{'x : Dform; 's : Dform; 'a : Dform} : Dform

(************************************************************************
 * INVERSE IMAGE
 ************************************************************************)

declare math_invimage{'x : Dform; 's : Dform; 'a : Dform; 't : Dform} : Dform

(************************************************************************
 * GROUP
 ************************************************************************)

declare math_group{'g : Dform} : Dform
declare math_car{'g : Dform} : Dform
declare math_op{'g : Dform; 'a : Dform; 'b : Dform} : Dform
declare math_id{'g : Dform} : Dform
declare math_inv{'g : Dform; 'a : Dform} : Dform

(************************************************************************
 * GROUP BUILDER
 ************************************************************************)

declare math_groupbvd{'h : Dform; 'g : Dform; 's : Dform} : Dform

(************************************************************************
 * ABELIAN GROUP
 ************************************************************************)

declare math_abel{'g : Dform} : Dform

(************************************************************************
 * SUBGROUP
 ************************************************************************)

declare math_subgroup{'s : Dform; 'g : Dform} : Dform

(************************************************************************
 * GROUP POWER
 ************************************************************************)

declare math_power{'g : Dform; 'z : Dform; 'n : Dform} : Dform

(************************************************************************
 * CYCLIC SUBGROUP
 ************************************************************************)

declare math_cycsubg{'s : Dform; 'g : Dform; 'a : Dform} : Dform

(************************************************************************
 * CYCLIC GROUP
 ************************************************************************)

declare math_cycgroup{'g : Dform; 'a : Dform} : Dform
declare math_cycg{'g : Dform} : Dform

(************************************************************************
 * COSET
 ************************************************************************)

declare math_lcoset{'h : Dform; 'g : Dform; 'a : Dform} : Dform
declare math_rcoset{'h : Dform; 'g : Dform; 'a : Dform} : Dform

(************************************************************************
 * NORMAL SUBGROUP
 ************************************************************************)

declare math_normalsubg{'s : Dform; 'g : Dform} : Dform

(************************************************************************
 * HOMOMORPHISM
 ************************************************************************)

declare math_hom{'x : Dform; 'g1 : Dform; 'g2 : Dform; 'f : Dform} : Dform

(************************************************************************
 * KERNEL
 ************************************************************************)

declare math_ker{'x : Dform; 'h : Dform; 'g1 : Dform; 'g2 : Dform; 'f : Dform} : Dform

(************************************************************************
 * ISOMORPHISM
 ************************************************************************)

declare math_iso{'x : Dform; 'g1 : Dform; 'g2 : Dform; 'f : Dform} : Dform

(************************************************************************
 * KLEIN 4-GROUP
 ************************************************************************)

declare math_klein4 : Dform
declare math_k0 : Dform
declare math_k1 : Dform
declare math_k2 : Dform
declare math_k3 : Dform

(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
