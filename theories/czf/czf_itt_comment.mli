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

include Itt_theory

(************************************************************************
 * SETS
 ************************************************************************)

declare math_set
declare math_isset{'s}
declare math_collect{'x; 'T; 'a}
declare math_set_ind{'s; 'T; 'f; 'g; 'b}

(************************************************************************
 * EQUALITY
 ************************************************************************)

declare math_eq{'s1; 's2}
declare math_equal{'s1; 's2}
declare math_funset{'z; 'f}
declare math_funprop{'z; 'P}
declare math_dfunprop{'x; 'A; 'B}

(************************************************************************
 * MEMBERSHIP
 ************************************************************************)

declare math_mem{'x; 'y}
declare math_member{'x; 'y}

(************************************************************************
 * LOGIC
 ************************************************************************)

declare math_strue
declare math_sfalse
declare math_sor{'A; 'B}
declare math_sand{'A; 'B}
declare math_simplies{'A; 'B}
declare math_snot{'A}
declare math_siff{'A; 'B}
declare math_sall{'x; 'A; 'B}
declare math_sall{'x; 'A}
declare math_sexists{'x; 'A; 'B}
declare math_sexists{'x; 'A}
declare math_dall{'x; 'A; 'B}
declare math_dexists{'x; 'A; 'B}

(************************************************************************
 * SEPARATION
 ************************************************************************)

declare math_sep{'x; 's; 'P}
declare math_restricted{'P}

(************************************************************************
 * EMPTY
 ************************************************************************)

declare math_empty

(************************************************************************
 * SINGLETON
 ************************************************************************)

declare math_sing{'s}

(************************************************************************
 * UNION
 ************************************************************************)

declare math_union{'s}

(************************************************************************
 * INTERSECTION
 ************************************************************************)

declare math_isect{'s1; 's2}
declare math_isect{'s}

(************************************************************************
 * PAIR
 ************************************************************************)

declare math_pair{'s1; 's2}

(************************************************************************
 * INFINITY
 ************************************************************************)

declare math_inf
declare math_zero
declare math_succ{'i}
declare math_lt{'i; 'j}

(************************************************************************
 * RELATION
 ************************************************************************)

declare math_rel{'x; 'y; 'P; 's1; 's2}

(************************************************************************
 * SUBSET COLLECTION
 ************************************************************************)

declare math_power{'s1; 's2}

(************************************************************************
 * SUBSET
 ************************************************************************)

declare math_subset{'s1; 's2}

(************************************************************************
 * EQUIVALENCE RELATION
 ************************************************************************)

declare math_equiv{'s; 'r; 'a; 'b}
declare math_equiv{'s; 'r}
declare math_equivfunset{'s; 'r; 'z; 'f}
declare math_equivfunprop{'s; 'r; 'z; 'P}

(************************************************************************
 * GROUP
 ************************************************************************)

declare math_group{'g}
declare math_car{'g}
declare math_eqG{'g}
declare math_op{'g; 'a; 'b}
declare math_id{'g}
declare math_inv{'g; 'a}

(************************************************************************
 * GROUP BUILDER
 ************************************************************************)

declare math_groupbvd{'h; 'g; 's}

(************************************************************************
 * ABELIAN GROUP
 ************************************************************************)

declare math_abel{'g}

(************************************************************************
 * SUBGROUP
 ************************************************************************)

declare math_subgroup{'s; 'g}

(************************************************************************
 * CYCLIC SUBGROUP
 ************************************************************************)

declare math_power{'g; 'z; 'n}
declare math_cycsubg{'s; 'g; 'a}

(************************************************************************
 * CYCLIC GROUP
 ************************************************************************)

declare math_cycgroup{'g; 'a}

(************************************************************************
 * COSET
 ************************************************************************)

declare math_lcoset{'h; 'g; 'a}
declare math_rcoset{'h; 'g; 'a}

(************************************************************************
 * NORMAL SUBGROUP
 ************************************************************************)

declare math_normalsubg{'s; 'g}

(************************************************************************
 * SET BUILDER
 ************************************************************************)

declare math_setbvd{'x; 's; 'a}

(************************************************************************
 * INVERSE IMAGE
 ************************************************************************)

declare math_invimage{'x; 's; 'a; 't}

(************************************************************************
 * HOMOMORPHISM
 ************************************************************************)

declare math_hom{'x; 'g1; 'g2; 'f}

(************************************************************************
 * KERNEL
 ************************************************************************)

declare math_ker{'x; 'h; 'g1; 'g2; 'f}

(************************************************************************
 * ISOMORPHISM
 ************************************************************************)

declare math_iso{'x; 'g1; 'g2; 'f}

(************************************************************************
 * KLEIN 4-GROUP
 ************************************************************************)

declare math_klein4
declare math_k0
declare math_k1
declare math_k2
declare math_k3

(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
