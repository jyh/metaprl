(*
 * @begin[doc]
 * @theory[Itt_comment]
 *
 * Terms used for comments in the @Nuprl type theory.
 * @end[doc]
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
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
 * @email{jyh@cs.caltech.edu}
 * @end[doc]
 *)

extends Base_theory

(************************************************************************
 * UNIVERSES AND EQULITY
 ************************************************************************)

declare math_type{'a}
declare math_univ{'i}
declare math_equal{'T; 'a; 'b}
declare math_member{'T; 'a}
declare math_cumulativity{'i; 'j}

(************************************************************************
 * VOID
 ************************************************************************)

declare math_void
declare math_false

(************************************************************************
 * UNIT
 ************************************************************************)

declare math_unit
declare math_true
declare math_it

(************************************************************************
 * ATOM
 ************************************************************************)

declare math_atom
declare math_token{'t}

(************************************************************************
 * BOOL
 ************************************************************************)

declare math_bool
declare math_btrue
declare math_bfalse
declare math_bor{'a; 'b}
declare math_band{'a; 'b}
declare math_bimplies{'a; 'b}
declare math_bnot{'a}
declare math_assert{'t}
declare math_if{'a; 'b; 'c}

(************************************************************************
 * INTEGERS
 ************************************************************************)

declare math_int
declare math_number{'n}
declare math_ind{'i; 'm; 'z; 'down; 'base; 'm; 'z; 'up}
declare math_add{'a; 'b}
declare math_sub{'a; 'b}
declare math_mul{'a; 'b}
declare math_div{'a; 'b}
declare math_rem{'a; 'b}
declare math_lt{'a; 'b}
declare math_le{'a; 'b}
declare math_ge{'a; 'b}
declare math_gt{'a; 'b}

(************************************************************************
 * UNION
 ************************************************************************)

declare math_union{'A; 'B}
declare math_inl{'x}
declare math_inr{'x}
declare math_decide{'x; 'y; 'a; 'z; 'b}
declare math_or{'a; 'b}
declare math_cor{'a; 'b}

(************************************************************************
 * FUNCTIONS
 ************************************************************************)

declare math_rfun{'f; 'x; 'A; 'B}
declare math_fun{'x; 'A; 'B}
declare math_fun{'A; 'B}
declare math_lambda{'v; 'b}
declare math_apply{'f; 'a}
declare math_well_founded{'A; 'x; 'y; 'R}
declare math_well_founded_assum{'A; 'a1; 'a2; 'R; 'P}
declare math_well_founded_prop{'A}
declare math_well_founded_apply{'P; 'a}
declare math_fix{'f; 'b}

declare math_not{'A}
declare math_all{'x; 'A; 'B}
declare math_implies{'A; 'B}
declare math_iff{'A; 'B}

(************************************************************************
 * PRODUCT
 ************************************************************************)

declare math_prod{'x; 'A; 'B}
declare math_prod{'A; 'B}
declare math_pair{'a; 'b}
declare math_spread{'e; 'u; 'v; 'b}
declare math_fst{'e}
declare math_snd{'e}
declare math_and{'a; 'b}
declare math_cand{'a; 'b}
declare math_exists{'x; 'A; 'B}

(************************************************************************
 * SET TYPE
 ************************************************************************)

declare math_set{'x; 'A; 'B}
declare math_squash{'A}

(************************************************************************
 * DECIDABLE
 ************************************************************************)

declare math_decidable{'P}

(************************************************************************
 * INTERSECTION
 ************************************************************************)

declare math_isect{'x; 'A; 'B}
declare math_top
declare math_record{'t}
declare math_bisect{'A; 'B}

(************************************************************************
 * Union
 ************************************************************************)

declare math_tunion{'x; 'A; 'B}
declare math_bunion{'A; 'B}

(************************************************************************
 * RECURSIVE TYPES
 ************************************************************************)

declare math_srec{'T; 'B}
declare math_prec{'T; 'y; 'B; 'a}
declare math_srecind{'t; 'a; 'b; 'c}
declare math_precind{'t; 'a; 'b; 'c}

declare math_w{'x; 'A; 'B}
declare math_tree{'a; 'f}
declare math_treeind{'z; 'a; 'f; 'g; 'body}

declare math_nil
declare math_cons{'a; 'b}
declare math_list{'l}
declare math_listind{'e; 'base; 'h; 't; 'f; 'step}

(************************************************************************
 * QUOTIENT TYPE
 ************************************************************************)

declare math_quot{'T; 'x; 'y; 'E}
declare math_esquash{'P}

(************************************************************************
 * SUBSET
 ************************************************************************)

declare math_subset{'t1; 't2}

(************************************************************************
 * GROUP THEORY
 ************************************************************************)

declare math_groupoid{'i}
declare math_semigroup{'i}
declare math_monoid{'i}
declare math_group{'i}
declare math_premonoid{'i}
declare math_pregroup{'i}

declare math_car{'g}
declare math_mul{'g; 'a; 'b}
declare math_id{'g}
declare math_inv{'g; 'a}

declare math_csemigroup{'i}
declare math_cmonoid{'i}
declare math_abelg{'i}

declare math_subStructure{'s; 'g}
declare math_subgroup{'i; 's; 'g}

declare math_lcoset{'h; 'g; 'a}
declare math_rcoset{'h; 'g; 'a}
declare math_normalSubg{'i; 's; 'g}

declare math_group_power{'g; 'a; 'n}
declare math_cycGroup{'g}
declare math_cycSubg{'g; 'a}

declare math_isBijective{'f; 'A; 'B}
declare math_groupHom{'A; 'B}
declare math_groupIso{'A; 'B}
declare math_groupKer{'f; 'A; 'B}

(* OTHER *)

declare colons{'a}
declare semicolons{'a}

(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
