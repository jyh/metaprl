(*
 * @theory[Itt_comment]
 *
 * Terms used for comments in the @Nuprl type theory.
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
 *)

extends Base_theory

(************************************************************************
 * UNIVERSES AND EQULITY
 ************************************************************************)

declare math_type{'a : Dform} : Dform
declare math_univ{'i : Dform} : Dform
declare math_equal{'T : Dform; 'a : Dform; 'b : Dform} : Dform
declare math_member{'T : Dform; 'a : Dform} : Dform
declare math_cumulativity{'i : Dform; 'j : Dform} : Dform

(************************************************************************
 * VOID
 ************************************************************************)

declare math_false : Dform

(************************************************************************
 * UNIT
 ************************************************************************)

declare math_unit : Dform
declare math_true : Dform
declare math_it : Dform

(************************************************************************
 * ATOM
 ************************************************************************)

declare math_atom : Dform
declare math_token{'t : Dform} : Dform

(************************************************************************
 * BOOL
 ************************************************************************)

declare math_bool : Dform
declare math_btrue : Dform
declare math_bfalse : Dform
declare math_bor{'a : Dform; 'b : Dform} : Dform
declare math_band{'a : Dform; 'b : Dform} : Dform
declare math_bimplies{'a : Dform; 'b : Dform} : Dform
declare math_bnot{'a : Dform} : Dform
declare math_if{'a : Dform; 'b : Dform; 'c : Dform} : Dform

(************************************************************************
 * INTEGERS
 ************************************************************************)

declare math_int : Dform
declare math_number{'n : Dform} : Dform
declare math_ind{'i : Dform; 'm : Dform; 'z : Dform; 'down : Dform; 'base : Dform; 'm : Dform; 'z : Dform; 'up : Dform} : Dform
declare math_add{'a : Dform; 'b : Dform} : Dform
declare math_sub{'a : Dform; 'b : Dform} : Dform
declare math_mul{'a : Dform; 'b : Dform} : Dform
declare math_div{'a : Dform; 'b : Dform} : Dform
declare math_rem{'a : Dform; 'b : Dform} : Dform
declare math_lt{'a : Dform; 'b : Dform} : Dform
declare math_le{'a : Dform; 'b : Dform} : Dform
declare math_ge{'a : Dform; 'b : Dform} : Dform
declare math_gt{'a : Dform; 'b : Dform} : Dform

(************************************************************************
 * UNION
 ************************************************************************)

declare math_union{'A : Dform; 'B : Dform} : Dform
declare math_inl{'x : Dform} : Dform
declare math_inr{'x : Dform} : Dform
declare math_decide{'x : Dform; 'y : Dform; 'a : Dform; 'z : Dform; 'b : Dform} : Dform
declare math_or{'a : Dform; 'b : Dform} : Dform
declare math_cor{'a : Dform; 'b : Dform} : Dform

(************************************************************************
 * FUNCTIONS
 ************************************************************************)

declare math_rfun{'f : Dform; 'x : Dform; 'A : Dform; 'B : Dform} : Dform
declare math_fun{'x : Dform; 'A : Dform; 'B : Dform} : Dform
declare math_fun{'A : Dform; 'B : Dform} : Dform
declare math_lambda{'v : Dform; 'b : Dform} : Dform
declare math_apply{'f : Dform; 'a : Dform} : Dform
declare math_well_founded{'A : Dform; 'x : Dform; 'y : Dform; 'R : Dform} : Dform
declare math_well_founded_assum{'A : Dform; 'a1 : Dform; 'a2 : Dform; 'R : Dform; 'P : Dform} : Dform
declare math_well_founded_prop{'A : Dform} : Dform
declare math_well_founded_apply{'P : Dform; 'a : Dform} : Dform
declare math_fix{'f : Dform; 'b : Dform} : Dform

declare math_not{'A : Dform} : Dform
declare math_all{'x : Dform; 'A : Dform; 'B : Dform} : Dform
declare math_implies{'A : Dform; 'B : Dform} : Dform
declare math_iff{'A : Dform; 'B : Dform} : Dform

(************************************************************************
 * PRODUCT
 ************************************************************************)

declare math_prod{'x : Dform; 'A : Dform; 'B : Dform} : Dform
declare math_prod{'A : Dform; 'B : Dform} : Dform
declare math_pair{'a : Dform; 'b : Dform} : Dform
declare math_spread{'e : Dform; 'u : Dform; 'v : Dform; 'b : Dform} : Dform
declare math_fst{'e : Dform} : Dform
declare math_snd{'e : Dform} : Dform
declare math_and{'a : Dform; 'b : Dform} : Dform
declare math_cand{'a : Dform; 'b : Dform} : Dform
declare math_exists{'x : Dform; 'A : Dform; 'B : Dform} : Dform

(************************************************************************
 * SET TYPE
 ************************************************************************)

declare math_set{'x : Dform; 'A : Dform; 'B : Dform} : Dform
declare math_squash{'A : Dform} : Dform

(************************************************************************
 * DECIDABLE
 ************************************************************************)

declare math_decidable{'P : Dform} : Dform

(************************************************************************
 * INTERSECTION
 ************************************************************************)

declare math_isect{'x : Dform; 'A : Dform; 'B : Dform} : Dform
declare math_top : Dform
declare math_record{'t : Dform} : Dform
declare math_bisect{'A : Dform; 'B : Dform} : Dform

(************************************************************************
 * Union
 ************************************************************************)

declare math_tunion{'x : Dform; 'A : Dform; 'B : Dform} : Dform
declare math_bunion{'A : Dform; 'B : Dform} : Dform

(************************************************************************
 * RECURSIVE TYPES
 ************************************************************************)

declare math_srec{'T : Dform; 'B : Dform} : Dform
declare math_prec{'T : Dform; 'y : Dform; 'B : Dform; 'a : Dform} : Dform
declare math_srecind{'t : Dform; 'a : Dform; 'b : Dform; 'c : Dform} : Dform
declare math_precind{'t : Dform; 'a : Dform; 'b : Dform; 'c : Dform} : Dform

declare math_w{'x : Dform; 'A : Dform; 'B : Dform} : Dform
declare math_tree{'a : Dform; 'f : Dform} : Dform
declare math_treeind{'z : Dform; 'a : Dform; 'f : Dform; 'g : Dform; 'body : Dform} : Dform

declare math_nil : Dform
declare math_cons{'a : Dform; 'b : Dform} : Dform
declare math_list{'l : Dform} : Dform
declare math_listind{'e : Dform; 'base : Dform; 'h : Dform; 't : Dform; 'f : Dform; 'step : Dform} : Dform

(************************************************************************
 * QUOTIENT TYPE
 ************************************************************************)

declare math_quot{'T : Dform; 'x : Dform; 'y : Dform; 'E : Dform} : Dform

(* OTHER *)

declare colons{'a : Dform} : Dform
declare semicolons{'a : Dform} : Dform

(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
