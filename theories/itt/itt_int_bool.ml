(*
 * Additional Boolean functions on integers.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of Nuprl-Light, a modular, higher order
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

include Itt_bool
include Itt_int
include Itt_logic

open Itt_logic

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*
 * Boolean valued predicates.
 *)
declare eq_int{'i; 'j}
declare lt_int{'i; 'j}
declare le_int{'i; 'j}
declare gt_int{'i; 'j}
declare ge_int{'i; 'j}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

primrw reduceEQInt : eq_int{natural_number[@i:n]; natural_number[@j:n]} <--> bool_flag[@i = @j]
primrw reduceLTInt : lt_int{natural_number[@i:n]; natural_number[@j:n]} <--> bool_flag[@i < @j]
primrw reduceGTInt : gt_int{natural_number[@i:n]; natural_number[@j:n]} <--> bool_flag[@j < @i]
primrw reduceLEInt : le_int{'i; 'j} <--> bor{eq_int{'i; 'j}; lt_int{'i; 'j}}
primrw reduceGEInt : le_int{'i; 'j} <--> bor{eq_int{'i; 'j}; gt_int{'i; 'j}}

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform eq_int_df : mode[prl] :: parens :: "prec"[prec_implies] :: eq_int{'i; 'j} =
   slot{'i} " " `"=" " " slot{'j}

dform lt_int_df : mode[prl] :: parens :: "prec"[prec_implies] :: lt_int{'i; 'j} =
   slot{'i} " " `"<" " " slot{'j}

dform le_int_df : mode[prl] :: parens :: "prec"[prec_implies] :: le_int{'i; 'j} =
   slot{'i} " " Nuprl_font!le " " slot{'j}

dform gt_int_df : mode[prl] :: parens :: "prec"[prec_implies] :: gt_int{'i; 'j} =
   slot{'i} " " `">" " " slot{'j}

dform ge_int_df : mode[prl] :: parens :: "prec"[prec_implies] :: ge_int{'i; 'j} =
   slot{'i} " " Nuprl_font!ge " " slot{'j}

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
