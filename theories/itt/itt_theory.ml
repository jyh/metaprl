(*!
 * @begin[doc]
 * @theory[Itt_theory]
 *
 * The @tt{Itt_theory} module collects all of the modules in the
 * @Nuprl type theory.  This is the basic module to use when
 * stating and proving theorems the the @Nuprl type theory.
 * @end[doc]
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
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
 * @email{jyh@cs.cornell.edu}
 * @end[license]
 *)

(*!
 * @begin[doc]
 * @parents
 * @end[doc]
 *)
include Base_theory
include Itt_equal
include Itt_void
include Itt_bool
include Itt_atom
include Itt_int
include Itt_rfun
include Itt_dfun
include Itt_fun
include Itt_well_founded
include Itt_dprod
include Itt_prod
include Itt_union
include Itt_struct
include Itt_set
include Itt_isect
include Itt_tunion
include Itt_bisect
include Itt_disect
include Itt_bunion
include Itt_subtype
include Itt_w
include Itt_prec
include Itt_srec
include Itt_list
include Itt_list2
include Itt_quotient
include Itt_esquash
include Itt_decidable

(*!
 * Theories we do not want to include in the
 * documentation.
 *
 * @docoff
 *)
include Itt_atom_bool
include Itt_int_bool
include Itt_arith
include Itt_derive
include Itt_prop_decide
include Itt_fset

open Itt_equal
open Itt_rfun
open Itt_logic
open Itt_w
open Itt_list
open Itt_list2
open Itt_tunion
open Itt_bisect
open Itt_bunion
open Itt_atom_bool
open Itt_fset
open Itt_esquash

(*
 * Combine the precedences.
 *)
prec prec_assoc < prec_equal
prec prec_equal < prec_apply
prec prec_type = prec_apply
prec prec_not < prec_apply
prec prec_w = prec_quant
prec prec_tree_ind < prec_quant
prec prec_list = prec_apply
prec prec_tunion = prec_apply
prec prec_bisect = prec_and
prec prec_bunion = prec_or
prec prec_eq_atom = prec_equal

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)

