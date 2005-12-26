doc <:doc<
   The @tt[Itt_hoas_vector] module defines the ``vector bindings''
   extensions for the basic ITT HOAS.

   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

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

   Author: Aleksey Nogin @email{nogin@cs.caltech.edu}

   @end[license]
>>
extends Itt_hoas_base
extends Itt_nat
extends Itt_list2

open Basic_tactics

declare bind{'n; x.'t['x]}
declare subst{'n; 'bt; 't}
declare substl{'bt; 'tl}

define iform simple_bindn: bind{'n; 't} <-->  bind{'n; x.'t}

(************************************************************************
 * Tactics.
 *)
topval reduceBTermC : conv
topval reduceBTermT : tactic

val subst_to_substl : conv
val bindone_into_bind : conv
val bind_into_bindone : conv
val coalesce_bindn_bindn : conv
val substl_substl_lof : conv
val bindn_to_list_of_fun : conv

val is_bindn_term : term -> bool
val mk_bindn_term : var -> term -> term -> term
val dest_bindn_term : term -> var * term * term

val is_substl_term : term -> bool
val dest_substl_term : term -> term * term
val mk_substl_term : term -> term -> term

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
