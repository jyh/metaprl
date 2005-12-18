doc <:doc<
   @module[Itt_hoas_debruijn]
   The @tt[Itt_hoas_debruijn] module defines a mapping from de Bruijn-like
   representation of syntax into the HOAS.

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
extends Itt_hoas_vector
extends Itt_nat
extends Itt_list2
extends Itt_image

open Basic_tactics

declare var{'left; 'right}
declare mk_bterm{'n; 'op; 'btl}
declare bdepth{'bt}
declare left{'v}
declare right{'v}
declare get_op{'bt; 'op}
declare subterms{'bt}
declare not_found
define iform unfold_get_op1 :
   get_op{'bt} <--> get_op{'bt; not_found}

(*
 * More abstract variable representation.
 * The type Var contains all the var{l; r} terms.
 *)
declare Var

topval fold_Var : conv
topval fold_mk_term : conv

declare beq_var{'x; 'y}

(************************************************************************
 * Tactics.
 *)

(*
 * Some reductions useful in wf proving (later, in Itt_hoas_bterm_wf).
 *)
val reduce_bind_of_mk_bterm_of_list_of_fun : conv
val reduce_vec_bind_of_mk_bterm_of_list_of_fun : conv
val reduce_bdepth_mk_bterm : conv

(*
 * Terms.
 *)
val is_mk_bterm_term : term -> bool
val dest_mk_bterm_term : term -> term * term * term
val mk_mk_bterm_term : term -> term -> term -> term

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
