doc <:doc<
   @module[Itt_vec_list1]

   The @tt[Itt_vec_list1] module defines lists expressed as
   sequents.

   @docoff
   ----------------------------------------------------------------

   @begin[license]

   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 1998-2005 MetaPRL Group, Caltech

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

   Author: Jason Hickey @email{jyh@cs.caltech.edu}

   @end[license]

   @parents
>>
extends Itt_theory
extends Itt_vec_dform
extends Meta_extensions_theory

doc docoff

open Basic_tactics

(*
 * BUG: Unfortunately, we don't have define forms for sequents.
 * Temporarily use the declare/prim_rw form.
 *)
doc <:doc<
   The vector list produces a list from the hyps.
>>
prim_rw unfold_vlist : vlist{| <H> >- 'C |} <-->
   sequent_ind{c. nil; u, v. cons{'u; happly{'v; 'u}}; Sequent{| <H> >- 'C |}}

doc docoff

let fold_vlist = makeFoldC << vlist{| <H> |} >> unfold_vlist

doc <:doc<
   Reductions.
>>
interactive_rw reduce_vlist_nil {| reduce |} :
   vlist{||}
   <-->
   nil

interactive_rw reduce_vlist_cons :
   vlist{| x: 'e; <J['x]> |}
   <-->
   cons{'e; vlist{| <J['e]> |}}

doc <:doc<
   Well-formedness for vector sequents.
>>
interactive vlist_nil_wf {| intro [] |} :
   [wf] sequent { <H> >- 'A Type } -->
   sequent { <H> >- vlist{||} in list{'A} }

interactive vlist_cons_wf {| intro [] |} :
   [wf] sequent { <H> >- 'e in 'A } -->
   [wf] sequent { <H> >- vlist{| <J['e]> |} in list{'A} } -->
   sequent { <H> >- vlist{| x: 'e; <J['x]> |} in list{'A} }

interactive vlist_split_wf 'J :
   [wf] sequent { <H> >- vlist{| <J> |} in list{'A} } -->
   [wf] sequent { <H> >- vlist{| <K> |} in list{'A} } -->
   sequent { <H> >- vlist{| <J>; <K<|H|> > |} in list{'A} }

(************************************************************************
 * Display forms.
 *)
dform vlist_df : vlist{| <H> |} =
   szone pushm[1] `"[" display_sequent{vlist{| <H> |}} `"]" popm ezone

dform vlist_hyp_df : display_hyp{vlist; x. 'e} =
   szone pushm[3] slot{'x} `":" hspace slot{'e} popm ezone

dform vlist_sep_df : display_hyp_sep{vlist} =
   `";" hspace

dform vlist_concl_df : display_concl{vlist; 'c} =
   `"???"

dform vlist_concl_df : display_concl{vlist; xconcl} =
   `""

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
