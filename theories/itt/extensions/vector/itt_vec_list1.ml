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
   sequent_ind{u, v. cons{'u; happly{'v; 'u}}; Sequent{| <H> >- 'C |}}

doc <:doc<
   Reductions.
>>
interactive_rw reduce_vlist_nil {| reduce |} :
   vlist{| >- 'l |}
   <-->
   'l

interactive_rw reduce_vlist_cons :
   vlist{| y: 'e; <J['y]> >- 'l['y] |}
   <-->
   cons{'e; vlist{| <J['e]> >- 'l['e] |}}

interactive_rw reduce_vlist_tail :
   vlist{| <J>; x: 'e >- 'l['x] |}
   <-->
   vlist{| <J> >- cons{'e; 'l['e]} |}

interactive_rw hoist_vlist_tail :
   vlist{| <J> >- cons{'e; 'l} |}
   <-->
   vlist{| <J>; 'e >- 'l |}

interactive_rw flatten_tail :
   vlist{| <J>; x: 'e >- 'l['x] |}
   <-->
   vlist{| <J>; 'e >- 'l['e] |}

doc <:doc<
   Well-formedness for vector lists.
>>
interactive vlist_nil_wf {| intro [] |} :
   [wf] sequent { <H> >- 'l in list{'A} } -->
   sequent { <H> >- vlist{| >- 'l |} in list{'A} }

interactive vlist_cons_wf {| intro [] |} :
   [wf] sequent { <H> >- 'e in 'A } -->
   [wf] sequent { <H> >- vlist{| <J['e]> >- 'l['e] |} in list{'A} } -->
   sequent { <H> >- vlist{| x: 'e; <J['x]> >- 'l['x] |} in list{'A} }

interactive vlist_split_wf 'J :
   [wf] sequent { <H> >- vlist{| <J> >- vlist{| <K> >- 'l |} |} in list{'A} } -->
   sequent { <H> >- vlist{| <J>; <K> >- 'l |} in list{'A} }

doc <:doc<
   The << flatten{'l} >> term flattens a list using << append{'l1; 'l2} >>.
>>
define unfold_flatten : flatten{'l} <-->
   list_ind{'l; nil; u, v, g. append{'u; 'g}}

interactive_rw reduce_flatten_nil {| reduce |} :
   flatten{nil}
   <-->
   nil

interactive_rw reduce_flatten_cons {| reduce |} :
   flatten{'u::'v}
   <-->
   append{'u; flatten{'v}}

interactive flatten_wf {| intro [] |} :
   [wf] sequent { <H> >- 'l in list{list} } -->
   sequent { <H> >- flatten{'l} in list }

doc <:doc<
   The << vflatten{| <J> >- 'l |} >> term provides a sequent version of
   flattening.
>>
declare sequent [vflatten] { Term : Term >- Term } : Term

prim_rw unfold_vflatten : vflatten{| <J> >- 'C |} <-->
   sequent_ind{u, v. append{'u; happly{'v; it}}; TermSequent{| <J> >- 'C |}}

interactive_rw reduce_vflatten_nil {| reduce |} :
   vflatten{| >- 'C |}
   <-->
   'C

interactive_rw reduce_vflatten_left :
   vflatten{| x: 'A; <J['x]> >- 'C['x] |}
   <-->
   append{'A; vflatten{| <J[it]> >- 'C[it] |}}

interactive_rw reduce_vflatten_right :
   vflatten{| <J>; x: 'A >- 'C['x] |}
   <-->
   vflatten{| <J> >- append{'A; 'C[it]} |}

interactive_rw reduce_vflatten_split 'J :
   vflatten{| <J>; <K> >- 'C |}
   <-->
   vflatten{| <J> >- vflatten{| <K> >- 'C |} |}

(*
 * Reversed rewrites.
 *)
interactive_rw collect_vflatten_left :
   append{'l; vflatten{| <J> >- 'C |}}
   <-->
   vflatten{| 'l; <J> >- 'C |}

interactive_rw reduce_vflatten_join :
   vflatten{| <J> >- vflatten{| <K> >- 'C |} |}
   <-->
   vflatten{| <J>; <K> >- 'C |}

(*
 * Nested appends.
 *)
interactive_rw reduce_append_assoc :
   'l1 in "list" -->
   'l2 in "list" -->
   append{append{'l1; 'l2}; 'l3}
   <-->
   append{'l1; append{'l2; 'l3}}

interactive_rw reduce_vflatten_append 'J :
   'l1 in "list" -->
   'l2 in "list" -->
   vflatten{| <J>; x: append{'l1<||>; 'l2<||>}; <K['x]> >- 'C['x] |}
   <-->
   vflatten{| <J>; 'l1; 'l2; <K[it]> >- 'C[it] |}

(************************************************************************
 * Display forms.
 *)
doc docoff

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

(************************************************************************
 * Tactics.
 *)
let fold_vlist = makeFoldC << vlist{| <H> >- 'C |} >> unfold_vlist
let fold_vflatten = makeFoldC << vflatten{| <J> >- 'C |} >> unfold_vflatten

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
