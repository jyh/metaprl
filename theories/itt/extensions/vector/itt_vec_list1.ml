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

(************************************************************************
 * Vlist.
 *)

(*
 * BUG: Unfortunately, we don't have define forms for sequents.
 * Temporarily use the declare/prim_rw form.
 *)
doc <:doc<
   The vector list produces a list from the hyps.
>>
declare sequent [vlist_nest] { Term : Term >- Term } : Term

prim_rw unfold_vlist_nest : vlist_nest{| <H> >- 'C |} <-->
   sequent_ind{u, v. cons{'u; happly{'v; it}}; Sequent{| <H> >- 'C |}}

doc <:doc<
   Reductions.
>>
interactive_rw reduce_vlist_nest_nil {| reduce |} :
   vlist_nest{| >- 'l |}
   <-->
   'l

interactive_rw reduce_vlist_nest_left :
   vlist_nest{| y: 'e; <J['y]> >- 'l['y] |}
   <-->
   cons{'e; vlist_nest{| <J[it]> >- 'l[it] |}}

interactive_rw reduce_vlist_nest_right :
   vlist_nest{| <J>; x: 'e >- 'l['x] |}
   <-->
   vlist_nest{| <J> >- cons{'e; 'l[it]} |}

interactive_rw hoist_vlist_nest_concl :
   vlist_nest{| <J> >- cons{'e; 'l} |}
   <-->
   vlist_nest{| <J>; 'e >- 'l |}

interactive_rw reduce_vlist_nest_bind_right :
   vlist_nest{| <J>; x: 'e >- 'l['x] |}
   <-->
   vlist_nest{| <J>; 'e >- 'l[it] |}

interactive_rw reduce_vlist_nest_split 'J :
   vlist_nest{| <J>; <K> >- 'l |}
   <-->
   vlist_nest{| <J> >- vlist_nest{| <K> >- 'l |} |}

doc <:doc<
   Well-formedness for the nested version of vector lists.
>>
interactive vlist_nest_concl_wf {| intro [] |} :
   [wf] sequent { <H> >- 'l in list{'A} } -->
   sequent { <H> >- vlist_nest{| >- 'l |} in list{'A} }

interactive vlist_nest_left_wf {| intro [] |} :
   [wf] sequent { <H> >- 'e in 'A } -->
   [wf] sequent { <H> >- vlist_nest{| <J[it]> >- 'l[it] |} in list{'A} } -->
   sequent { <H> >- vlist_nest{| x: 'e; <J['x]> >- 'l['x] |} in list{'A} }

doc <:doc<
   The actual << vlist{| <J> |} >> ignores its conclusion.
>>
declare sequent [vlist] { Term : Term >- Term } : Term

prim_rw unfold_vlist : vlist{| <J> >- 'C |} <-->
   vlist_nest{| <J> >- nil |}

interactive_rw reduce_vlist_nil {| reduce |} :
   vlist{||}
   <-->
   nil

interactive_rw reduce_vlist_left :
   vlist{| x: 'A; <J['x]> |}
   <-->
   'A :: vlist{| <J[it]> |}

interactive_rw reduce_vlist_split 'J :
   vlist{| <J>; <K<||> > |}
   <-->
   append{vlist{| <J> |}; vlist{| <K> |}}

interactive vlist_nil_wf :
   [wf] sequent { <H> >- 'A Type } -->
   sequent { <H> >- vlist{||} in list{'A} }

interactive vlist_left_wf :
   [wf] sequent { <H> >- 'e in 'A } -->
   [wf] sequent { <H> >- vlist{| <J[it]> |} in list{'A} } -->
   sequent { <H> >- vlist{| x: 'e; <J['x]> |} in list{'A} }

interactive vlist_split_wf 'J :
   [wf] sequent { <H> >- vlist{| <J> |} in list{'A} } -->
   [wf] sequent { <H> >- vlist{| <K> |} in list{'A} } -->
   sequent { <H> >- vlist{| <J>; <K<|H|> > |} in list{'A} }

(************************************************************************
 * Flattening.
 *)
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
   The << vflatten_nest{| <J> >- 'l |} >> term provides a sequent version of
   flattening.
>>
declare sequent [vflatten_nest] { Term : Term >- Term } : Term

prim_rw unfold_vflatten_nest : vflatten_nest{| <J> >- 'C |} <-->
   sequent_ind{u, v. append{'u; happly{'v; it}}; TermSequent{| <J> >- 'C |}}

interactive_rw reduce_vflatten_nest_nil {| reduce |} :
   vflatten_nest{| >- 'C |}
   <-->
   'C

interactive_rw reduce_vflatten_nest_left :
   vflatten_nest{| x: 'A; <J['x]> >- 'C['x] |}
   <-->
   append{'A; vflatten_nest{| <J[it]> >- 'C[it] |}}

interactive_rw reduce_vflatten_nest_right :
   vflatten_nest{| <J>; x: 'A >- 'C['x] |}
   <-->
   vflatten_nest{| <J> >- append{'A; 'C[it]} |}

interactive_rw reduce_vflatten_nest_split 'J :
   vflatten_nest{| <J>; <K> >- 'C |}
   <-->
   vflatten_nest{| <J> >- vflatten_nest{| <K> >- 'C |} |}

doc <:doc<
   The << vflatten{| <J> |} >> term ignores the conclusion.
>>
declare sequent [vflatten] { Term : Term >- Term } : Term

prim_rw unfold_vflatten : vflatten{| <J> >- 'C |} <-->
   vflatten_nest{| <J> >- nil |}

interactive_rw reduce_vflatten_nil {| reduce |} :
   vflatten{||}
   <-->
   nil

interactive_rw reduce_vflatten_left :
   vflatten{| x: 'A; <J['x]> |}
   <-->
   append{'A; vflatten{| <J[it]> |}}

doc <:doc<
   Well-formedness reasoning.
>>
interactive vflatten_list_wf {| intro [] |} :
   [wf] sequent { <H> >- vlist{| <J> |} in list{list} } -->
   sequent { <H> >- vflatten{| <J> |} in list }

doc <:doc<
   Associative properties.
>>
interactive_rw reduce_append_assoc :
   'l1 in "list" -->
   'l2 in "list" -->
   append{append{'l1; 'l2}; 'l3}
   <-->
   append{'l1; append{'l2; 'l3}}

interactive_rw reduce_vflatten_split 'J :
   vlist{| <J> |} in list{list} -->
   vflatten{| <J>; <K<||> > |}
   <-->
   append{vflatten{| <J> |}; vflatten{| <K> |}}

interactive_rw vflatten_collect 'J 'K :
   vlist{| <J> |} in list{list} -->
   vlist{| <K> |} in list{list} -->
   vflatten{| <J>; <K<||> >; <L<||> > |}
   <-->
   vflatten{| <J>; vflatten{| <K> |}; <L> |}

interactive_rw vflatten_flatten 'J :
   vlist{| <J> |} in list{list} -->
   vlist{| <K> |} in list{list} -->
   vflatten{| <J>; vflatten{| <K<||> > |}; <L<||> > |}
   <-->
   vflatten{| <J>; <K>; <L> |}

doc <:doc<
   Forming flatten vectors out of nested appends.
>>
interactive_rw vflatten_of_append :
   'l1 in list -->
   'l2 in list -->
   append{'l1; 'l2}
   <-->
   vflatten{| 'l1; 'l2 |}

interactive_rw reduce_vflatten_append 'J :
   'l1 in "list" -->
   'l2 in "list" -->
   vflatten{| <J>; x: append{'l1<||>; 'l2<||>}; <K['x]> |}
   <-->
   vflatten{| <J>; 'l1; 'l2; <K[it]> |}

(************************************************************************
 * Display forms.
 *)
doc docoff

dform vlist_nest_df : vlist_nest{| <H> |} =
   szone pushm[1] `"[" display_sequent{vlist_nest{| <H> |}} `"]" popm ezone

dform vlist_nest_hyp_df : display_hyp{vlist_nest; x. 'e} =
   szone pushm[3] slot{'x} `":" hspace slot{'e} popm ezone

dform vlist_nest_sep_df : display_hyp_sep{vlist_nest} =
   `";" hspace

dform vlist_nest_concl_df : display_concl{vlist_nest; 'c} =
   `"???"

dform vlist_nest_concl_df : display_concl{vlist_nest; xconcl} =
   `""

(************************************************************************
 * Tactics.
 *)
let fold_vlist_nest = makeFoldC << vlist_nest{| <H> >- 'C |} >> unfold_vlist_nest
let fold_vflatten_nest = makeFoldC << vflatten_nest{| <J> >- 'C |} >> unfold_vflatten_nest

dform vlist_df : vlist{| <H> >- 'C |} =
   szone pushm[3] `"vlist[" display_sequent{vlist{| <H> >- 'C |}} `"]" popm ezone

dform vlist_hyp_df : display_hyp{vlist; v. 'e} =
   slot{'e}

dform vlist_concl_df : display_concl{vlist; xconcl} =
   `""

dform vlist_concl_df2 : display_concl{vlist; 'C} =
   slot{'C}

dform vflatten_df : vflatten{| <H> >- 'C |} =
   szone pushm[3] `"vflatten[" display_sequent{vflatten{| <H> >- 'C |}} `"]" popm ezone

dform vflatten_hyp_df : display_hyp{vflatten; v. 'e} =
   slot{'e}

dform vflatten_concl_df : display_concl{vflatten; xconcl} =
   `""

dform vflatten_concl_df2 : display_concl{vflatten; 'C} =
   slot{'C}

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
