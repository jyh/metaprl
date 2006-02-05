doc <:doc<
   @module[Itt_vec_list2]

   Dependent vector lists.

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
extends Itt_vec_list1
extends Itt_vec_dform

doc docoff

open Basic_tactics

open Itt_equal

(*
 * BUG: Unfortunately, we don't have define forms for sequents.
 * Temporarily use the declare/prim_rw form.
 *)
doc <:doc<
   The vector list produces a list from the hyps.
>>
declare sequent [vdlist_nest{'f}] { Term : Term >- Term } : Term

prim_rw unfold_vdlist_nest : vdlist_nest{'f}{| <H> >- 'C |} <-->
   sequent_ind{u, v. cons{'u; happly{'v; 'f 'u}}; TermSequent{| <H> >- 'C |}}

doc <:doc<
   Reductions.
>>
interactive_rw reduce_vdlist_nest_nil {| reduce |} :
   vdlist_nest{'f}{| >- 'l |}
   <-->
   'l

interactive_rw reduce_vdlist_nest_left :
   vdlist_nest{'f}{| y: 'e; <J['y]> >- 'l['y] |}
   <-->
   cons{'e; vdlist_nest{'f}{| <J['f 'e]> >- 'l['f 'e] |}}

interactive_rw reduce_vdlist_nest_right :
   vdlist_nest{'f}{| <J>; x: 'e >- 'l['x] |}
   <-->
   vdlist_nest{'f}{| <J> >- cons{'e; 'l['f 'e]} |}

interactive_rw hoist_vdlist_nest_concl :
   vdlist_nest{'f}{| <J> >- cons{'e; 'l} |}
   <-->
   vdlist_nest{'f}{| <J>; 'e >- 'l |}

interactive_rw reduce_vdlist_nest_bind_right :
   vdlist_nest{'f}{| <J>; x: 'e >- 'l['x] |}
   <-->
   vdlist_nest{'f}{| <J>; 'e >- 'l['f 'e] |}

interactive_rw reduce_vdlist_nest_split 'J :
   vdlist_nest{'f}{| <J>; <K> >- 'l |}
   <-->
   vdlist_nest{'f}{| <J> >- vdlist_nest{'f}{| <K> >- 'l |} |}

doc <:doc<
   Well-formedness for the nested version of vector lists.
>>
interactive vdlist_nest_concl_wf {| intro [] |} :
   [wf] sequent { <H> >- 'l in list{'A} } -->
   sequent { <H> >- vdlist_nest{'f}{| >- 'l |} in list{'A} }

interactive vdlist_nest_left_wf {| intro [] |} :
   [wf] sequent { <H> >- 'e in 'A } -->
   [wf] sequent { <H> >- vdlist_nest{'f}{| <J['f 'e]> >- 'l['f 'e] |} in list{'A} } -->
   sequent { <H> >- vdlist_nest{'f}{| x: 'e; <J['x]> >- 'l['x] |} in list{'A} }

doc <:doc<
   The actual << vdlist{'f}{| <J> |} >> ignores its conclusion.
>>
declare sequent [vdlist{'f}] { Term : Term >- Term } : Term

prim_rw unfold_vdlist : vdlist{'f}{| <J> >- 'C |} <-->
   vdlist_nest{'f}{| <J> >- nil |}

interactive_rw reduce_vdlist_nil {| reduce |} :
   vdlist{'f}{||}
   <-->
   nil

interactive_rw reduce_vdlist_left :
   vdlist{'f}{| x: 'A; <J['x]> |}
   <-->
   'A :: vdlist{'f}{| <J['f 'A]> |}

interactive vdlist_nil_wf :
   [wf] sequent { <H> >- 'A Type } -->
   sequent { <H> >- vdlist{'f}{||} in list{'A} }

interactive vdlist_left_wf :
   [wf] sequent { <H> >- 'e in 'A } -->
   [wf] sequent { <H> >- vdlist{'f}{| <J['f 'e]> |} in list{'A} } -->
   sequent { <H> >- vdlist{'f}{| x: 'e; <J['x]> |} in list{'A} }

doc docoff

doc <:doc<
   A vdlist is @emph{always} a list.
>>
interactive vdlist_wf {| intro [] |} :
   sequent { <H> >- vdlist{'f}{| <J> |} in list }

doc <:doc<
   The @refmodule[Itt_list2] module defines a conditional rewrite
   << 'l in list => 'l ~ list_of_fun{i. nth{'l; 'i}; length{'l}} >>.
   Define an equivalent form that is unconditional.
>>
interactive_rw vdlist_of_nil 'f :
   nil
   <-->
   vdlist{'f}{||}

interactive_rw expand_vdlist_left :
   'A :: vdlist{'f}{| <J> |}
   <-->
   vdlist{'f}{| 'A; <J> |}

interactive_rw list_of_fun_of_vdlist :
   vdlist{'f}{| <J> |}
   <-->
   list_of_fun{i. nth{vdlist{'f}{| <J> |}; 'i}; length{vdlist{'f}{| <J> |}}}

(************************************************************************
 * An expanded wf property for the lists.
 *)
doc <:doc<
   The term <:xterm< vlistwf{A; B; C}{| <J> >- D |} >> specifies that
   if all the hyp bindings have type << 'A >>, then the hyp values
   have type << 'B >>, and the conclusion has type << 'C >>.
>>
declare sequent [vlistwf{'A; 'B; 'C}] { Term : Term >- Term } : Term

prim_rw unfold_vlistwf : <:xrewrite<
   vlistwf{A; B; C}{| <J> >- D |}
   <-->
   sequent_ind{u, v. (u in B) && (all x: A. happly{v; x}); TermSequent{| <J> >- D in C |}}
>>

declare sequent [vlistlistwf] { Term : Term >- Term } : Term

prim_rw unfold_vlistlistwf : <:xrewrite<
   vlistlistwf{| <J> >- C |}
   <-->
   vlistwf{top; list; top}{| <J> >- C |}
>>

interactive_rw reduce_vlistwf_concl : <:xrewrite<
   vlistwf{A; B; C}{| >- D |}
   <-->
   D in C
>>

interactive_rw reduce_vlistwf_left : <:xrewrite<
   vlistwf{A; B; C}{| x: e; <J[x]> >- D[x] |}
   <-->
   (e in B) && (all x: A. vlistwf{A; B; C}{| <J[x]> >- D[x] |})
>>

interactive_rw reduce_vlistlistwf_concl : <:xrewrite<
   vlistlistwf{| >- C |}
   <-->
   C in top
>>

interactive_rw reduce_vlistlistwf_left : <:xrewrite<
   vlistlistwf{| x: A; <J[x]> >- C[x] |}
   <-->
   (A in list) && (all x: top. vlistlistwf{| <J[x]> >- C[x] |})
>>

interactive vlistlistwf_concl {| intro |} : <:xrule<
   <H> >- vlistlistwf{| >- C |}
>>

interactive vlistlistwf_left {| intro |} : <:xrule<
   "wf" : <H> >- A in list -->
   "wf" : <H>; x: top >- vlistlistwf{| <J[x]> >- C[x] |} -->
   <H> >- vlistlistwf{| x: A; <J[x]> >- C[x] |}
>>

interactive vlistlistwf_elim_concl {| elim |} 'H : <:xrule<
   <H>; <J[it]> >- D[it] -->
   <H>; x: vlistlistwf{| >- C |}; <J[x]> >- D[x]
>>

interactive vlistlistwf_elim_left {| elim |} 'H : <:xrule<
   <H>; u: A in list; v: (all y: top. vlistlistwf{| <J[y]> >- C[y] |}); <K[(u, v)]> >- D[(u, v)] -->
   <H>; x: vlistlistwf{| y: A; <J[y]> >- C[y] |}; <K[x]> >- D[x]
>>

doc <:doc<
   Length properties.
>>
interactive lemma : <:xrule<
   <H> >- f in top -> list -->
   <H> >- f e = f it in list
>>


(************************************************************************
 * Tactics.
 *)

(************************************************************************
 * Display forms.
 *)
dform vlist_df : vdlist{'f}{| <H> >- 'C |} =
   szone pushm[3] `"vdlist{" slot{'f} `"}[" display_sequent{vdlist{'f}{| <H> >- 'C |}} `"]" popm ezone

dform vlist_hyp_df : display_hyp{vdlist{'f}; v. 'e} =
   slot{'e}

dform vlist_concl_df : display_concl{vdlist{'f}; xconcl} =
   `""

dform vlist_concl_df2 : display_concl{vdlist{'f}; 'C} =
   slot{'C}

dform vlistlistwf_df : vlistlistwf{| <H> >- 'C |} =
   szone pushm[3] `"vlistlistwf[" display_sequent{vlistlistwf{| <H> >- 'C |}} `"]" popm ezone

dform vlistlistwf_hyp_df : display_hyp{vlistlistwf; v. 'e} =
   slot{'e}

dform vlistlistwf_concl_df : display_concl{vlistlistwf; xconcl} =
   `""

dform vlistlistwf_concl_df2 : display_concl{vlistlistwf; 'C} =
   slot{'C}

(*
 * -*-
 * Local Variables:
 * Fill-column: 120
 * End:
 * -*-
 * vim:ts=3:et:tw=120
 *)
