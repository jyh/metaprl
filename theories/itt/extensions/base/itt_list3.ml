doc <:doc<
   @module[Itt_list3]

   This is another library of list operations.

   ----------------------------------------------------------------

   @begin[license]
   Copyright (C) 2005 Mojave Group, Caltech

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

   Author: Jason Hickey
   @email{jyh@cs.caltech.edu}
   @end[license]

   @parents
>>
extends Itt_bool
extends Itt_dfun
extends Itt_image
extends Itt_list2
extends Itt_nat
extends Itt_pairwise

doc docoff

open Basic_tactics
open Itt_struct
open Itt_equal

(************************************************************************
 * Prefixes, suffixes, and elements.
 *)
doc <:doc<
   One of the reasons to define sloppy lists is to allow general lemmas
   about squiggle equality of lists.  The general form split the list using
   the << nth_prefix{'l; 'i} >> and << nth_suffix{'l; 'i} >> terms.
>>
define unfold_nth_prefix : nth_prefix{'l; 'i} <-->
   ind{'i; lambda{l. nil}; j, g. lambda{l. list_ind{'l; it; u, v, h. 'u :: 'g 'v}}} 'l

define unfold_nth_suffix : nth_suffix{'l; 'i} <-->
   ind{'i; lambda{l. 'l}; j, g. lambda{l. 'g tl{'l}}} 'l

interactive_rw reduce_nth_prefix_zero {| reduce |} :
   nth_prefix{'l; 0}
   <-->
   nil

interactive_rw reduce_nth_suffix_zero {| reduce |} :
   nth_suffix{'l; 0}
   <-->
   'l

interactive_rw reduce_nth_prefix_cons {| reduce |} :
   'i in nat -->
   nth_prefix{'u::'v; 'i +@ 1}
   <-->
   'u :: nth_prefix{'v; 'i}

interactive_rw reduce_nth_suffix_cons {| reduce |} :
   'i in nat -->
   nth_suffix{'l; 'i +@ 1}
   <-->
   nth_suffix{tl{'l}; 'i}

interactive_rw nth_suffix_swap_tl :
   'i in nat -->
   nth_suffix{tl{'l}; 'i}
   <-->
   tl{nth_suffix{'l; 'i}}

interactive_rw reduce_nth_nth_prefix {| reduce |} :
   'l in list -->
   'n in nat -->
   'n <= length{'l} -->
   'i in nat -->
   'i < 'n -->
   nth{nth_prefix{'l; 'n}; 'i}
   <-->
   nth{'l; 'i}

interactive_rw reduce_length_of_nth_prefix {| reduce |} :
   'l in list -->
   'i in nat -->
   'i <= length{'l} -->
   length{nth_prefix{'l; 'i}}
   <-->
   'i

interactive nth_prefix_wf {| intro [] |} :
   [wf] sequent { <H> >- 'l in list } -->
   [wf] sequent { <H> >- 'i in nat } -->
   [wf] sequent { <H> >- 'i <= length{'l} } -->
   sequent { <H> >- nth_prefix{'l; 'i} in list }

interactive_rw list_elements_id_elem :
   'l in list -->
   list_of_fun{k. nth{'l; 'k}; length{'l}}
   <-->
   'l

interactive_rw list_of_fun_nth_succ {| reduce |} :
   'n in nat -->
   list_of_fun{i. nth{'u::'v; 'i +@ 1}; 'n}
   <-->
   list_of_fun{i. nth{'v; 'i}; 'n}

interactive_rw list_of_fun_nth_succ2 :
   'n in nat -->
   list_of_fun{i. nth{'l; 'i +@ 1}; 'n}
   <-->
   list_of_fun{i. nth{tl{'l}; 'i}; 'n}

interactive_rw reduce_nth_prefix_append_lof {| reduce |} :
   'n in nat -->
   nth_prefix{append{list_of_fun{i.nth{'l1; 'i}; 'n}; 'l2}; 'n}
   <-->
   list_of_fun{i.nth{'l1; 'i}; 'n}

interactive_rw reduce_nth_suffix_append_lof {| reduce |} :
   'n in nat -->
   nth_suffix{append{list_of_fun{i.nth{'l1; 'i}; 'n}; 'l2}; 'n}
   <-->
   'l2

(************************************************************************
 * Squiggle equality.
 *)
doc <:doc<
   One of the reasons to define sloppy lists is to allow general lemmas
   about squiggle equality of lists.  The general form splits the list using
   the << nth_prefix{'l; 'i} >> and << nth_suffix{'l; 'i} >> terms.
>>
interactive split_list 'i :
   [wf] sequent { <H> >- 'l in list } -->
   [wf] sequent { <H> >- 'i in nat } -->
   [wf] sequent { <H> >- 'i <= length{'l} } -->
   sequent { <H> >- 'l ~ append{nth_prefix{'l; 'i}; nth_suffix{'l; 'i}} }

interactive_rw split_list_sqequal 'i ('l :> Term) :
   'l in list -->
   'i in nat -->
   'i <= length{'l} -->
   'l
   <-->
   append{nth_prefix{'l; 'i}; nth_suffix{'l; 'i}}

doc <:doc<
   This is a key equality lemma.  Two lists are equal if they are split
   at an arbitrary point, and the prefixes and suffixes are equal.
>>
interactive split_list_pair 'i :
   [wf] sequent { <H> >- 'l1 in list } -->
   [wf] sequent { <H> >- 'l2 in list } -->
   [wf] sequent { <H> >- 'i in nat } -->
   [wf] sequent { <H> >- 'i <= length{'l1} } -->
   [wf] sequent { <H> >- 'i <= length{'l2} } -->
   sequent { <H> >- append{nth_prefix{'l1; 'i}; nth_suffix{'l1; 'i}} ~ append{nth_prefix{'l2; 'i}; nth_suffix{'l2; 'i}} } -->
   sequent { <H> >- 'l1 ~ 'l2 }

(************************************************************************
 * Induction lemmas.
 *)
interactive_rw reduce_last_suffix_list :
   'e in list -->
   length{'e} = 'n in nat -->
   nth_suffix{'e; 'n}
   <-->
   nil

(************************************************************************
 * List_of_fun normalization.
 *)
interactive_rw nth_prefix_lof :
   'n in nat -->
   'm in nat -->
   'm <= 'n -->
   nth_prefix{list_of_fun{i. 'f['i]; 'n}; 'm}
   <-->
   list_of_fun{i. 'f['i]; 'm}

interactive_rw nth_suffix_lof :
   'n in nat -->
   'm in nat -->
   'm <= 'n -->
   nth_suffix{list_of_fun{i. 'f['i]; 'n}; 'm}
   <-->
   list_of_fun{i. 'f['i +@ 'm]; 'n -@ 'm}

let normalizeListOfFunC = idC

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
