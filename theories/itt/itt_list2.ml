doc <:doc< 
   @begin[doc]
   @module[Itt_list2]
  
   The @tt{Itt_list2} module defines a ``library'' of
   additional operations on the lists defined in
   the @hrefmodule[Itt_list] module.
   @end[doc]
  
   ----------------------------------------------------------------
  
   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.
  
   See the file doc/index.html for information on Nuprl,
   OCaml, and more information about this system.
  
   Copyright (C) 1998 Jason Hickey, Cornell University
  
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
  
   Author: Jason Hickey @email{jyh@cs.cornell.edu}
   Modified By: Aleksey Nogin @email{nogin@cs.cornell.edu}
   @end[license]
>>

doc <:doc< @doc{@parents} >>
extends Itt_list
extends Itt_logic
extends Itt_bool
extends Itt_int_base
extends Itt_int_ext
extends Itt_int_arith
doc <:doc< @docoff >>

open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.RefineError
open Mp_resource

open Tactic_type
open Tactic_type.Tacticals
open Var

open Dtactic
open Typeinf
open Top_conversionals

open Itt_equal
open Itt_list
open Itt_rfun
open Itt_dprod

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

doc <:doc< 
   @begin[doc]
   @terms
  
   The @tt{is_nil} term defines a Boolean value that is true
   @emph{iff} the argument list $l$ is empty.
   @end[doc]
>>
define unfold_is_nil :
   is_nil{'l} <--> list_ind{'l; btrue; h, t, g. bfalse}

doc <:doc< 
   @begin[doc]
   @terms
  
   The @tt[mem] term defines list membership.
   @end[doc]
>>
define unfold_mem :
   mem{'x; 'l; 'T} <-->
      list_ind{'l; "false"; h, t, g. "or"{('x = 'h in 'T); 'g}}

doc <:doc< 
   @begin[doc]
   @terms
  
   The @tt{subset} term determines whether the elements in $l_1$ are also
   in $l_2$.
   @end[doc]
>>
define unfold_subset :
   \subset{'l1; 'l2; 'T} <-->
      list_ind{'l1; "true"; h, t, g. "and"{mem{'h; 'l2; 'T}; 'g}}

doc <:doc< 
   @begin[doc]
   @terms
  
   The @tt[sameset] term determines whether the two lists contain the same
   set of elements.
   @end[doc]
>>
define unfold_sameset :
   sameset{'l1; 'l2; 'T} <-->
      "and"{\subset{'l1; 'l2; 'T}; \subset{'l2; 'l1; 'T}}

doc <:doc< 
   @begin[doc]
   @noindent
   The @tt{append} term takes two lists and concatenates them.
   @end[doc]
>>
define unfold_append :
   append{'l1; 'l2} <-->
      list_ind{'l1; 'l2; h, t, g. 'h :: 'g}

doc <:doc< 
   @begin[doc]
   @noindent
   The @tt{ball2} term defines a Boolean universal quantification
   over two lists.  The test $b[x, y]$ must compute a Boolean value
   given elements of the two lists, and the test is $@bfalse$ if
   the lists have different lengths.
   @end[doc]
>>
define unfold_ball2 :
   ball2{'l1; 'l2; x, y. 'b['x; 'y]} <-->
      (list_ind{'l1; lambda{z. list_ind{'z; btrue; h, t, g. bfalse}};
                     h1, t1, g1. lambda{z. list_ind{'z; bfalse;
                     h2, t2, g2. band{'b['h1; 'h2]; .'g1 't2}}}} 'l2)

doc <:doc< 
   @begin[doc]
   @noindent
   The @tt[assoc] term defines an associative lookup on
   the list $l$.  The list $l$ should be a list of pairs.
   The @tt[assoc] term searches for the element $x$ as
   the first element of one of the pairs.  On the first
   occurrence of a pair $(x, y)$, the value $b[y]$ is returned.
   The $z$ term is returned if a pair is not found.
   @end[doc]
>>
define unfold_assoc :
   assoc{'eq; 'x; 'l; y. 'b['y]; 'z} <-->
      list_ind{'l; 'z; h, t, g.
         spread{'h; u, v.
            ifthenelse{.'eq 'u 'x; 'b['v]; 'g}}}

doc <:doc< 
   @begin[doc]
   @noindent
   The @tt[rev_assoc] term also performs an associative search,
   but it keys on the second element of each pair.
   @end[doc]
>>
define unfold_rev_assoc :
   rev_assoc{'eq; 'x; 'l; y. 'b['y]; 'z} <-->
      list_ind{'l; 'z; h, t, g.
         spread{'h; u, v.
            ifthenelse{.'eq 'v 'x; 'b['u]; 'g}}}

doc <:doc< 
   @begin[doc]
   @noindent
   The @tt{map} term applies the function $f$ to each element
   of the list $l$, and returns the list of the results (in
   the same order).
   @end[doc]
>>
define unfold_map : map{'f; 'l} <-->
   list_ind{'l; nil; h, t, g. cons{.'f 'h; 'g}}

doc <:doc< 
   @begin[doc]
   @noindent
   The @tt{fold_left} term applies the function $f$ to each element
   of the list $l$, together with an extra argument $v$.  The result
   of each computation is passed as the argument $v$ to the
   next stage of the computation.
   @end[doc]
>>
define unfold_fold_left :
   fold_left{'f; 'v; 'l} <-->
      (list_ind{'l; lambda{v. 'v}; h, t, g. lambda{v. 'g ('f 'h 'v)}} 'v)

doc <:doc< 
   @begin[doc]
   @noindent
   The @tt[nth] term returns element $i$ of list $l$.
   The argument $i$ must be within the bounds of the list.
   @end[doc]
>>
define unfold_nth :
   nth{'l; 'i} <-->
      (list_ind{'l; it; u, v, g. lambda{j. ifthenelse{beq_int{'j; 0}; 'u; .'g ('j -@ 1)}}} 'i)

doc <:doc< 
   @begin[doc]
   @noindent
   The @tt[replace_nth] term replace element $i$ of list $l$
   with the term $v$.
   @end[doc]
>>
define unfold_replace_nth :
   replace_nth{'l; 'i; 't} <-->
      (list_ind{'l; nil; u, v, g. lambda{j. ifthenelse{beq_int{'j; 0}; cons{'t; 'v}; cons{'u; .'g ('j -@ 1)}}}} 'i)

doc <:doc< 
   @begin[doc]
   @noindent
   The @tt{length} term returns the total number of elements in
   the list $l$.
   @end[doc]
>>
define unfold_length :
   length{'l} <--> list_ind{'l; 0; u, v, g. 'g +@ 1}

doc <:doc< 
   @begin[doc]
   @noindent
   The @tt[rev] function returns a list with the same elements as
   list $l$, but in reverse order.
   @end[doc]
>>
define unfold_rev : rev{'l} <-->
   list_ind{'l; nil; u, v, g. append{'g; cons{'u; nil} }}
doc <:doc< @docoff >>

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

prec prec_append
prec prec_ball
prec prec_assoc

dform is_nil_df : except_mode[src] :: parens :: "prec"[prec_equal] :: is_nil{'l} =
   slot{'l} `" =" subb `" []"

dform mem_df : except_mode[src] :: mem{'x; 'l; 'T} =
   `"(" slot{'x} " " Nuprl_font!member `" " slot{'l} `" in " slot{'T} `")"

dform subset_df : except_mode[src] :: \subset{'l1; 'l2; 'T} =
   `"(" slot{'l1} " " Nuprl_font!subseteq `"[" slot{'T} `"] " slot{'l2} `")"

dform sameset_df : except_mode[src] :: sameset{'l1; 'l2; 'T} =
   (keyword["sameset"] 'l1 'l2 'T)

dform append_df : except_mode[src] :: parens :: "prec"[prec_append] :: append{'l1; 'l2} =
   slot{'l1} `" @" space slot{'l2}

dform ball2_df : except_mode[src] :: parens :: "prec"[prec_ball] :: ball2{'l1; 'l2; x, y. 'b} =
   pushm[3] Nuprl_font!forall subb slot{'x} `", " slot{'y} space
      Nuprl_font!member space slot{'l1} `", " slot{'l2} sbreak["",". "]
      slot{'b} popm

dform assoc_df : except_mode[src] :: parens :: "prec"[prec_assoc] :: assoc{'eq; 'x; 'l; v. 'b; 'z} =
   szone pushm[0] pushm[3]
   `"try" hspace
      pushm[3]
      `"let " slot{'v} `" = assoc " slot{'x} space Nuprl_font!member slot{'eq} space slot{'l} popm hspace
      pushm[3] `"in" hspace
      slot{'b} popm popm hspace
   pushm[3] `"with Not_found ->" hspace
   slot{'z} popm popm ezone

dform rev_assoc_df : except_mode[src] :: parens :: "prec"[prec_assoc] :: rev_assoc{'eq; 'x; 'l; v. 'b; 'z} =
   szone pushm[0] pushm[3]
   `"try" hspace
      pushm[3]
      `"let " slot{'v} `" = rev_assoc " slot{'x} space Nuprl_font!member slot{'eq} space slot{'l} popm hspace
      pushm[3] `"in" hspace
      slot{'b} popm popm hspace
   pushm[3] `"with Not_found ->" hspace
   slot{'z} popm popm ezone

dform map_df : except_mode[src] :: parens :: "prec"[prec_apply] :: map{'f; 'l} =
   `"map" space slot{'f} space slot{'l}

dform fold_left_df : except_mode[src] :: fold_left{'f; 'v; 'l} =
   `"fold_left(" slot{'f} `", " slot{'v} `", " slot{'l} `")"

dform length_df : except_mode[src] :: length{'l} =
   `"length(" slot{'l} `")"

dform nth_df : except_mode[src] :: nth{'l; 'i} =
   `"nth(" slot{'l} `", " slot{'i} `")"

dform replace_nth_df : except_mode[src] :: replace_nth{'l; 'i; 'v} =
   szone `"replace_nth(" pushm[0] slot{'l} `"," hspace slot{'i} `"," hspace slot{'v} `")" popm ezone

dform rev_df : except_mode[src] :: rev{'l} =
   `"rev(" slot{'l} `")"

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

doc <:doc< 
   @begin[doc]
   @rewrites
  
   The @hrefterm[is_nil] term is defined with the
   @hrefterm[list_ind] term, with a base case $@btrue$,
   and step case $@bfalse$.
   @end[doc]
>>
interactive_rw reduce_is_nil_nil {| reduce |} : is_nil{nil} <--> btrue

interactive_rw reduce_is_nil_cons {| reduce |} : is_nil{cons{'h; 't}} <--> bfalse
doc docoff

let fold_is_nil = makeFoldC << is_nil{'l} >> unfold_is_nil

doc <:doc< 
   @begin[doc]
   The @hrefterm[mem] term performs induction over the list.
   @end[doc]
>>
interactive_rw reduce_mem_nil {| reduce |} : mem{'x; nil; 'T} <--> "false"

interactive_rw reduce_mem_cons {| reduce |} :
   mem{'x; cons{'u; 'v}; 'T} <--> "or"{('x = 'u in 'T); mem{'x; 'v; 'T}}
doc docoff

let fold_mem = makeFoldC << mem{'x; 'l; 'T} >> unfold_mem

doc <:doc< 
   @begin[doc]
   The @hrefterm[subset] term performs induction over the first list.
   @end[doc]
>>
interactive_rw reduce_subset_nil {| reduce |} : \subset{nil; 'l; 'T} <--> "true"

interactive_rw reduce_subset_cons {| reduce |} : 
   \subset{cons{'u; 'v}; 'l; 'T} <--> "and"{mem{'u; 'l; 'T}; \subset{'v; 'l; 'T}}

doc docoff

let fold_subset = makeFoldC << \subset{'l1; 'l2; 'T} >> unfold_subset

let fold_sameset = makeFoldC << sameset{'l1; 'l2; 'T} >> unfold_sameset

doc <:doc< 
   @begin[doc]
   The @hrefterm[append] term performs induction over the
   first list.
   @end[doc]
>>
interactive_rw reduce_append_nil {| reduce |} : append{nil; 'l2} <--> 'l2

interactive_rw reduce_append_cons {| reduce |} :
   append{cons{'x; 'l1}; 'l2} <--> cons{'x; append{'l1; 'l2}}

doc docoff

let fold_append = makeFoldC << append{'l1; 'l2} >> unfold_append

doc <:doc< 
   @begin[doc]
   The @hrefterm[ball2] term performs simultaneous induction
   over both lists, comparing the elements of the lists with
   the comparison $b[x, y]$.
   @end[doc]
>>
interactive_rw reduce_ball2_nil_nil {| reduce |} :
   ball2{nil; nil; x, y. 'b['x; 'y]} <--> btrue

interactive_rw reduce_ball2_nil_cons {| reduce |} :
   ball2{nil; cons{'h; 't}; x, y.'b['x; 'y]} <--> bfalse

interactive_rw reduce_ball2_cons_nil {| reduce |} :
   ball2{cons{'h; 't}; nil; x, y. 'b['x; 'y]} <--> bfalse

interactive_rw reduce_ball2_cons_cons {| reduce |} :
   ball2{cons{'h1; 't1}; cons{'h2; 't2}; x, y. 'b['x; 'y]} <-->
      band{'b['h1; 'h2]; ball2{'t1; 't2; x, y. 'b['x; 'y]}}
      
doc docoff

let fold_ball2 = makeFoldC << ball2{'l1; 'l2; x, y. 'b['x; 'y]} >> unfold_ball2

doc <:doc< 
   @begin[doc]
   The @hrefterm[assoc] term performs induction over the list,
   splitting each pair and comparing it with the key.
   @end[doc]
>>
interactive_rw reduce_assoc_nil {| reduce |} :
   assoc{'eq; 'x; nil; y. 'b['y]; 'z} <--> 'z

interactive_rw reduce_assoc_cons {| reduce |} :
   assoc{'eq; 'x; cons{pair{'u; 'v}; 'l}; y. 'b['y]; 'z} <-->
      ifthenelse{.'eq 'u 'x; 'b['v]; assoc{'eq; 'x; 'l; y. 'b['y]; 'z}}

doc docoff

let fold_assoc = makeFoldC << assoc{'eq; 'x; 'l; v. 'b['v]; 'z} >> unfold_assoc

doc <:doc< 
   @begin[doc]
   The @hrefterm[rev_assoc] term also performs induction over the list,
   but it keys on the second element of each pair.
   @end[doc]
>>
interactive_rw reduce_rev_assoc_nil {| reduce |} :
   rev_assoc{'eq; 'x; nil; y. 'b['y]; 'z} <--> 'z

interactive_rw reduce_rev_assoc_cons {| reduce |} :
   rev_assoc{'eq; 'x; cons{pair{'u; 'v}; 'l}; y. 'b['y]; 'z} <-->
      ifthenelse{.'eq 'v 'x; 'b['u]; rev_assoc{'eq; 'x; 'l; y. 'b['y]; 'z}}

doc docoff

let fold_rev_assoc = makeFoldC << rev_assoc{'eq; 'x; 'l; v. 'b['v]; 'z} >> unfold_rev_assoc

doc <:doc< 
   @begin[doc]
   The @hrefterm[map] term performs induction over the list $l$,
   applying the function to each element, and collecting the results.
   @end[doc]
>>
interactive_rw reduce_map_nil {| reduce |} :
   map{'f; nil} <--> nil

interactive_rw reduce_map_cons {| reduce |} :
   map{'f; cons{'h; 't}} <--> cons{.'f 'h; map{'f; 't}}

doc docoff

let fold_map = makeFoldC << map{'f; 'l} >> unfold_map

doc <:doc< 
   @begin[doc]
   The @hrefterm[fold_left] term performs induction over the
   list argument, applying the function to the head element
   and the argument computed by the previous stage of the computation.
   @end[doc]
>>
interactive_rw reduce_fold_left_nil {| reduce |} :
   fold_left{'f; 'v; nil} <--> 'v

interactive_rw reduce_fold_left_cons {| reduce |} :
   fold_left{'f; 'v; cons{'h; 't}} <-->
   fold_left{'f; .'f 'h 'v; 't}

doc docoff

let fold_fold_left = makeFoldC << fold_left{'f; 'v; 'l} >> unfold_fold_left

doc <:doc< 
   @begin[doc]
   The @hrefterm[length] function counts the total number of elements in the
   list.
   @end[doc]
>>
interactive_rw reduce_length_nil {| reduce |} : length{nil} <--> 0

interactive_rw reduce_length_cons {| reduce |} : length{cons{'u; 'v}} <--> (length{'v} +@ 1)

doc docoff

let fold_length = makeFoldC << length{'l} >> unfold_length

doc <:doc< 
   @begin[doc]
   The @hrefterm[nth] term performs induction over the
   list, comparing the index to 0 at each step and returning the head element
   if it reaches 0.  The $@it$ term is returned if the index never reaches 0.
   @end[doc]
>>
interactive_rw reduce_nth_cons {| reduce |} :
   nth{cons{'u; 'v}; 'i} <--> ifthenelse{beq_int{'i; 0}; 'u; nth{'v; .'i -@ 1}}

doc docoff

let fold_nth = makeFoldC << nth{'l; 'i} >> unfold_nth

doc <:doc< 
   @begin[doc]
   The @hrefterm[replace_nth] term is similar to the @hrefterm[nth]
   term, but it collects the list, and replaces the head element
   when the index reaches 0.
   @end[doc]
>>
interactive_rw reduce_replace_nth_cons {| reduce |} :
   replace_nth{cons{'u; 'v}; 'i; 't} <-->
      ifthenelse{beq_int{'i; 0}; cons{'t; 'v}; cons{'u; replace_nth{'v; .'i -@ 1; 't}}}

doc docoff

let fold_replace_nth = makeFoldC << replace_nth{'l; 'i; 't} >> unfold_replace_nth

doc <:doc< 
   @begin[doc]
   The @hrefterm[rev] term reverses the list.
   This particular computation is rather inefficient;
   it appends the head of the list to the reversed tail.
   @end[doc]
>>
interactive_rw reduce_rev_nil {| reduce |} : rev{nil} <--> nil

interactive_rw reduce_rev_cons {| reduce |} : rev{cons{'u;'v}} <--> append{rev{'v};cons{'u;nil}}

doc docoff

let fold_rev = makeFoldC << rev{'l} >> unfold_rev

(************************************************************************
 * REDUCTION                                                            *
 ************************************************************************)

(* We need a proper implementation of rewrites in order to do this.

interactive_rw append_nil {| reduce |} 'A :
   [wf] sequent [squash] { <H> >- "type"{'A} } -->
   [wf] sequent [squash] { <H> >- 'l in list{'A} } -->
   sequent ['ext] { <H>>- append{'l;nil} <--> 'l }

interactive_rw rev_append {| reduce |} :
   [wf] sequent [squash] { <H> >- "type"{'A} } -->
   [wf] sequent [squash] { <H> >- 'a in list{'A} } -->
   [wf] sequent [squash] { <H> >- 'b in list{'A} } -->
   sequent ['ext] { <H>>- rev{append{'a;'b}} <--> append{rev{'b};rev{'a}} }

interactive_rw rev2 {| reduce |} :
   [wf] sequent [squash] { <H> >- "type"{'A} } -->
   [wf] sequent [squash] { <H> >- 'l in list{'A} } -->
   sequent ['ext] { <H>>- rev{rev{'l}} <--> 'l }

*)

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

doc <:doc< 
   @begin[doc]
   @rules
  
   The rules in the @hrefmodule[Itt_list2] are limited to
   well-formedness of each of the constructions.
   @end[doc]
>>
interactive is_nil_wf {| intro [intro_typeinf <<'l>>] |} list{'T} :
   [wf] sequent [squash] { <H> >- 'l in list{'T} } -->
   sequent ['ext] { <H> >- is_nil{'l} in bool }

(*
 * Membership.
 *)
interactive mem_wf {| intro [] |} :
   [wf] sequent [squash] { <H> >- "type"{'T} } -->
   [wf] sequent [squash] { <H> >- 'x in 'T } -->
   [wf] sequent [squash] { <H> >- 'l in list{'T} } -->
   sequent ['ext] { <H> >- "type"{mem{'x; 'l; 'T}} }

(*
 * Subset.
 *)
interactive subset_wf {| intro [] |} :
   [wf] sequent [squash] { <H> >- "type"{'T} } -->
   [wf] sequent [squash] { <H> >- 'l1 in list{'T} } -->
   [wf] sequent [squash] { <H> >- 'l2 in list{'T} } -->
   sequent ['ext] { <H> >- "type"{\subset{'l1; 'l2; 'T}} }

(*
 * Sameset.
 *)
interactive sameset_wf {| intro [] |} :
   [wf] sequent [squash] { <H> >- "type"{'T} } -->
   [wf] sequent [squash] { <H> >- 'l1 in list{'T} } -->
   [wf] sequent [squash] { <H> >- 'l2 in list{'T} } -->
   sequent ['ext] { <H> >- "type"{sameset{'l1; 'l2; 'T}} }

(*
 * Append.
 *)
interactive append_wf2 {| intro [] |} :
   [wf] sequent [squash] { <H> >- 'l1 in list{'T} } -->
   [wf] sequent [squash] { <H> >- 'l2 in list{'T} } -->
   sequent ['ext] { <H> >- append{'l1; 'l2} in list{'T} }

(*
 * Ball2.
 *)
interactive ball2_wf2 {| intro [] |} 'T1 'T2 :
   [wf] sequent [squash] { <H> >- "type"{'T1} } -->
   [wf] sequent [squash] { <H> >- "type"{'T2} } -->
   [wf] sequent [squash] { <H> >- 'l1 in list{'T1} } -->
   [wf] sequent [squash] { <H> >- 'l2 in list{'T2} } -->
   [wf] sequent [squash] { <H>; u: 'T1; v: 'T2 >- 'b['u; 'v] in bool } -->
   sequent ['ext] { <H> >- ball2{'l1; 'l2; x, y. 'b['x; 'y]} in bool }

(*
 * assoc2.
 *)
interactive assoc_wf {| intro [intro_typeinf <<'l>>] |} 'z list{.'T1 * 'T2} :
   [wf] sequent [squash] { <H> >- "type"{'T2} } -->
   [wf] sequent [squash] { <H> >- 'eq in 'T1 -> 'T1 -> bool } -->
   [wf] sequent [squash] { <H> >- 'x in 'T1 } -->
   [wf] sequent [squash] { <H> >- 'l in list{.'T1 * 'T2} } -->
   [wf] sequent [squash] { <H>; z: 'T2 >- 'b['z] in 'T } -->
   [wf] sequent [squash] { <H> >- 'z in 'T } -->
   sequent ['ext] { <H> >- assoc{'eq; 'x; 'l; v. 'b['v]; 'z} in 'T }

interactive rev_assoc_wf {| intro [intro_typeinf <<'l>>] |} 'z list{.'T1 * 'T2} :
   [wf] sequent [squash] { <H> >- "type"{'T1} } -->
   [wf] sequent [squash] { <H> >- 'eq in 'T2 -> 'T2 -> bool } -->
   [wf] sequent [squash] { <H> >- 'x in 'T2 } -->
   [wf] sequent [squash] { <H> >- 'l in list{.'T1 * 'T2} } -->
   [wf] sequent [squash] { <H>; z: 'T1 >- 'b['z] in 'T } -->
   [wf] sequent [squash] { <H> >- 'z in 'T } -->
   sequent ['ext] { <H> >- rev_assoc{'eq; 'x; 'l; v. 'b['v]; 'z} in 'T }

(*
 * map.
 *)
interactive map_wf {| intro [intro_typeinf <<'l>>] |} list{'T1} :
   [wf] sequent [squash] { <H> >- "type"{'T1} } -->
   [wf] sequent [squash] { <H> >- "type"{'T2} } -->
   [wf] sequent [squash] { <H> >- 'f in 'T1 -> 'T2 } -->
   [wf] sequent [squash] { <H> >- 'l in list{'T1} } -->
   sequent ['ext] { <H> >- map{'f; 'l} in list{'T2} }

(*
 * Fold_left.
 *)
interactive fold_left_wf {| intro [intro_typeinf <<'l>>] |} list{'T1} :
   [wf] sequent [squash] { <H> >- "type"{'T1} } -->
   [wf] sequent [squash] { <H> >- "type"{'T2} } -->
   [wf] sequent [squash] { <H> >- 'f in 'T1 -> 'T2 -> 'T2 } -->
   [wf] sequent [squash] { <H> >- 'v in 'T2 } -->
   [wf] sequent [squash] { <H> >- 'l in list{'T1} } -->
   sequent ['ext] { <H> >- fold_left{'f; 'v; 'l} in 'T2 }

(*
 * Length.
 *)
interactive length_wf {| intro [intro_typeinf <<'l>>] |} list{'T1} :
   [wf] sequent [squash] { <H> >- "type"{'T1} } -->
   [wf] sequent [squash] { <H> >- 'l in list{'T1} } -->
   sequent ['ext] { <H> >- length{'l} in int }

interactive nth_wf {| intro [] |} :
   [wf] sequent [squash] { <H> >- "type"{'T} } -->
   [wf] sequent [squash] { <H> >- 'l in list{'T} } -->
   [wf] sequent [squash] { <H> >- ge{'i; 0} } -->
   [wf] sequent [squash] { <H> >- lt{'i; length{'l}} } -->
   [wf] sequent [squash] { <H> >- 'i in int } -->
   sequent ['ext] { <H> >- nth{'l; 'i} in 'T }

interactive replace_nth_wf {| intro [] |} :
   [wf] sequent [squash] { <H> >- "type"{'T} } -->
   [wf] sequent [squash] { <H> >- 'l in list{'T} } -->
   [wf] sequent [squash] { <H> >- ge{'i; 0} } -->
   [wf] sequent [squash] { <H> >- lt{'i; length{'l}} } -->
   [wf] sequent [squash] { <H> >- 'i in int } -->
   [wf] sequent [squash] { <H> >- 't in 'T } -->
   sequent ['ext] { <H> >- replace_nth{'l; 'i; 't} in list{'T} }

(*
 * Reverse.
 *)
interactive rev_wf {| intro [] |} :
   [wf] sequent [squash] { <H> >- "type"{'A} } -->
   [wf] sequent [squash] { <H> >- 'l in list{'A} } -->
   sequent ['ext] { <H> >- rev{'l} in list{'A} }
doc <:doc< @docoff >>

doc <:doc< 
   @begin[doc]
   @rules
  
   A list $v$ is a subset of the list <<cons{'u; 'v}>>.
   @end[doc]
>>
interactive subset_cons {| intro [AutoMustComplete] |} :
   [wf] sequent [squash] { <H> >- "type"{'A} } -->
   [wf] sequent [squash] { <H> >- 'u in 'A } -->
   [wf] sequent [squash] { <H> >- 'v in list{'A} } -->
   [wf] sequent [squash] { <H> >- 'l in list{'A} } -->
   sequent ['ext] { <H> >- \subset{'v; 'l; 'A} } -->
   sequent ['ext] { <H> >- \subset{'v; cons{'u; 'l}; 'A} }

doc <:doc< 
   @begin[doc]
   @rules
  
   @tt[subset] is reflexive and transitive.
   @end[doc]
>>
interactive subset_ref {| intro [] |} :
   [wf] sequent [squash] { <H> >- "type"{'A} } -->
   [wf] sequent [squash] { <H> >- 'l in list{'A} } -->
   sequent ['ext] { <H> >- \subset{'l; 'l; 'A} }

interactive subset_trans 'l2 :
   [wf] sequent [squash] { <H> >- "type"{'A} } -->
   [wf] sequent [squash] { <H> >- 'l1 in list{'A} } -->
   [wf] sequent [squash] { <H> >- 'l2 in list{'A} } -->
   [wf] sequent [squash] { <H> >- 'l3 in list{'A} } -->
   sequent ['ext] { <H> >- \subset{'l1; 'l2; 'A} } -->
   sequent ['ext] { <H> >- \subset{'l2; 'l3; 'A} } -->
   sequent ['ext] { <H> >- \subset{'l1; 'l3; 'A} }

doc <:doc< 
   @begin[doc]
   @rules
  
   @tt[sameset] is reflexive, symmetric, and transitive.
   @end[doc]
>>
interactive sameset_ref {| intro [] |} :
   [wf] sequent [squash] { <H> >- "type"{'A} } -->
   [wf] sequent [squash] { <H> >- 'l in list{'A} } -->
   sequent ['ext] { <H> >- sameset{'l; 'l; 'A} }

interactive sameset_sym :
   [wf] sequent [squash] { <H> >- "type"{'A} } -->
   [wf] sequent [squash] { <H> >- 'l1 in list{'A} } -->
   [wf] sequent [squash] { <H> >- 'l2 in list{'A} } -->
   sequent ['ext] { <H> >- sameset{'l1; 'l2; 'A} } -->
   sequent ['ext] { <H> >- sameset{'l2; 'l1; 'A} }

interactive sameset_trans 'l2 :
   [wf] sequent [squash] { <H> >- "type"{'A} } -->
   [wf] sequent [squash] { <H> >- 'l1 in list{'A} } -->
   [wf] sequent [squash] { <H> >- 'l2 in list{'A} } -->
   [wf] sequent [squash] { <H> >- 'l3 in list{'A} } -->
   sequent ['ext] { <H> >- sameset{'l1; 'l2; 'A} } -->
   sequent ['ext] { <H> >- sameset{'l2; 'l3; 'A} } -->
   sequent ['ext] { <H> >- sameset{'l1; 'l3; 'A} }
doc <:doc< @docoff >>

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let ball2_term = << ball2{'l1; 'l2; x, y. 'b['x; 'y]} >>
let ball2_opname = opname_of_term ball2_term
let is_ball2_term = is_dep0_dep0_dep2_term ball2_opname
let mk_ball2_term = mk_dep0_dep0_dep2_term ball2_opname
let dest_ball2 = dest_dep0_dep0_dep2_term ball2_opname

let samesetSymT = sameset_sym
let samesetTransT = sameset_trans

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
