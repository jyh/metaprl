doc <:doc<
   @module[Itt_hoas_lang]
   The @tt[Itt_hoas_lang] module defines the type of a language over
   a list of operators.

   If <<'ops>> is a list of operators, then <<Lang{'ops}>> is a
   subtype of type <<BTerm>> that contains all terms built
   with operators from the list <<'ops>>.


   @docoff
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

   Author: Xin Yu @email{xiny@cs.caltech.edu}

   @end[license]
>>

doc <:doc< @parents >>
extends Itt_hoas_bterm
doc docoff

open Basic_tactics

doc terms

doc <:doc<
     We define the type <<Lang{'ops}>> as the recursive type.

>>

define unfold_lang: Lang{'ops} <-->  { t: BTerm | dest_bterm{'t; l,r. "true"; d,op,ts. find{'ops; 'op; x,y.is_same_op{'x; 'y}} <> length{'ops}} }
doc docoff

let fold_lang = makeFoldC << Lang{'ops} >> unfold_lang

doc rules

interactive lang_wf  {| intro[] |} :
   sequent { <H> >- 'ops in list{Operator} } -->
   sequent { <H> >- Lang{'ops} Type }

interactive lang_subtype  {| intro[] |} :
   sequent { <H> >- 'ops in list{Operator} } -->
   sequent { <H> >- Lang{'ops} subtype BTerm }

interactive lang_induction  {| elim[] |} 'H:
   [wf] sequent { <H> >- 'ops in list{Operator} } -->
   [base] sequent { <H>; x: Lang{'ops}; <J['x]>; l: nat; r:nat >- 'P[var{'l;'r}] } -->
   [step] sequent { <H>; x: Lang{'ops}; <J['x]>; bdepth: nat; op:Operator; subterms:list{Lang{'ops}};
               compatible_shapes{'bdepth;'op;'subterms}(*; all_list{'subterms; t.'P['t]}*) >- 'P[mk_bterm{'bdepth;'op;'subterms}] } -->
   sequent { <H>; x: Lang{'ops}; <J['x]> >- 'P['x] }


interactive lang_intro_var {| intro[] |}:
   sequent{ <H> >- 'l in nat } -->
   sequent{ <H> >- 'r in nat } -->
   sequent { <H> >- 'ops in list{Operator} } -->
   sequent { <H> >- var{'l;'r} in Lang{'ops} }

interactive lang_intro1 {| intro[] |}:
   sequent{ <H> >- 'depth in nat } -->
   sequent{ <H> >- 'op in Operator } -->
   sequent{ <H> >- 'subterms in list{Lang{'ops}} } -->
   sequent { <H> >- 'ops in list{Operator} } -->
   sequent { <H> >- mem{'op;'ops;Operator}  } -->
   sequent { <H> >- all_list{'subterms;t.'t in Lang{'ops}} } -->
   sequent{ <H> >- compatible_shapes{'depth;'op;'subterms} } -->
   sequent{ <H> >- mk_bterm{'depth;'op;'subterms} in Lang{'ops} }

doc docoff

dform lang_df: Lang{'op} =
   tt["Language"] `"[" slot{'op} `"]"
