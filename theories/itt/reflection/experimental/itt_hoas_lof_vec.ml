doc <:doc<
   @module[Itt_hoas_lof_vec]

   Vector counterparts for @hrefterm[lof] normalization.

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

   Author: Jason Hickey @email{jyh@cs.caltech.edu}

   @end[license]
   @parents
>>
extends Itt_hoas_vbind
extends Itt_hoas_lof
extends Itt_vec_list1

doc docoff

open Basic_tactics
open Itt_hoas_lof

doc <:doc<
   The vector binder.
>>
declare sequent [lof_vbind] { Term : Term >- Term } : Term

prim_rw unfold_lof_vbind : lof_vbind{| <J> >- 'e |} <-->
   vbind{| <J> >- 'e |}

(************************************************************************
 * Bind-pushing.
 *)
doc <:doc<
   Bind migration for vector binders << lof_vbind{| <J> >- 'e |} >>.
>>
interactive_rw lof_vbind_nil {| reduce_lof |} :
   'm = 0 in nat -->
   lof{j. lof_vbind{| <J> >- lof_nil |}; 'm}
   <-->
   lof{j. lof_nil; 'm}

interactive_rw lof_vbind_cons {| reduce_lof |} :
   'm in nat -->
   lof{j. lof_vbind{| <J> >- lof_cons{i. 'f['i]; 'j<||>; 'e} |}; 'm}
   <-->
   lof{j. lof_cons{i. lof_vbind{| <J> >- 'f['i] |}; 'j; lof_vbind{| <J> >- 'e |}}; 'm}

interactive_rw lof_vbind_tl {| reduce_lof |} :
   lof{j. lof_vbind{| <J> >- lof_tl{i. 'f['i]; 'j<||>} |}; 'm}
   <-->
   lof{j. lof_tl{i. lof_vbind{| <J> >- 'f['i] |}; 'j}; 'm}

interactive_rw lof_vbind_nth_prefix {| reduce_lof |} :
   'r in nat -->
   lof{j. lof_vbind{| <J> >- lof_nth_prefix{i. 'f['i]; 'j<||>; 'p<||>; 'q<||>} |}; 'r}
   <-->
   lof{j. lof_nth_prefix{i. lof_vbind{| <J> >- 'f['i] |}; 'j; 'p; 'q}; 'r}

interactive_rw lof_vbind_nth_suffix {| reduce_lof |} :
   'r in nat -->
   lof{j. lof_vbind{| <J> >- lof_nth_suffix{i. 'f['i]; 'j<||>; 'p<||>; 'q<||>} |}; 'r}
   <-->
   lof{j. lof_nth_suffix{i. lof_vbind{| <J> >- 'f['i] |}; 'j; 'p; 'q}; 'r}

interactive_rw lof_vbind_append {| reduce_lof |} :
   'r in nat -->
   'p in nat -->
   lof{j. lof_vbind{| <J> >- lof_append{i. 'f['i]; k. 'g['k]; 'j<||>; 'p<||>; 'q<||>} |}; 'r}
   <-->
   lof{j. lof_append{i. lof_vbind{| <J> >- 'f['i] |}; k. lof_vbind{| <J> >- 'g['k] |}; 'j; 'p; 'q}; 'r}

(************************************************************************
 * Bind creation.
 *)
interactive_rw reduce_lof_vbind_nil {| reduce |} :
   lof_vbind{| >- 'e |}
   <-->
   'e

interactive_rw reduce_lof_vbind_left :
   lof_vbind{| x: 'A; <J['x]> >- 'e['x] |}
   <-->
   bind{x. lof_vbind{| <J['x]> >- 'e['x] |}}

interactive_rw vbind_to_lof_vbind {| pre_normalize_lof |} :
   vbind{| <J> >- 'e |}
   <-->
   lof_vbind{| <J> >- 'e |}

interactive_rw coalesce_lof_vbind {| reduce_lof |} :
   lof_vbind{| <J> >- lof_vbind{| <K> >- 'e |} |}
   <-->
   lof_vbind{| <J>; <K> >- 'e |}

interactive_rw coalesce_lof_vbind_bind1 {| reduce_lof |} : <:xrewrite<
   lof_vbind{| <J> >- lof_bind{1; x. e[x]} |}
   <-->
   lof_vbind{| <J>; x: it >- e[ [x] ] |}
>>

interactive_rw reduce_bind_mk_bterm_vlist :
   'n in nat -->
   'm in nat -->
   bind{x. mk_bterm{'n +@ length{vlist{| <J> |}}; 'op; lof{y. 'f['x; 'y]; 'm}}}
   <-->
   mk_bterm{'n +@ (length{vlist{| <J> |}} +@ 1); 'op; lof{y. bind{x. 'f['x; 'y]}; 'm}}

interactive_rw reduce_lof_vbind_mk_bterm {| reduce_lof |} :
   'n in nat -->
   'm in nat -->
   lof_vbind{| <J> >- mk_bterm{'n<||>; 'op<||>; lof{y. 'f['y]; 'm<||>}} |}
   <-->
   mk_bterm{'n +@ length{vlist{| <J> |}}; 'op; lof{y. lof_vbind{| <J> >- 'f['y] |}; 'm}}

(************************************************************************
 * Tactics.
 *)
let lofVBindElimC = unfold_lof_vbind

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
