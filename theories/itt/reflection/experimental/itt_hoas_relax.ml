doc <:doc<
   @module[Itt_hoas_relax]

   The @tt[Itt_hoas_relax] module defines some transformations
   with relaxed wf subgoals.

   The goal here is to define a type << Bind >> that includes
   all the terms in Itt_hoas_base.  It will follow trivially
   that << BTerm subtype Bind >>.  It will also follow that
   any term of the form << bind{'n; x. inr{math_ldots}} >>
   will be in the << Bind >> type.

   We can then show the eta-rules for << Bind >> terms, and
   then a corresponding rule for
   << dest_bterm{'e; l, r. 'base['l; 'r]; d, o, s. 'step['d; 'o; 's]} >>
   that uses relaxed terms.

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
extends Itt_hoas_bterm
extends Itt_match

doc docoff

open Basic_tactics

(************************************************************************
 * General Bind type.
 *)
doc <:doc<
   Define a type << Bind >> that includes all values from Itt_hoas_base.
>>
define const unfold_BindInfo : BindInfo <--> <:xterm<
   Prod n: nat * ({ l : list{top} | length{l} = n in nat } -> top)
>>

define unfold_bind_of_info : bind_of_info{'x} <--> <:xterm<
   let n, f = x in
       bind{n; y. mk_terms{f y}}
>>

define const unfold_Bind : Bind <--> <:xterm<
   Img{BindInfo; x. bind_of_info{x}}
>>

(************************************************************************
 * Depth lemmas.
 *)
doc <:doc<
   The << bdepth{'e} >> is fairly forgiving on the terms that it takes.
   Here are some relaxed lemmas.
>>
define unfold_mk_it_vec : mk_it_vec{'n} <--> <:xterm<
   ind{n; []; i, g. it :: g}
>>

interactive_rw reduce_mk_it_vec_zero {| reduce |} : <:xrewrite<
   mk_it_vec{0}
   <-->
   []
>>

interactive_rw reduce_mk_it_vec_succ {| reduce |} : <:xrewrite<
   'n in nat -->
   mk_it_vec{'n +@ 1}
   <-->
   it :: mk_it_vec{'n}
>>

interactive_rw reduce_bdepth_mk_terms {| reduce |} : <:xrewrite<
   bdepth{mk_terms{'e}}
   <-->
   0
>>

(************************************************************************
 * Depth-binding.
 *)
doc <:doc<
   The << Bind{'n} >> type includes any term that has exactly binding
   depth << 'n >>.
>>
define unfold_Bindn : Bind{'n} <--> <:xterm<
   { e: Bind | bdepth{e} = 'n in nat }
>>

(************************************************************************
 * Well-formedness.
 *)
doc <:doc<
   Well-formedness of the << Bind >> type.
>>
interactive bind_info_wf {| intro [] |} : <:xrule<
   <H> >- BindInfo Type
>>

interactive bind_wf {| intro [] |} : <:xrule<
   <H> >- Bind Type
>>

doc <:doc<
   Well-formedness of the bounded << Bind{'n} >> type.
>>
interactive_rw bind_of_info_pair {| reduce |} : <:xrewrite<
   bind_of_info{(n, f)}
   <-->
   bind{n; x. mk_terms{f x}}
>>

interactive bindn_in_bind_type {| intro [] |} : <:xrule<
   "wf" : <H> >- n in nat -->
   <H> >- bind{'n; x. mk_terms{'f['x]}} in Bind
>>

interactive bdepth_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- e in Bind -->
   <H> >- bdepth{e} in nat
>>

interactive bdepth_int_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- e in Bind -->
   <H> >- bdepth{e} in int
>>

interactive bindn_wf {| intro [] |} : <:xrule<
   "wf" : <H> >- n in nat -->
   <H> >- Bind{n} Type
>>

(************************************************************************
 * Relaxed rewrites.
 *)
interactive_rw reduce_bdepth_bindn_mk_terms {| reduce |} : <:xrewrite<
   n in nat -->
   bdepth{bind{n; x. mk_terms{e[x]}}}
   <-->
   n
>>

interactive_rw bind_eta_relax {| reduce |} : <:xrewrite<
   t in Bind -->
   bdepth{t} > 0 -->
   bind{x. subst{t; x}}
   <-->
   t
>>

interactive_rw bindn_eta_relax {| reduce |} : <:xrewrite<
   n in nat -->
   t in Bind -->
   bdepth{t} >= n -->
   bind{n; x. substl{t; x}}
   <-->
   t
>>

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
