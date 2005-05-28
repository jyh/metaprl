doc <:doc<
   @begin[doc]
   @module[Itt_hoas_destterm]
   The @tt[Itt_hoas_destterm] module defines destructors for extracting
   from a bterm the components corresponding to the de Bruijn-like representation
   of that bterm.
   @end[doc]

   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/index.html for information on Nuprl,
   OCaml, and more information about this system.

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

doc <:doc< @doc{@parents} >>

extends Itt_hoas_base
extends Itt_hoas_vector
extends Itt_hoas_operator
extends Itt_hoas_debruijn

doc docoff

open Basic_tactics

doc <:doc<
   @begin[doc]
   @terms
   The @hrefterm[is_var] operator decides whether a bterm is a @hrefterm[var] or a
   @hrefterm[mk_bterm]. In order to implement the @refterm[is_var] operator we
   assume that there exist at least two distinct operators (for any concrete
   notion of operators this would, of course, be trivially derivable but we would
   like to keep the operators type abstract at this point).

   The @hrefterm[dest_bterm] operator is a generic destructor that can extract all the
   components of the de Bruijn-like representation of a bterm.
   @end[doc]
>>
declare op1
declare op2

define (*private*) unfold_isvar:
   is_var{'bt} <--> bnot{is_same_op{get_op{'bt; op1}; get_op{'bt; op2}}}

define (*private*) unfold_dest_bterm:
   dest_bterm{'bt; l,r.'var_case['l; 'r]; bdepth,op,subterms. 'op_case['bdepth; 'op; 'subterms] }
   <--> if is_var{'bt}
           then 'var_case[left{'bt}; right{'bt}]
           else 'op_case[bdepth{'bt}; get_op{'bt; it}; subterms{'bt}]

doc <:doc< @doc{@rules} >>

prim op1_op {| intro [] |}:
   sequent { <H> >- op1 in Operator }
   = it

prim op2_op {| intro [] |}:
   sequent { <H> >- op2 in Operator }
   = it

doc <:doc< @doc{@rewrites} >>

prim_rw ops_distict {| reduce |}:
   is_same_op{op1; op2} <--> bfalse

interactive_rw same_op_id {| reduce |} :
   'op in Operator -->
   is_same_op{'op; 'op} <--> btrue

interactive_rw is_var_var {| reduce |} :
   'm in nat -->
   'n in nat -->
   is_var{var{'m; 'n}} <--> btrue

interactive_rw is_var_mk_bterm {| reduce |} :
   'op in Operator -->
   'n in nat -->
   is_var{mk_bterm{'n; 'op; 'btl}} <--> bfalse

interactive_rw dest_bterm_var {| reduce |} :
   'l in nat -->
   'r in nat -->
   dest_bterm{var{'l; 'r}; l,r.'var_case['l; 'r]; d,o,s. 'op_case['d; 'o; 's] } <--> 'var_case['l; 'r]

interactive_rw dest_bterm_mk_bterm {| reduce |} :
   'n in nat -->
   'op in Operator -->
   'subterms in list -->
   dest_bterm{mk_bterm{'n; 'op; 'subterms}; l,r.'var_case['l; 'r]; bdepth,op,subterms. 'op_case['bdepth; 'op; 'subterms] }
   <-->
   'op_case['n; 'op; map{bt. bind{'n; v. substl{'bt; 'v}}; 'subterms}]

doc docoff

dform is_var_df : is_var{'bt} =
   pushm[3] tt["is_var"] `"(" slot{'bt} `")" popm

dform dest_bterm_df : dest_bterm{'bt; l,r.'var_case; d,o,sb. 'op_case } =
   pushm[0] szone szone pushm[3] keyword["match"] hspace slot{'bt} popm hspace ezone pushm[1] pushm[3]
   keyword["with"] hspace pushm[3] var{'l; 'r} `" -> " slot{'var_case} popm popm hspace
   `"| " pushm[3] mk_bterm{'d; 'o; 'sb} `" -> " slot{'op_case} popm popm ezone popm

