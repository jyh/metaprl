doc <:doc<
   @begin[doc]
   @module[Itt_synt_operator]

   @end[doc]

   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/index.html for information on Nbindrl,
   OCaml, and more information about this system.

   Copyright (C) 2005, MetaPRL Grobind

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

   Authors: Aleksey Nogin @email{nogin@cs.caltech.edu}
            Alexei Kopylov @email{kopylov@cs.caltech.edu}
            Xin Yu @email{xiny@cs.caltech.edu}

   @end[license]
>>

doc "doc"{parents}

extends Itt_quotient
extends Itt_int_base
extends Itt_nat

open Basic_tactics

doc "doc"{terms}

declare BOperator
declare op_bdepth{'op}
declare arity{'op}
declare is_same_op{'op_1;'op_2} (* Do not consider  op_bdepth *)
declare inject{'op; 'n} (* Op * Nat -> BOp *)

define unfold_unbind :
   unbind{'op} <--> inject{'op; op_bdepth{'op} -@ 1 }

define unfold_bind :
   bind{'op; 'n} <--> inject{'op; op_bdepth{'op} +@ 'n }

define unfold_op :
   Operator <--> quot o1, o2 : BOperator // "assert"{is_same_op{'o1; 'o2}}

doc "doc"{rewrites}

prim_rw op_bdepth_inject_id {| reduce |} :
   'op in Operator -->
   'n in nat -->
   op_bdepth{inject{'op; 'n}} <--> 'n

doc "doc"{rules}

prim bop_univ {| intro [] |}:
   sequent { <H> >- BOperator in univ[l:l] } = it

interactive bop_type {| intro [] |}:
   sequent { <H> >- BOperator Type }

prim is_same_op_wf {| intro [] |} :
   sequent { <H> >- 'op_1 in BOperator } -->
   sequent { <H> >- 'op_2 in BOperator } -->
   sequent { <H> >- is_same_op{'op_1;'op_2} in bool }
   = it

prim is_same_op_ref {| intro [] |} :
   [wf] sequent { <H> >- 'op in BOperator } -->
   sequent { <H> >- "assert"{is_same_op{'op;'op}} }
   = it

prim is_same_op_sym :
   [wf] sequent { <H> >- 'op1 in BOperator } -->
   [wf] sequent { <H> >- 'op2 in BOperator } -->
   sequent { <H> >- "assert"{is_same_op{'op1;'op2}} } -->
   sequent { <H> >- "assert"{is_same_op{'op2;'op1}} } = it

prim is_same_op_trans 'op2 :
   [wf] sequent { <H> >- 'op1 in BOperator } -->
   [wf] sequent { <H> >- 'op2 in BOperator } -->
   [wf] sequent { <H> >- 'op3 in BOperator } -->
   sequent { <H> >- "assert"{is_same_op{'op1;'op2}} } -->
   sequent { <H> >- "assert"{is_same_op{'op2;'op3}} } -->
   sequent { <H> >- "assert"{is_same_op{'op1;'op3}} } = it

interactive op_univ {| intro [] |}:
   sequent { <H> >- Operator in univ[l:l] }

interactive op_type {| intro [] |}:
   sequent { <H> >- Operator Type }

interactive bop_subtype_op {| intro [AutoMustComplete] |}:
   sequent { <H> >- 'op in BOperator } -->
   sequent { <H> >- 'op in Operator }

interactive bop_subtype_op2 {| nth_hyp |} 'H :
   sequent { <H>; op: BOperator; <J['op]> >- 'op in Operator }

prim op_bdepth_wf {| intro [] |} :
   sequent { <H> >- 'op in BOperator } -->
   sequent { <H> >- op_bdepth{'op} in nat }
   = it

prim arity_wf {| intro [] |} :
   sequent { <H> >- 'op in Operator } -->
   sequent { <H> >- arity{'op} in list{nat} }
   = it

prim inject_wf {| intro [] |} :
   sequent { <H> >- 'op in Operator } -->
   sequent { <H> >- 'n in nat } -->
   sequent { <H> >- inject{'op; 'n} in BOperator }
   = it

prim inject_id {| intro [] |} :
   [wf] sequent { <H> >- 'op in BOperator } -->
   sequent { <H> >- inject{'op; op_bdepth{'op}} = 'op in BOperator }
   = it

interactive bind_wf {| intro [] |} :
   sequent { <H> >- 'op in BOperator } -->
   sequent { <H> >- 'n in nat } -->
   sequent { <H> >- bind{'op; 'n} in  BOperator }

interactive_rw bind_red {| reduce |} :
   'op in BOperator -->
   'n in nat ->
   op_bdepth{bind{'op; 'n}} <--> op_bdepth{'op} +@ 'n

interactive unbind_wf {| intro [] |} :
   sequent { <H> >- 'op in BOperator } -->
   sequent { <H> >- op_bdepth{'op} > 0 } -->
   sequent { <H> >- unbind{'op} in  BOperator }

interactive_rw unbind_red {| reduce |} :
   'op in BOperator -->
   op_bdepth{'op} > 0 -->
   op_bdepth{unbind{'op}} <--> op_bdepth{'op} -@ 1



doc <:doc< @docoff >>
