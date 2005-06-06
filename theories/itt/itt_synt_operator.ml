doc <:doc<
   @begin[doc]
   @module[Itt_synt_operator]
   The @tt[Itt_synt_operator] module defines a type of operators << BOperator >>
   for our simple theory of syntax.
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
extends Itt_list2
doc docoff

open Basic_tactics

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

doc <:doc<
   @begin[doc]
   @terms

   The @tt{BOperator} type is an abstract type with a decidable equality.
   We only require that an operator have a fixed binding depth (a number)
   and a shape.

   As in the case of concrete quoted operators, the shape of
   an abstract operator is a list of numbers, each stating the number of
   bindings the operator adds to the corresponding subterm; the length of
   this list is the arity of an operator.

   The @tt{Operator} type imposes a @emph{new} equality
   << is_same_op{'op1; 'op2} >> on type <<BOperator>>, in which two
   operators are considered equal iff they are of the same shape (which
   means their binding depths can be different.)

   The << inject{'op;'n} >> operator gives the operator << 'op >> a ``new''
   binding depth << 'n >>.

   @end[doc]
>>

declare BOperator
declare op_bdepth{'op}
declare shape{'op}
declare is_same_op{'op_1;'op_2} (* Do not consider op_bdepth *)
declare inject{'op; 'n} (* Op * Nat -> BOp *)

define unfold_unbind :
   unbind{'op} <--> inject{'op; op_bdepth{'op} -@ 1 }
define unfold_bind :
   bind{'op; 'n} <--> inject{'op; op_bdepth{'op} +@ 'n }
define unfold_bind1 :
   bind{'op} <--> inject{'op; op_bdepth{'op} +@ 1 }

define unfold_op :
   Operator <--> quot o1, o2 : BOperator // "assert"{is_same_op{'o1; 'o2}}
doc docoff

let fold_op = makeFoldC << Operator >> unfold_op

dform op_bdepth_df: op_bdepth{'op} = `"bdepth" sub["o"] "(" slot{'op} ")"
dform shape_df: shape{'op} = `"shape(" slot{'op} `")"
dform issameop_df : is_same_op{'op1;'op2} =
   `"is_same_op(" slot{'op1} `"; " slot{'op2} `")"
dform inject_df : inject{'op;'n} =
   `"inject(" slot{'op} `"; " slot{'n} `")"
dform unbind_df: unbind{'op} = `"unbind(" slot{'op} `")"
dform bind_df : bind{'op;'n} =
   `"bind(" slot{'op} `"; " slot{'n} `")"
dform bind_df1: bind{'op} = `"bind(" slot{'op} `")"
dform arity_df: arity{'op} = `"arity(" slot{'op} `")"

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

doc <:doc< @begin[doc]
   @tt[is_same_op] is an equivalence relation on << BOperator >>.
@end[doc] >>
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

doc <:doc< @begin[doc]
   << BOperator >> is a subtype of << Operator >>.
@end[doc] >>
interactive op_univ {| intro [] |}:
   sequent { <H> >- Operator in univ[l:l] }

interactive op_type {| intro [] |}:
   sequent { <H> >- Operator Type }

interactive bop_subtype_op {| intro [AutoMustComplete] |}:
   sequent { <H> >- 'op in BOperator } -->
   sequent { <H> >- 'op in Operator }

interactive bop_subtype_op2 {| nth_hyp |} 'H :
   sequent { <H>; op: BOperator; <J['op]> >- 'op in Operator }

doc <:doc< @begin[doc]
   Some well-formedness rules.
@end[doc] >>
prim op_bdepth_wf {| intro [] |} :
   sequent { <H> >- 'op in BOperator } -->
   sequent { <H> >- op_bdepth{'op} in nat }
   = it

interactive op_bdepth_wf2 {| intro [] |} :
   sequent { <H> >- 'op in BOperator } -->
   sequent { <H> >- op_bdepth{'op} in int }

prim shape_wf {| intro [] |} :
   sequent { <H> >- 'op in Operator } -->
   sequent { <H> >- shape{'op} in list{nat} }
   = it

prim inject_wf {| intro [] |} :
   sequent { <H> >- 'op in Operator } -->
   sequent { <H> >- 'n in nat } -->
   sequent { <H> >- inject{'op; 'n} in BOperator }
   = it

interactive bind_wf {| intro [] |} :
   sequent { <H> >- 'op in BOperator } -->
   sequent { <H> >- 'n in nat } -->
   sequent { <H> >- bind{'op; 'n} in  BOperator }

interactive bind1_wf {| intro [] |} :
   sequent { <H> >- 'op in BOperator } -->
   sequent { <H> >- bind{'op} in  BOperator }

interactive is_same_op_wf2 {| intro [] |} :
   sequent { <H> >- 'op_1 in Operator } -->
   sequent { <H> >- 'op_2 in Operator } -->
   sequent { <H> >- is_same_op{'op_1;'op_2} in bool }



doc <:doc< @begin[doc]
   Properties of the operators.
@end[doc] >>
prim inject_id {| intro [] |} :
   [wf] sequent { <H> >- 'op in BOperator } -->
   sequent { <H> >- inject{'op; op_bdepth{'op}} = 'op in BOperator }
   = it

prim inject_sameop {| intro [] |} :
   [wf] sequent { <H> >- 'op in Operator } -->
   [wf] sequent { <H> >- 'n in nat } -->
   sequent { <H> >- "assert"{is_same_op{inject{'op;'n}; 'op}} }
   = it

interactive is_same_op_ref1 {| intro [] |} :
   [wf] sequent { <H> >- 'op in Operator } -->
   sequent { <H> >- "assert"{is_same_op{'op;'op}} }

interactive is_same_op_sym1 :
   [wf] sequent { <H> >- 'op1 in Operator } -->
   [wf] sequent { <H> >- 'op2 in Operator } -->
   sequent { <H> >- "assert"{is_same_op{'op1;'op2}} } -->
   sequent { <H> >- "assert"{is_same_op{'op2;'op1}} }

interactive is_same_op_trans1 'op2 :
   [wf] sequent { <H> >- 'op1 in Operator } -->
   [wf] sequent { <H> >- 'op2 in Operator } -->
   [wf] sequent { <H> >- 'op3 in Operator } -->
   sequent { <H> >- "assert"{is_same_op{'op1;'op2}} } -->
   sequent { <H> >- "assert"{is_same_op{'op2;'op3}} } -->
   sequent { <H> >- "assert"{is_same_op{'op1;'op3}} }

interactive inject_equal {| intro [] |} :
   [wf] sequent { <H> >- 'op in Operator } -->
   [wf] sequent { <H> >- 'n in nat } -->
   sequent { <H> >- inject{'op;'n} = 'op in Operator }

interactive bind_equal {| intro [] |} :
   [wf] sequent { <H> >- 'op in BOperator } -->
   [wf] sequent { <H> >- 'n in nat } -->
   sequent { <H> >- bind{'op;'n} = 'op in Operator }

interactive bind1_equal {| intro [] |} :
   [wf] sequent { <H> >- 'op in BOperator } -->
   sequent { <H> >- bind{'op} = 'op in Operator }

interactive_rw bind_red {| reduce |} :
   'op in BOperator -->
   'n in nat -->
   op_bdepth{bind{'op; 'n}} <--> op_bdepth{'op} +@ 'n

interactive_rw bind1_red {| reduce |} :
   'op in BOperator -->
   op_bdepth{bind{'op}} <--> op_bdepth{'op} +@ 1

interactive unbind_wf {| intro [] |} :
   sequent { <H> >- 'op in BOperator } -->
   sequent { <H> >- op_bdepth{'op} > 0 } -->
   sequent { <H> >- unbind{'op} in  BOperator }

interactive_rw unbind_red {| reduce |} :
   'op in BOperator -->
   op_bdepth{'op} > 0 -->
   op_bdepth{unbind{'op}} <--> op_bdepth{'op} -@ 1
doc docoff

interactive inject_wf2 {| intro [] |} :
   sequent { <H> >- 'op1 = 'op2 in Operator } -->
   sequent { <H> >- 'n in nat } -->
   sequent { <H> >- inject{'op1; 'n} = inject{'op2; 'n} in BOperator }

interactive shape_int_list {| intro [] |} :
   sequent { <H> >- 'op in Operator } -->
   sequent { <H> >- shape{'op} in list{int} }

interactive shape_list {| intro [] |} :
   sequent { <H> >- 'op in Operator } -->
   sequent { <H> >- shape{'op} in list }

interactive shape_nat_list {| intro [] |} :
   sequent { <H> >- 'op1 = 'op2 in Operator } -->
   sequent { <H> >- shape{'op1} = shape{'op2} in list{nat} }

interactive shape_int_list1 {| intro [] |} :
   sequent { <H> >- 'op1 = 'op2 in Operator } -->
   sequent { <H> >- shape{'op1} = shape{'op2} in list{int} }

interactive shape_int_list2 {| intro [] |} :
   sequent { <H> >- 'op1 = 'op2 in Operator } -->
   sequent { <H> >- shape{'op1} ~ shape{'op2} }



doc <:doc< @begin[doc]
@end[doc] >>
interactive_rw shape_inject {| reduce |} :
   'op in Operator -->
   'n in nat -->
   shape{inject{'op; 'n}} <--> shape{'op}

interactive_rw shape_bind {| reduce |} :
   'op in BOperator -->
   'n in nat -->
   shape{bind{'op; 'n}} <--> shape{'op}

interactive_rw shape_bind1 {| reduce |} :
   'op in BOperator -->
   shape{bind{'op}} <--> shape{'op}
doc docoff
