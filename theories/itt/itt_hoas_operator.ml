doc <:doc<
   @module[Itt_hoas_operator]
   The @tt[Itt_hoas_operator] module defines a type << Operator >> of abstract
   operators; it also estabishes the connection between abstract operator type
   and the internal notion of syntax that is exposed by the computational bterms
   theory (@hrefmodule[Base_operator]).

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

   Authors: Aleksey Nogin @email{nogin@cs.caltech.edu}
            Alexei Kopylov @email{kopylov@cs.caltech.edu}
            Xin Yu @email{xiny@cs.caltech.edu}

   @end[license]
>>

doc <:doc< @parents >>
extends Itt_theory
extends Base_operator
extends Itt_nat
extends Itt_list2
doc docoff
extends Itt_int_base
extends Itt_nequal

open Base_operator
open Basic_tactics
open Itt_struct

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

doc <:doc<
   @terms

   The @tt{Operator} type is an abstract type with a decidable equality.
   We only require that an operator have a fixed shape.

   As in the case of concrete quoted operators, the shape of
   an abstract operator is a list of numbers, each stating the number of
   bindings the operator adds to the corresponding subterm; the length of
   this list is the arity of an operator.

>>

declare Operator
declare shape{'op}
declare is_same_op{'op_1;'op_2}

doc docoff

dform shape_df: shape{'op} = `"shape(" slot{'op} `")"
dform issameop_df : is_same_op{'op1;'op2} =
   `"is_same_op(" slot{'op1} `"; " slot{'op2} `")"
dform arity_df: arity{'op} = `"arity(" slot{'op} `")"

doc <:doc<
   @rules

   <<Operator>> is an abstract type.
>>

prim op_univ {| intro [] |}:
   sequent { <H> >- Operator in univ[l:l] } = it

interactive op_type {| intro [] |}:
   sequent { <H> >- Operator Type }

doc <:doc<
   Equal operators must be identical.
>>
prim op_sqeq {| nth_hyp |} :
   sequent { <H> >- 'op1 = 'op2 in Operator } -->
   sequent { <H> >- 'op1 ~ 'op2 }
   = it

doc <:doc<
   @tt[is_same_op] decides the equality of << Operator >>.
>>

prim is_same_op_wf {| intro [] |} :
   sequent { <H> >- 'op_1 in Operator } -->
   sequent { <H> >- 'op_2 in Operator } -->
   sequent { <H> >- is_same_op{'op_1;'op_2} in bool }
   = it

prim is_same_op_eq {| intro [AutoMustComplete] |} :
   sequent { <H> >- 'op_1 = 'op_2 in Operator } -->
   sequent { <H> >- "assert"{is_same_op{'op_1;'op_2}} }
   = it

prim is_same_op_rev_eq :
   [wf] sequent { <H> >- 'op_1 in Operator } -->
   [wf] sequent { <H> >- 'op_2 in Operator } -->
   sequent { <H> >- "assert"{is_same_op{'op_1;'op_2}} } -->
   sequent { <H> >- 'op_1 = 'op_2 in Operator }
   = it

interactive op_decidable {| intro [] |} :
   sequent { <H> >- 'op_1 in Operator } -->
   sequent { <H> >- 'op_2 in Operator } -->
   sequent { <H> >- decidable{'op_1 = 'op_2 in Operator} }

interactive is_same_op_elim {| elim [ThinOption thinT] |} 'H :
   [wf] sequent { <H>; x: "assert"{is_same_op{'op_1;'op_2}}; <J['x]> >- 'op_1 in Operator } -->
   [wf] sequent { <H>; x: "assert"{is_same_op{'op_1;'op_2}}; <J['x]> >- 'op_2 in Operator } -->
   [main] sequent { <H>; x: "assert"{is_same_op{'op_1;'op_2}}; 'op_1 = 'op_2 in Operator; <J['x]> >- 'C['x] } -->
   sequent { <H>; x: "assert"{is_same_op{'op_1;'op_2}}; <J['x]> >- 'C['x] }

doc <:doc<
   Each operator has a @tt[shape] --- a list of natural numbers that are meant
   to represent the number of bindings in each of the arguments. The length of
   of the list is the operator's arity.
>>

define iform unfold_arity : arity{'op} <--> length{shape{'op}}

prim shape_nat_list {| intro [] |} :
   sequent { <H> >- 'op in Operator } -->
   sequent { <H> >- shape{'op} in list{nat} }
   = it

interactive shape_list {| intro [] |} :
   sequent { <H> >- 'op in Operator } -->
   sequent { <H> >- shape{'op} in list }

interactive shape_nat_list_eq {| intro [] |} :
   sequent { <H> >- 'op1 = 'op2 in Operator } -->
   sequent { <H> >- shape{'op1} = shape{'op2} in list{nat} }

interactive shape_int_list {| intro [] |} :
   sequent { <H> >- 'op1 = 'op2 in Operator } -->
   sequent { <H> >- shape{'op1} = shape{'op2} in list{int} }

interactive arity_nat {| intro [] |} :
   sequent { <H> >- 'op1 = 'op2 in Operator } -->
   sequent { <H> >- arity{'op1} = arity{'op2} in nat }

interactive arity_int {| intro [] |} :
   sequent { <H> >- 'op1 = 'op2 in Operator } -->
   sequent { <H> >- arity{'op1} = arity{'op2} in int }

interactive shape_int_list_sq {| intro [] |} :
   sequent { <H> >- 'op1 = 'op2 in Operator } -->
   sequent { <H> >- shape{'op1} ~ shape{'op2} }

doc <:doc<
   @modsection{Concrete Operators}

   This section establishes the connection between the abstract notion
   of operator and the internal notion of opertor that is exposed by
   the computational bterms theory (@hrefmodule[Base_operator]).

   Essentially, it @emph{postulates} that the abstract operator is
   compatible with the notion of operators that we have defined
   computationally, that the computationally-defined operations on
   operators act as expected, and that the syntactic operations we
   defined (such as shape) correspond exactly to the built-in
   operations of the meta-theory. In a way, this theory establishes
   the operator expressions as denotations for constants of the
   << Operator >> type --- this is similar to how numerals denote
   constants of type <<int>>.

   First, we define a concrete representation for operators. We will represent
   an operator by a bterm of the form <<operator[op:op]>>
>>
doc docoff
(************************************************************************
 * Xlist                                                                *
 ************************************************************************)

(* XXX: This part should be in a separate theory *)

declare rlist_of_list{'l}

prim_rw rlist_list_cons {| reduce |} :
   rlist_of_list{ 'hd :: 'tl } <--> rcons{'hd; rlist_of_list{'tl}}

prim_rw rlist_list_nil {| reduce |} :
   rlist_of_list{ nil } <--> rnil

declare list_of_rlist{'l}

prim_rw reduce_rlist_cons {| reduce |} :
   list_of_rlist{rcons{'hd; 'tl}} <--> ('hd :: list_of_rlist{'tl})

prim_rw reduce_rlist_nil {| reduce |} :
   list_of_rlist{rnil} <--> nil

let rec reduce_rlist t =
   if is_rnil_term (one_subterm t) then
      reduce_rlist_nil
   else
      reduce_rlist_cons thenC addrC [Subterm 2] (termC reduce_rlist)

dform list_of_rlist_df : except_mode[src] :: list_of_rlist{'l} =
   `"list_of_rlist(" slot{'l} `")"

(* ********************************************************************* *)

doc docon

declare operator[op:op]

prim op_constant {| intro [] |} :
   sequent { <H> >- operator[op:op] in Operator }
   = it

prim_rw bterm_shape {| reduce |} :
   shape{operator[op:op]} <-->  list_of_rlist{Base_operator!shape[op:op]}

prim_rw bterm_same_op {| reduce |} :
   is_same_op{operator[op1:op]; operator[op2:op]} <--> meta_eq[op1:op, op2:op]{btrue;bfalse}

doc docoff

(* ********** Examples ************* *)
interactive op_exam1 {| intro[] |}:
   sequent{ <H> >- operator[(apply{'x;'y}):op] in Operator }

interactive op_exam2 {| intro[] |}:
   sequent{ <H> >- lambda[@]{x.it[@]} in Operator }

interactive op_exam3 {| intro[] |}:
   sequent{ <H> >- apply[@]{'x; union[@]{'y; 'z}} = apply[@]{it[@]; int[@]} in Operator }

interactive op_exam4 {| intro[] |}:
   sequent{ <H> >- lambda[@]{x.it[@]} = lambda[@]{x.'P['x]} in Operator }

interactive diffops {| intro[] |}:
   sequent{ <H> >- apply[@]{it[@]; it[@]} <> lambda[@]{x.it[@]} in Operator }

interactive shape_exam1 {| intro[] |}:
   sequent{ <H> >- shape{apply[@]{'x; union[@]{'y; 'z}}} = 0::0::nil in list{int} }

interactive shape_exam2 {| intro[] |}:
   sequent{ <H> >- shape{lambda[@]{x.it[@]}} = 1::nil in list{int} }
