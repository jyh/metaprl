doc <:doc<
   @begin[doc]
   @module[Itt_reflection_new]

   The @tt[Itt_reflection_new] module defines the @emph{reflection theory
   for syntax}. It establishes the connection between the abstract notion
   of syntax formalized in the simple theory of syntax
   (@hrefmodule[Itt_synt_var], @hrefmodule[Itt_synt_operator],
   @hrefmodule[Itt_synt_bterm], @hrefmodule[Itt_synt_subst]) and the
   internal notion of syntax that is exposed by the computational
   bterms theory (@hrefmodule[Base_reflection]).

   Essentially, the reflection theory @emph{postulates} that the simple
   theory of syntax is compatible with the notion of bterms that we have
   defined computationally, that the computationally-defined operations
   on bterms act as expected, and that the syntactic operations we defined
   (such as substitution) correspond exactly to the built-in operations of
   the meta-theory. In a way, this theory establishes the bterm expressions
   as denotions for constants of the << BTerm >> type --- this is similar
   to how numerals denote constants of type <<int>>.

   @end[doc]

   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/index.html for information on Nuprl,
   OCaml, and more information about this system.

   Copyright (C) 2004 MetaPRL Group

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

doc <:doc<
   @begin[doc]
   @parents
   @end[doc]
>>
extends Itt_theory
extends Base_reflection
extends Itt_nat
extends Itt_synt_bterm
extends Itt_synt_subst
doc docoff


open Dtactic

open Base_reflection
open Basic_tactics
open Itt_nat
open Itt_equal
open Itt_struct
open Itt_squash


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


(************************************************************************
 * Operator                                                             *
 ************************************************************************)

doc <:doc< @begin[doc]
   @modsection{Operators}

   First, we define a concrete representation for operators. We will represent
   an operator by a bterm of the form
   $bterm@{<<Gamma>>.op[quote]@{<<Delta>>_{1}.t_{1},@ldots,<<Delta>>_{n}.t_{n}@}@}$,
   in which the length of <<Gamma>> is the binding depth of the operator, and
   $<<Delta>>_{i}$'s are the binding variables of $t_{i}$. The operator is
   solely defined by its binding depth, name and shape. We define the shape
   of an operator, equality of two operators and binding depth using operations
   from @hrefmodule[Itt_synt_operator] and @hrefmodule[Itt_synt_bterm].
@end[doc] >>

declare bterm{x.'bt['x]}
prim_rw bterm_reduce: bterm{x.bterm{| <K> >- 't['x] |}} <-->  bterm{| x:term; <K> >- 't['x] |}


prim bterm_op {| intro[AutoMustComplete] |} :
  sequent { <H> >- if_quoted_op{'op<||>;"true"} } -->
  sequent { <H> >- 'op<||> in BOperator }
  = it

let resource intro +=
 (<<bterm{| <J> >- 'op<||> |} in BOperator>>,wrap_intro (bterm_op thenT rw reduce_if_quoted_op 0 thenT trivialT) )

prim_rw bterm_op_bdepth1 {| reduce |} : op_bdepth{ bterm{| >- 'op |}} <--> 0
prim_rw bterm_op_bdepth2 {| reduce |} : op_bdepth{ bterm{| x:term; <H> >- 'op |}} <--> op_bdepth{ bterm{| <H> >- 'op |} } +@ 1

prim_rw bterm_shape :
    if_quoted_op{'op<||>;"true"} -->
    shape{'op} <-->  map{lambda{x.op_bdepth{'x}}; list_of_rlist{Base_reflection!subterms{'op}} }

let resource reduce += (<<shape{bterm{| <K> >- 't |}}>>,bterm_shape)

prim_rw bterm_same_op:
       is_same_op{'op1;'op2} <--> Base_reflection!if_same_op{'op1;'op2;btrue;bfalse}

prim_rw bterm_inject: inject{bterm{| <K> >- 'op<||> |}; 'n} <--> ind{'n; bterm{| >- 'op<||> |}; k,l.bterm{x.'l}}

(************************************************************************
 * Var                                                                  *
 ************************************************************************)

doc <:doc< @begin[doc]
   @modsection{BTerms}

   Second, we define the evaluation rules for bterms that map expressions
   $bterm@{@ldots@}$ to elements of the type <<BTerm>> defined in
   @hrefmodule[Itt_synt_bterm].

   @modsubsection{Var}

   In the case of a variable, $bterm@{<<Gamma>>,x,<<Delta>>.x@}$ evaluates
   to <<var{length{Gamma}; length{Delta}}>>.
@end[doc] >>

prim_rw bterm_var_1 :
  bterm{| x : term >- 'x |} <--> var{0;0}

prim bterm_var_right :
  sequent{ <H> >- bterm{| <K> >- 'x |} ~ var{'l;'r} } -->
  sequent{ <H> >- bterm{| <K>; y:term >- 'x |} ~ var{'l;'r +@ 1} }
  = it

prim bterm_var_left :
  sequent{ <H> >- bterm{| <K> >- 'x |} ~ var{'l;'r} } -->
  sequent{ <H> >- bterm{| y:term; <K> >- 'x |} ~ var{'l +@ 1;'r} }
  = it

(************************************************************************
 * Make_bterm                                                           *
 ************************************************************************)

doc <:doc< @begin[doc]
   @modsubsection{Make_bterm}

   If << 'bt >> is a compound bterm, then << 'bt >> evaluates to
   << make_bterm{'bt; subterms{'bt}} >>.
@end[doc] >>

prim_rw make_bterm_eval:
 if_quoted_op{ bterm{| <J> >- 'T |} ;"true"} -->
 bterm{| <J> >- 'T |} <-->
 make_bterm{bterm{| <J> >- 'T |};list_of_rlist{Base_reflection!subterms{bterm{| <J> >- 'T |}}}}

(************************************************************************
 * Reflection rule for substitution                                     *
 ************************************************************************)

doc <:doc< @begin[doc]
   @modsection{Substitution}
   This reflection rule for the substitution operator states that the
   substitution we have defined syntactically agrees with  the second
   order substitution that we have internally in the system.
@end[doc] >>

prim_rw reflection_subst 'H :
 (if_bterm{bterm{| <H>;x:term;<J> >- 't['x] |};"true"} ) -->
 (if_bterm{bterm{| <H>;x:term;<J> >- 's['x] |};"true"} ) -->
 subst{bterm{| <H>;x:term;<J> >- 't['x] |};
       bterm{| <H>;x:term;<J> >- 'x |};
       bterm{| <H>;x:term;<J> >- 's['x] |}} <-->
 bterm{| <H>;x:term;<J> >- 't['s['x]] |}
doc docoff
