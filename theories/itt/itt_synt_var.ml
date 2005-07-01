doc <:doc<
   @begin[doc]
   @module[Itt_synt_var]
    Our simple theory of syntax has three core parts.
    The first part @hrefmodule[Itt_synt_var] defines a type of variables <<Var>> in a de Bruijn-like style @cite[deb72].
    The second part @hrefmodule[Itt_synt_operators] defines a type of operators @tt[BOperator].
    The third part @hrefmodule[Itt_synt_bterm] defines a type of terms @tt[BTerm].
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

   Authors: Aleksey Nogin @email{nogin@cs.caltech.edu}
            Alexei Kopylov @email{kopylov@cs.caltech.edu}
            Xin Yu @email{xiny@cs.caltech.edu}

   @end[license]
>>

doc "doc"{parents}
extends Itt_int_base
extends Itt_nat
extends Itt_omega
doc docoff

open Basic_tactics

doc <:doc< @begin[doc]
   @modsection{Abstract type}
   <<Var>> consists of terms of the form <<var{'i;'j}>>, where <<'i>> and <<'j>>
   are arbitrary natural numbers, and <<var{it;it}>> is a new constructor.
   The expression <<var{'i;'j}>> is meant to represent the bterm
   $bterm(@Gamma; x; @Delta. x)$ where $|@Gamma|=i$ and $|@Delta|=j$.
@end[doc] >>

declare Var
declare var{'left; 'right} (* depth = left + right + 1 *)
declare left{'v}
declare right{'v}

prim_rw left_id {| reduce |} :
   'left in nat -->
   'right in nat -->
   left {var{'left; 'right}} <--> 'left

prim_rw right_id {| reduce |} :
   'left in nat -->
   'right in nat -->
   right {var{'left; 'right}} <--> 'right

doc <:doc< @begin[doc]
 @modsection{Definitions}
 @modsubsection{Depth}
 The depth of a variable <<var{'i;'j}>> is <<'i+@'j+@1>>.
@end[doc] >>

define unfold_depth:
   depth{'v} <--> left{'v} +@ right{'v} +@ 1

interactive_rw depth_reduce {| reduce |} :
   'l in nat -->
   'r in nat -->
   depth{var{'l;'r}} <--> 'l +@ 'r +@ 1

doc <:doc< @begin[doc]
   <<Var{'n}>> is a set of variables with depth <<'n>>.
@end[doc] >>

define unfold_var: Var{'n} <--> {v:Var| depth{'v} = 'n in int }

doc <:doc< @begin[doc]
   @modsubsection{Equality}
   Variables <<var{'i;'j}>> and <<var{'i;'k}>> represent the same binding
   << 'x >> in $bterm(@Gamma; x; @Delta. t[x])$ where $|@Gamma|=i$.
   We define:
@end[doc] >>

define unfold_is_eq:
   is_eq{'v;'u} <--> (left{'v} =@ left{'u})

interactive_rw eq_equal {| reduce |} :
   'left_1 in nat -->
   'left_2 in nat -->
   'right_1 in nat -->
   'right_2 in nat -->
   is_eq{var{'left_1; 'right_1};var{'left_2; 'right_2}} <--> ('left_1 =@ 'left_2)

doc "doc"{rules}

prim var_univ {| intro [] |}:
   sequent { <H> >- Var in univ[l:l] } = it

interactive var_type {| intro [] |}:
   sequent { <H> >- Var Type }

prim var_wf {| intro [] |} :
   sequent { <H> >- 'left in nat } -->
   sequent { <H> >- 'right in nat } -->
   sequent { <H> >- var{'left; 'right} in Var } = it

prim var_elim {| elim [] |} 'H :
   ('ext['left; 'right]: sequent { <H>; left: nat; right: nat; <J[var{'left; 'right}]>
      >- 'C[var{'left; 'right}] }) -->
   sequent { <H>; v: Var; <J['v]> >- 'C['v] } = 'ext[left{'v}; right{'v}]

interactive left_wf {| intro [] |} :
   sequent { <H> >- 'v in Var } -->
   sequent { <H> >- left{'v} in nat }

interactive left_wf2 {| intro [] |} :
   sequent { <H> >- 'v in Var } -->
   sequent { <H> >- left{'v} in int }

interactive right_wf {| intro [] |} :
   sequent { <H> >- 'v in Var } -->
   sequent { <H> >- right{'v} in nat }

interactive right_wf2 {| intro [] |} :
   sequent { <H> >- 'v in Var } -->
   sequent { <H> >- right{'v} in int }

interactive depth_wf {| intro [] |} :
   sequent { <H> >- 'v in Var } -->
   sequent { <H> >- depth{'v} in nat }

interactive depth_wf2 {| intro [] |} :
   sequent { <H> >- 'v in Var } -->
   sequent { <H> >- depth{'v} in int }

interactive eq_wf {| intro [] |} :
   sequent { <H> >- 'v1 in Var } -->
   sequent { <H> >- 'v2 in Var } -->
   sequent { <H> >- is_eq{'v1; 'v2} in bool }

interactive eq_wf1 {| intro [] |} :
   sequent { <H> >- 'v1 in Var } -->
   sequent { <H> >- 'v2 in Var } -->
   sequent { <H> >- eq{'v1; 'v2} Type }

interactive_rw eq_same {| reduce |} :
   ('v in Var) -->
   is_eq{'v;'v} <--> btrue

interactive eq_sym :
   sequent { <H> >- 'v1 in Var } -->
   sequent { <H> >- 'v2 in Var } -->
   sequent { <H> >- "assert"{is_eq{'v1; 'v2}} } -->
   sequent { <H> >- "assert"{is_eq{'v2; 'v1}} }

interactive eq_trans 'v2 :
   sequent { <H> >- 'v1 in Var } -->
   sequent { <H> >- 'v2 in Var } -->
   sequent { <H> >- 'v3 in Var } -->
   sequent { <H> >- "assert"{is_eq{'v1; 'v2}} } -->
   sequent { <H> >- "assert"{is_eq{'v2; 'v3}} } -->
   sequent { <H> >- "assert"{is_eq{'v1; 'v3}} }

(* XXX: TODO: arith tactics need to know abot the next 3 rules *)

interactive depth_pos {| intro [] |} :
   sequent { <H> >- 'v in Var } -->
   sequent { <H> >- depth{'v} > 0 }

interactive left_bound {| intro [] |} :
   sequent { <H> >- 'v in Var } -->
   sequent { <H> >- left{'v} < depth{'v} }

interactive right_bound {| intro [] |} :
   sequent { <H> >- 'v in Var } -->
   sequent { <H> >- right{'v} < depth{'v} }

interactive leftSquiggle {| intro [] |} :
   sequent { <H> >- 'v1 = 'v2 in Var } -->
   sequent { <H> >- left{'v1} ~ left{'v2} }

interactive rightSquiggle {| intro [] |} :
   sequent { <H> >- 'v1 = 'v2 in Var } -->
   sequent { <H> >- right{'v1} ~ right{'v2} }

interactive varSquiggle {| nth_hyp |} :
   sequent { <H> >- 'b1 = 'b2 in Var } -->
   sequent { <H> >- 'b1 ~ 'b2 }

doc docoff

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform var_df : var{'l; 'r} = `"var(" slot{'l} `"," slot{'r} `")"
dform left_df : left{'v} = pi sub["L"] `"("slot{'v} `")"
dform right_df : right{'v} = pi sub["R"] `"(" slot{'v} `")"
dform depth_df : depth{'v} = `"depth(" slot{'v} `")"
dform var_df : Var{'n} = Var sub{'n}
dform is_eq_df : is_eq{'v;'u} =  slot{'v} space cong sub{bool} space slot{'u}
dform eq_df : eq{'v;'u} =  slot{'v} space cong sub{Var} space slot{'u}
