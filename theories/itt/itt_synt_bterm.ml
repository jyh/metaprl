doc <:doc<
   @begin[doc]
   @module[Itt_reflection]

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
extends Itt_nat
extends Itt_synt_var
extends Itt_synt_operator
doc docoff


open Dtactic

open Basic_tactics
open Itt_nat
open Itt_equal
open Itt_struct
open Itt_squash

(************************************************************************
 * The BTerm type                                                       *
 ************************************************************************)


declare BTerm
declare make_bterm{'op; 'subterms}
declare bterm_ind{'bt; v.'var_case['v];
                       op,subterms,ind. 'op_case['op; 'subterms; 'ind] }

dform bterm_df : except_mode[src] :: BTerm =
   `"BTerm"

dform make_bterm_df : except_mode[src] :: make_bterm{'bt; 'btl} =
   `"make_bterm(" slot{'bt} `"; " slot{'btl} `")"




prim_rw bterm_ind_op_reduce {| reduce |}:
      bterm_ind{make_bterm{'op; 'subterms};
                v.'var_case['v];
                op,subterms,ind. 'op_case['op; 'subterms; 'ind] } <-->
         'op_case['op;
                  'subterms;
                  all_list_witness{ 'subterms; x.bterm_ind{'x;v.'var_case['v]; op,subterms,ind. 'op_case['op; 'subterms; 'ind]} }]

prim_rw bterm_ind_var_reduce {| reduce |}:
      bterm_ind{var{'l;'r};
                v.'var_case['v];
                op,subterms,ind. 'op_case['op; 'subterms; 'ind] } <-->
         'var_case[var{'l;'r}]


interactive_rw bterm_ind_var_reduce2 :
      ('v in Var) -->
      bterm_ind{'v;
                v.'var_case['v];
                op,subterms,ind. 'op_case['op; 'subterms; 'ind] } <-->
         'var_case['v]


define unfold_bdepth: bdepth{'bt} <--> bterm_ind{'bt; v. depth{'v}; op,btl,ind. op_bdepth{'op}}


define unfold_compatible_shapes: compatible_shapes{'op; 'btl} <-->
   fix{ f. lambda{ diff. lambda{ arity. lambda{ btl.
      list_ind{ 'arity; is_nil{'btl}; h1,t1,g.
         list_ind{ 'btl; bfalse; h2,t2,g.
            (bdepth{'h2} -@ 'h1 = 'diff in int) and  ('f 'diff 't1 't2) } }
      } } } } op_bdepth{'op} arity{'op} 'btl

prim btermUniv {| intro [] |} :
   sequent { <H> >- BTerm in univ[i:l] } =
   it

interactive btermType {| intro [] |} :
   sequent { <H> >- BTerm Type }

prim btermVar {| intro [AutoMustComplete] |} :
   sequent { <H> >- 'v in Var } -->
   sequent { <H> >- 'v in BTerm }
   = it

prim makebterm_wf {| intro [] |} :
   sequent { <H> >- 'op in BOperator } -->
   sequent { <H> >- 'btl in list{BTerm} } -->
   sequent { <H> >- compatible_shapes{'op; 'btl} } -->
   sequent { <H> >- make_bterm{'op; 'btl} in BTerm } =
   it

prim bterm_ind_wf {| intro [] |} bind{bt.'C['bt]}:
   sequent { <H> >- 'bt in BTerm } -->
   sequent { <H>; v:Var >- 'var_case['v] in 'C['v] } -->
   sequent { <H>; op:BOperator; subterms:list{BTerm}; compatible_shapes{'op;'subterms}; ind_hyp:all_list{'subterms; x.'C['x]}
                >- 'op_case['op;'subterms;'ind_hyp] in 'C[make_bterm{'op;'subterms}] } -->
   sequent { <H> >-  bterm_ind{'bt;
                               v.'var_case['v];
                               op,subterms,ind_hyp. 'op_case['op; 'subterms; 'ind_hyp] } in 'C['bt] } =
   it


prim operatorSquiddle {| intro[] |} :
   sequent { <H> >- 'op1 = 'op2 in BOperator } -->
   sequent { <H> >- 'btl in list{BTerm} } -->
   sequent { <H> >- compatible_shapes{'op1; 'btl} } -->
   sequent { <H> >- make_bterm{'op1; 'btl} ~ make_bterm{'op2; 'btl} } =
   it



(* Derivable rules *)

interactive bterm_elim {| elim [] |} 'H :
   sequent { <H>; b: BTerm; <J['b]>; v:Var >- 'C['v] } -->
   sequent { <H>; b: BTerm; <J['b]>; op: BOperator; bl: list{BTerm}; compatible_shapes{'op;'bl};
      ind_hyp:all_list{'bl; a.'C['a]} >- 'C[make_bterm{'op; 'bl}] }  -->
   sequent { <H>; b: BTerm; <J['b]> >- 'C['b] }

define unfold_dest_bterm:
      dest_bterm{'bt; v.'var_case['v];
                      op,subterms. 'op_case['op; 'subterms] }
 <--> bterm_ind{'bt; v.'var_case['v];
                     op,subterms,ind. 'op_case['op; 'subterms] }


interactive var_subtype {| intro [] |} :
   sequent { <H> >- Var subtype BTerm }


interactive btermSquiddle {| nth_hyp |} :
   sequent { <H> >- 'b1 = 'b2 in BTerm } -->
   sequent { <H> >- 'b1 ~ 'b2 }

interactive btermlistSquiddle {| nth_hyp |} :
   sequent { <H> >- 'b1 = 'b2 in list{BTerm} } -->
   sequent { <H> >- 'b1 ~ 'b2 }
