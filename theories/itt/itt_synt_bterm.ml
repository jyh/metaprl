doc <:doc<
   @module[Itt_synt_bterm]
   The @tt[Itt_synt_bterm] module defines a type of bterms << BTerm >>
   for our simple theory of syntax.

   @docoff
   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/index.html for information on Nuprl,
   OCaml, and more information about this system.

   Copyright (C) 2005 MetaPRL Group

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

   Authors: Alexei Kopylov @email{kopylov@cs.caltech.edu}
            Aleksey Nogin @email{nogin@cs.caltech.edu}
            Xin Yu @email{xiny@cs.caltech.edu}
   @end[license]
>>

doc <:doc<
   @parents
>>
extends Itt_theory
extends Itt_nat
extends Itt_list2
extends Itt_synt_var
extends Itt_synt_operator
extends Itt_pairwise2
doc docoff

open Basic_tactics
open Itt_nat
open Itt_equal
open Itt_struct
open Itt_squash

(************************************************************************
 * The BTerm type                                                       *
 ************************************************************************)

doc <:doc<
   @modsection{BTerm}

   The << BTerm >> type is defined recursively. A syntactic term is either
   a variable of type << Var >> or a composed term of the form
   << make_bterm{'op; 'mbtl} >>, where << 'op >> is an operator of type
   << BOperator >>, << 'mbtl >> is a list of syntactic terms, and << 'mbtl >>
   must be compatible with the shape and the binding depth of << 'op >>.

   The @tt[bterm_ind] defines the induction combinator for the << BTerm >> type.

>>


declare BTerm
declare make_bterm{'op; 'subterms}
declare bterm_ind{'bt; v.'var_case['v];
                       op,subterms,ind. 'op_case['op; 'subterms; 'ind] }

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
doc docoff

dform bterm_df : BTerm = `"BTerm"
dform make_bterm_df : make_bterm{'bt; 'btl} =
   `"make_bterm(" slot{'bt} `"; " slot{'btl} `")"
dform bterm_ind_df : bterm_ind{'bt; v.'var_case; op,subterms,ind. 'op_case } =
   szone pushm[1] pushm[3]
   `"match " slot{'bt} `" with" hspace
   pushm[3] slot{'v} `" ->" hspace slot{'var_case} popm popm hspace
   `"| " pushm[3] `"make_bterm(" slot{'op} `";" slot{'subterms} `")." slot{'ind} `" ->" hspace slot{'op_case} popm popm ezone

doc <:doc<
   @modsubsection{Depth}
   When a bterm << 'bt >> is a variable, its binding depth << bdepth{'bt} >>
   is defined as the depth of << 'bt >> as defined in @hrefmodule[Itt_synt_var].
   When << 'bt >> is a composed term of the form << make_bterm{'op; 'mbtl} >>,
   its binding depth is defined as the binding depth of the operator << 'op >>.
>>

define unfold_bdepth: bdepth{'bt} <--> bterm_ind{'bt; v. depth{'v}; op,btl,ind. op_bdepth{'op}}

interactive_rw bdepth_reduce1 {| reduce |} :  bdepth{make_bterm{'op;'btl}} <--> op_bdepth{'op}

interactive_rw bdepth_reduce2 {| reduce |} :  bdepth{var{'l;'r}} <--> depth{var{'l;'r}}

interactive_rw bdepth_var_reduce: ('v in Var) --> bdepth{'v} <--> depth{'v}
doc docoff
dform bdepth_df: bdepth{'bt} = `"bdepth(" slot{'bt} `")"

doc <:doc<
   @modsubsection{Compatible shapes}

   Suppose the shape of an operator << 'op >> is $[b_1;@ldots;b_n]$ ($n @ge 0$)
   and its binding depth is << 'd >>. We say << 'mbtl >> and << 'op >> have
   compatible shapes if << 'mbtl >> is a list of length << 'n >> where the
   binding depth of the $i$-@misspelled{th} element is $b_i+d$ (for each $i @in 1..n$).
>>
define unfold_compatible_shapes: compatible_shapes{'op; 'btl} <-->
      length{shape{'op}} = length{'btl} in int &
      all i:Index{'btl}. bdepth{nth{'btl;'i}} =  op_bdepth{'op} +@ nth{shape{'op};'i} in int
doc docoff

dform compatible_shapes_df: compatible_shapes{'op;'btl} = `"compatible_shapes(" slot{'op} `";" slot{'btl} `")"

doc rules

prim btermUniv {| intro [] |} :
   sequent { <H> >- BTerm in univ[i:l] } =
   it

prim btermVar {| nth_hyp |} 'H :
   sequent { <H>; v: Var; <J['v]> >- 'v in BTerm }
   = it

prim makebterm_wf {| intro [] |} :
   sequent { <H> >- 'op in BOperator } -->
   sequent { <H> >- 'btl in list{BTerm} } -->
   sequent { <H> >- compatible_shapes{'op; 'btl} } -->
   sequent { <H> >- make_bterm{'op; 'btl} in BTerm } =
   it

prim operatorSquiggle {| intro[] |} :
   sequent { <H> >- 'op1 = 'op2 in BOperator } -->
   sequent { <H> >- 'btl in list{BTerm} } -->
   sequent { <H> >- compatible_shapes{'op1; 'btl} } -->
   sequent { <H> >- make_bterm{'op1; 'btl} ~ make_bterm{'op2; 'btl} } =
   it

prim bterm_elim {| elim [] |} 'H :
   ('var_case['b;'v]: sequent { <H>; b: BTerm; <J['b]>; v:Var >- 'C['v] }) -->
   ('op_case['b;'op;'bl;'cs;'ind_hyp]: sequent { <H>; b: BTerm; <J['b]>; op: BOperator; bl: list{BTerm}; cs:compatible_shapes{'op;'bl};
      ind_hyp:all_list{'bl; a.'C['a]} >- 'C[make_bterm{'op; 'bl}] })  -->
   sequent { <H>; b: BTerm; <J['b]> >- 'C['b] }
      =  bterm_ind{'b;
                       v.'var_case['b;'v];
                       op,bl,ind_hyp. 'op_case['b;'op; 'bl; it; 'ind_hyp] }

(* Derivable rules *)

interactive btermType {| intro [] |} :
   sequent { <H> >- BTerm Type }

interactive bterm_ind_wf {| intro [] |} bind{bt.'C['bt]}:
   sequent { <H> >- 'bt in BTerm } -->
   sequent { <H>; v:Var >- 'var_case['v] in 'C['v] } -->
   sequent { <H>; op:BOperator; subterms:list{BTerm}; compatible_shapes{'op;'subterms}; ind_hyp:all_list{'subterms; x.'C['x]}
                >- 'op_case['op;'subterms;'ind_hyp] in 'C[make_bterm{'op;'subterms}] } -->
   sequent { <H> >-  bterm_ind{'bt;
                               v.'var_case['v];
                               op,subterms,ind_hyp. 'op_case['op; 'subterms; 'ind_hyp] } in 'C['bt] }

interactive bdepth_wf {| intro[] |} :
   sequent { <H> >- 'bt in BTerm } -->
   sequent { <H> >- bdepth{'bt} in nat }

interactive bdepth_wf2 {| intro[] |} :
   sequent { <H> >- 'bt in BTerm } -->
   sequent { <H> >- bdepth{'bt} in int }

interactive bdepth_wf3 {| intro[] |} :
   sequent { <H> >- 'bt in BTerm } -->
   sequent { <H> >- bdepth{'bt} >= 0 }

interactive compatible_shapes_wf {| intro [] |} :
   sequent { <H> >- 'op in BOperator } -->
   sequent { <H> >- 'btl in list{BTerm} } -->
   sequent { <H> >- compatible_shapes{'op; 'btl} Type }

interactive compatible_shapes_intro {| intro [] |} :
   sequent { <H> >- length{shape{'op}} = length{'btl} in int } -->
   sequent { <H> >- all i:Index{'btl}. bdepth{nth{'btl;'i}} =  op_bdepth{'op} +@ nth{shape{'op};'i} in int } -->
   sequent { <H> >- compatible_shapes{'op; 'btl} }

interactive compatible_shapes_squash :
   [wf] sequent { <H> >- 'btl in list } -->
   [wf] sequent { <H> >- squash{compatible_shapes{'op; 'btl}} } -->
   sequent { <H> >- compatible_shapes{'op; 'btl} }

interactive makebterm_wf2 {| intro [] |} :
   sequent { <H> >- 'op1 = 'op2 in BOperator } -->
   sequent { <H> >- 'btl in list{BTerm} } -->
   sequent { <H> >- compatible_shapes{'op2; 'btl} } -->
   sequent { <H> >- make_bterm{'op1; 'btl} = make_bterm{'op2; 'btl} in BTerm }

interactive var_subtype {| intro [] |} :
   sequent { <H> >- Var subtype BTerm }

interactive subterms_have_greater_bdepth {| intro [AutoMustComplete] |} :
   sequent { <H> >- 'op in BOperator } -->
   sequent { <H> >- 'btl in list{BTerm} } -->
   sequent { <H> >- compatible_shapes{'op;'btl} } -->
   sequent { <H> >- all_list{'btl; bt. bdepth{'bt} >= op_bdepth{'op}} }

doc <:doc<
   <<BTerm{'n}>> is a set of bterms with depth <<'n>>; <<BTerm_plus{'n}>> is a set of bterms with depth greater than or equal to <<'n>>.
>>

define iform bterm: BTerm{'n} <--> { bt:BTerm | bdepth{'bt} = 'n in nat }
define iform bterm_plus: BTerm_plus{'n} <--> { bt:BTerm | bdepth{'bt} >= 'n }

doc <:doc<

   << make_bterm{'op;'bdepth;'subterms} >> is a version of a bterm that
   takes the depth as an argument.

   @tt[dest_bterm] is a special case of @tt[bterm_ind] where <<'ind>> is
   omitted. It is simpler than @tt[bterm_ind], but is as powerful since
   @tt[bterm_ind] can also be defined using @tt[dest_bterm] and the
   @tt[fix] operator.

>>

define iform make_bterm: make_bterm{'op;'bdepth;'subterms} <--> make_bterm{inject{'op;'bdepth};'subterms}

define iform dest_bterm:
   dest_bterm{'bt; v.'var_case['v];
                   op,subterms. 'op_case['op; 'subterms] }
   <--> bterm_ind{'bt; v.'var_case['v];
                       op,subterms,ind. 'op_case['op; 'subterms] }

interactive_rw make_bterm_depth:
   ('op in BOperator) -->
   ('subterms in list{BTerm}) -->
   (compatible_shapes{'op; 'subterms}) -->
   make_bterm{'op;'subterms} <--> make_bterm{'op; op_bdepth{'op};'subterms}
doc docoff

dform make_bterm_df: make_bterm{'op;'bdepth;'subterms} =
   `"make_bterm" sub{'bdepth} `"(" slot{'op} `"; " slot{'subterms} `")"

(*
dform dest_bterm_df : dest_bterm{'bt; v.'var_case; op,subterms. 'op_case } =
   szone pushm[1] pushm[3]
   `"match " slot{'bt} `" with" hspace
   pushm[3] slot{'v} `" ->" hspace slot{'var_case} popm popm hspace
   `"| " pushm[3] `"make_bterm(" slot{'op} `";" slot{'subterms} `") ->" hspace slot{'op_case} popm popm ezone
*)
doc <:doc<
   << Vars_of{'bt} >> defines the set of variables whose depth is less than or
   equal to the depth of << 'bt >>.
>>

define unfold_vars_of: Vars_of{'bt} <--> { v: Var | bdepth{'v} <= bdepth{'bt} }

interactive vars_of_wf {| intro [] |} :
   [wf] sequent { <H> >- 'bt in BTerm } -->
   sequent { <H> >- Vars_of{'bt} Type }

interactive vars_of_intro {| intro [] |} :
   [wf] sequent { <H> >- 'v in Var } -->
   [wf] sequent { <H> >- 'bt in BTerm } -->
   sequent { <H> >- bdepth{'v} <= bdepth{'bt} } -->
   sequent { <H> >- 'v in Vars_of{'bt} }

interactive vars_of_elim {| elim [] |} 'H :
   sequent { <H>; v: Var; i: bdepth{'v} <= bdepth{'bt}; <J['v]> >- 'T['v] } -->
   sequent { <H>; v: Vars_of{'bt}; <J['v]> >- 'T['v] }

interactive vars_of_member {| nth_hyp |} 'H :
   sequent { <H>; u: Vars_of{'bt}; <J['u]> >- 'u in Var }
doc docoff
dform vars_of_df: Vars_of{'bt} = `"Vars_of(" slot{'bt} `")"

(************************************************************************
 * Var_bterm                                                            *
 ************************************************************************)
doc <:doc<
   << var_bterm{'bt} >> returns <<"true">> if << 'bt >> is in << Var >>,
   <<"false">> otherwise.
>>

define unfold_is_var_bterm: is_var_bterm{'bt} <--> dest_bterm{'bt; v.btrue; op,btl. bfalse}
define unfold_var_bterm: var_bterm{'bt} <--> "assert"{is_var_bterm{'bt}}
doc docoff

dform is_var_bterm_df : except_mode[src] :: is_var_bterm{'bt} =
   `"is_var_bterm(" slot{'bt} `")"
dform var_bterm_df : except_mode[src] :: var_bterm{'bt} =
   `"var_bterm(" slot{'bt} `")"

let fold_var_bterm = makeFoldC << var_bterm{'bt} >> unfold_var_bterm

doc <:doc<
>>
interactive_rw is_var_reduce1 {| reduce |}: is_var_bterm{var{'l;'r}} <--> btrue
interactive_rw is_var_reduce2 {| reduce |}: is_var_bterm{make_bterm{'op;'btl}} <--> bfalse
interactive_rw var_reduce1 {| reduce |}: var_bterm{var{'l;'r}} <--> "assert"{btrue}
interactive_rw var_reduce2 {| reduce |}: var_bterm{make_bterm{'op;'btl}} <--> "assert"{bfalse}

interactive is_var_bterm_wf {| intro [] |} :
   sequent { <H> >- 'bt in BTerm } -->
   sequent { <H> >- is_var_bterm{'bt} in bool }

interactive_rw varbterm_is_varbterm :
   (var_bterm{ 'bt}) -->
   is_var_bterm{'bt} <--> btrue

interactive_rw notvarbterm_is_not_varbterm :
   ('bt in BTerm ) -->
   (not{var_bterm{ 'bt}} ) -->
   is_var_bterm{'bt} <--> bfalse

interactive var_bterm_wf {| intro [] |} :
   sequent { <H> >- 'bt in BTerm } -->
   sequent { <H> >- var_bterm{'bt} Type }

interactive var_bterm_univ {| intro [] |} :
   [wf] sequent { <H> >- 'bt in BTerm } -->
   sequent { <H> >- var_bterm{'bt} in univ[i:l] }

interactive var_bterm_decidable {| intro [] |} :
   [wf] sequent { <H> >- 'bt in BTerm } -->
   sequent { <H> >- decidable{var_bterm{'bt}} }

interactive var_intro1 :
   sequent { <H> >- 'b in BTerm } -->
   sequent { <H> >- var_bterm{'b} } -->
   sequent { <H> >- 'b in Var }

interactive var_intro :
   sequent { <H> >- 'b1 = 'b2 in BTerm } -->
   sequent { <H> >- var_bterm{'b1} } -->
   sequent { <H> >- 'b1 = 'b2 in Var }

interactive var_elim 'H :
   sequent { <H>; u: BTerm; v: var_bterm{'u}; <J['u]> >- 'T['u] } -->
   sequent { <H>; u: Var; <J['u]> >- 'T['u] }

interactive_rw var_is_var:
   ('v in Var) -->
   is_var_bterm{'v} <--> btrue

interactive var_bterm {| intro [] |} :
   sequent { <H> >- 'l in nat} -->
   sequent { <H> >- 'r in nat} -->
   sequent { <H> >- var{'l; 'r} in BTerm }

(************************************************************************
 * OpBTerm                                                              *
 ************************************************************************)

doc <:doc<
   << OpBTerm >> is the set of non-variable bterms. So, a bterm is either in
   << Var >> or in << OpBTerm >>, but not in both.
>>
define unfold_opbterm:
   OpBTerm <--> { bt: BTerm |  not{ var_bterm{'bt} } }
doc docoff

dform opbterm_df : except_mode[src] :: OpBTerm =
   `"OpBTerm"

doc <:doc<
>>
interactive opbterm_univ {| intro [] |} :
   sequent { <H> >- OpBTerm in univ[i:l] }

interactive opbterm_wf {| intro [] |} :
   sequent { <H> >- OpBTerm Type }

interactive opbterm_subtype {| intro [] |} :
   sequent { <H> >- OpBTerm subtype BTerm }

interactive opbterm_intro {| intro [] |} :
   sequent { <H> >- 'b1 = 'b2 in BTerm } -->
   sequent { <H>; var_bterm{'b1} >- "false" } -->
   sequent { <H> >- 'b1 = 'b2 in OpBTerm }

interactive opbterm_elim {| elim [] |} 'H :
   sequent { <H>; u: BTerm; v: not{ var_bterm{'u} }; <J['u]> >- 'T['u] } -->
   sequent { <H>; u: OpBTerm; <J['u]> >- 'T['u] }

interactive_rw opbterm_is_not_var:
   ('v in OpBTerm) -->
   is_var_bterm{'v} <--> bfalse

interactive var_or_opbterm_concl bind{x. 'C['x]} 'b :
   [wf] sequent { <H> >- 'b in BTerm } -->
   [main] sequent { <H>; b: Var >- 'C['b] } -->
   [main] sequent { <H>; b: OpBTerm >- 'C['b] } -->
   sequent { <H> >- 'C['b] }

interactive var_or_opbterm_hyp 'H bind{x. 'A['x]} 'b :
   [wf] sequent { <H>; x: 'A['b]; <J['x]> >- 'b in BTerm } -->
   [main] sequent { <H>; x: 'A['b]; <J['x]>; 'b in Var >- 'C['x] } -->
   [main] sequent { <H>; x: 'A['b]; <J['x]>; 'b in OpBTerm >- 'C['x] } -->
   sequent { <H>; x: 'A['b]; <J['x]> >- 'C['x] }

(************************************************************************
 * Op_of                                                                *
 ************************************************************************)

doc <:doc<
   << op_of{'t} >> returns the operator of a bterm << 't >>.
>>
define unfold_op_of:
   op_of{'t} <--> dest_bterm{'t; v.'v; op,subterms.'op}
doc docoff

dform op_of_df: op_of{'bt} = `"op_of(" slot{'bt} `")"

doc <:doc<
>>
interactive_rw op_of_reduce {| reduce |}: op_of{make_bterm{'op;'btl}} <--> 'op

interactive op_of_wf {| intro [] |} :
   sequent { <H> >- 'bt in OpBTerm } -->
   sequent { <H> >- op_of{'bt} in BOperator }

interactive op_of_wf1 {| intro [] |} :
   sequent { <H> >- 'b1 = 'b2 in OpBTerm } -->
   sequent { <H> >- op_of{'b1} = op_of{'b2} in BOperator }

interactive op_of_eq 'bl1 'bl2 :
   sequent { <H> >- 'op1 in BOperator } -->
   sequent { <H> >- 'op2 in BOperator } -->
   sequent { <H> >- 'bl1 in list{BTerm} } -->
   sequent { <H> >- 'bl2 in list{BTerm} } -->
   sequent { <H> >- compatible_shapes{'op1; 'bl1} } -->
   sequent { <H> >- compatible_shapes{'op2; 'bl2} } -->
   sequent { <H> >- make_bterm{'op1; 'bl1} = make_bterm{'op2; 'bl2} in BTerm} -->
   sequent { <H> >- 'op1 = 'op2 in BOperator}

(************************************************************************
 * Subterms                                                             *
 ************************************************************************)

doc <:doc<
   << subterms{'t} >> returns the subterms of a bterm << 't >>.
>>
define unfold_subterms:
   subterms{'t} <--> dest_bterm{'t; v.nil; op,subterms.'subterms}
doc docoff

dform subterms_df : except_mode[src] :: subterms{'bt} =
   `"subterms(" slot{'bt} `")"

doc <:doc<
>>
interactive_rw subterms_reduce1 {| reduce |}:  subterms{var{'l;'r}} <--> nil
interactive_rw subterms_reduce2 {| reduce |}:  subterms{make_bterm{'op;'btl}} <--> 'btl

interactive subterms_wf {| intro [] |} :
   sequent { <H> >- 'bt in BTerm } -->
   sequent { <H> >- subterms{'bt} in list{BTerm} }

interactive_rw subterms_var :
   ('bt in Var) -->
   subterms{'bt} <--> nil

doc <:doc<
   We can prove if two bterms are equal, then they are squiggle equal.
>>
interactive btermSquiggle {| nth_hyp |} :
   sequent { <H> >- 'b1 = 'b2 in BTerm } -->
   sequent { <H> >- 'b1 ~ 'b2 }

interactive btermlistSquiggle {| nth_hyp |} :
   sequent { <H> >- 'b1 = 'b2 in list{BTerm} } -->
   sequent { <H> >- 'b1 ~ 'b2 }
doc docoff

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of bterm and subterms of bterms.
 *)
let resource typeinf += (<< BTerm >>, infer_univ1)
let resource typeinf += (<< subterms{'bt} >>, infer_const << list{BTerm} >>)

(************************************************************************
 * Same_op_of                                                              *
 ************************************************************************)

doc <:doc<
   << same_op_of{'b1; 'b2} >> decides whether two bterms have the same operator.
   If both are variables, it returns << "true" >>; if both are composed bterms,
   its result depends on whether their operators are the same; otherwise, it
   returns << "false">>.
>>
define unfold_is_same_op_of: is_same_op_of{'b1; 'b2} <-->
   dest_bterm{'b1;
               v1. dest_bterm{'b2; v2. is_eq{'v1;'v2}; op2,btl2.bfalse};
               op1,btl1. dest_bterm{'b2; v2. bfalse;
                                    op2,btl2. is_same_op{'op1;'op2}} }

define unfold_same_op_of: same_op_of{'b1; 'b2} <--> "assert"{is_same_op_of{'b1; 'b2}}
doc docoff

dform is_same_op_of_df : except_mode[src] :: is_same_op_of{'b1; 'b2} =
   `"is_same_op_of(" slot{'b1} `"; " slot{'b2} `")"
dform same_op_of_df : except_mode[src] :: same_op_of{'b1; 'b2} =
   `"same_op_of(" slot{'b1} `"; " slot{'b2} `")"

doc docon
interactive is_same_op_of_wf {| intro [] |} :
   sequent { <H> >- 'b1 in BTerm } -->
   sequent { <H> >- 'b2 in BTerm } -->
   sequent { <H> >- is_same_op_of{'b1; 'b2} in bool }

interactive_rw sameop_is_sameop :
   (same_op_of{'b1; 'b2}) -->
   is_same_op_of{'b1; 'b2} <--> btrue

interactive_rw notsameop_is_not_sameop :
   ('b1 in BTerm ) -->
   ('b2 in BTerm ) -->
   (not{same_op_of{'b1; 'b2}} ) -->
   is_same_op_of{'b1; 'b2} <--> bfalse

interactive same_op_of_wf {| intro [] |} :
   sequent { <H> >- 'b1 in BTerm } -->
   sequent { <H> >- 'b2 in BTerm } -->
   sequent { <H> >- same_op_of{'b1; 'b2} Type }

interactive same_op_of_decidable {| intro [] |} :
   [wf] sequent { <H> >- 'b1 in BTerm } -->
   [wf] sequent { <H> >- 'b2 in BTerm } -->
   sequent { <H> >- decidable{same_op_of{'b1; 'b2}} }

interactive same_op_of_id {| intro [] |} :
   sequent { <H> >- 'b in BTerm } -->
   sequent { <H> >- same_op_of{'b; 'b} }

interactive same_op_of_id2 {| intro [AutoMustComplete] |} :
   sequent { <H> >- 'b1 = 'b2 in BTerm } -->
   sequent { <H> >- same_op_of{'b1; 'b2} }

interactive same_op_of_sym :
   sequent { <H> >- 'b1 in BTerm } -->
   sequent { <H> >- 'b2 in BTerm } -->
   sequent { <H> >- same_op_of{'b1; 'b2} } -->
   sequent { <H> >- same_op_of{'b2; 'b1} }

interactive same_op_of_trans 'b2:
   sequent { <H> >- 'b1 in BTerm } -->
   sequent { <H> >- 'b2 in BTerm } -->
   sequent { <H> >- 'b3 in BTerm } -->
   sequent { <H> >- same_op_of{'b1; 'b2} } -->
   sequent { <H> >- same_op_of{'b2; 'b3} } -->
   sequent { <H> >- same_op_of{'b1; 'b3} }

interactive_rw is_same_op_make_bterm :
   ('op in BOperator) -->
   ('btl in list{BTerm}) -->
   (compatible_shapes{'op; 'btl}) -->
   is_same_op{op_of{make_bterm{'op; 'btl}}; 'op} <--> btrue
doc docoff

let sameOpOfSymT = same_op_of_sym
let sameOpOfTransT = same_op_of_trans
