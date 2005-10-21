doc <:doc<
   @module[Itt_hoas_lambda]
   The @tt[Itt_hoas_lambda] module is a toy example of how we are going
   to define a language.

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

   Author: Xin Yu @email{xiny@cs.caltech.edu}

   @end[license]
>>

doc <:doc< @parents >>
extends Itt_hoas_lang
doc docoff
extends Itt_nequal

open Basic_tactics

define app_op : app_op <--> operator[(apply{it;it}):op]
define lambda_op: lambda_op <-->  operator[(lambda{x.it}):op]
define iform lambdaTerm: LambdaTerm <--> Lang{SubOp{lambda_op::app_op::nil}}

dform app_df: app_op = `"\"apply\""
dform lambda_df: lambda_op = `"\"" lambda "\""
dform lambdaterm_df: LambdaTerm = `"Term" sub{lambda}

interactive app_wf {| intro[] |}:
   sequent{ <H> >-  app_op in Operator }

interactive lambda_wf {| intro[] |}:
   sequent{ <H> >-  lambda_op in Operator }

interactive_rw shape_of_app {| reduce |}: shape{app_op} <--> (0::0::nil)

interactive_rw shape_of_lam {| reduce |}: shape{lambda_op} <--> (1::nil)

interactive lambda_app_diffops {| intro[] |}:
   sequent{ <H> >- app_op <> lambda_op in Operator }

interactive lambdaterm_induction  {| elim[] |} 'H:
   sequent { <H>; x: LambdaTerm; <J['x]>; l: nat; r:nat >- 'P[var{'l;'r}] } -->
   sequent { <H>; x: LambdaTerm; <J['x]>; n: nat; t: LambdaTerm; s:LambdaTerm; bdepth{'t} = 'n in int; bdepth{'s} = 'n in nat(*; 'P['t]; 'P['s]*) >- 'P[ mk_bterm{'n; app_op; 't::'s::nil} ] } -->
   sequent { <H>; x: LambdaTerm; <J['x]>; n: nat; t: LambdaTerm; bdepth{'t} = 'n +@ 1in int(*; 'P['t]*) >- 'P[ mk_bterm{'n; lambda_op; 't::nil} ] } -->
   sequent { <H>; x: LambdaTerm; <J['x]> >- 'P['x] }

interactive lambda_intro  {| intro[] |} :
   sequent { <H> >- 'n in nat } -->
   sequent { <H> >- 't in LambdaTerm } -->
   sequent { <H> >- bdepth{'t} = 'n +@ 1 in int } -->
   sequent { <H> >- mk_bterm{'n; lambda_op; 't::nil} in LambdaTerm }

interactive app_intro  {| intro[] |} :
   sequent { <H> >- 'n in nat } -->
   sequent { <H> >- 't in LambdaTerm } -->
   sequent { <H> >- 's in LambdaTerm } -->
   sequent { <H> >- bdepth {'t} = 'n in int  } -->
   sequent { <H> >- bdepth {'s} = 'n in int  } -->
   sequent { <H> >- mk_bterm{'n; app_op; 't::'s::nil} in LambdaTerm }

(* Beta-reduction for the simple lambda-calculus *)

define unfold_mk_apply: mk_apply{'t;'s} <--> let depth=bdepth{'t} in  mk_bterm{'depth; app_op; 't::'s::nil}

define unfold_mk_lambda: mk_lambda{'f} <--> let depth=bdepth{'f} in mk_bterm{'depth -@ 1; lambda_op; 'f}

define unfold_dest_lambda_op: dest_lambda_op{'t; l,r.'var_case['l; 'r]; f.'lambda_case['f]; a,b.'apply_case['a;'b]} <-->
   dest_bterm{'t;
              l,r. 'var_case['l; 'r];
              n,op,subterms.
                 if is_same_op{lambda_op;'op}
                  then 'lambda_case[nth{'subterms;0}]
                  else 'apply_case[nth{'subterms;0};nth{'subterms;1}]
             }

interactive mk_lambda_wf  {| intro[] |} :
   sequent { <H> >- 't in LambdaTerm } -->
   sequent { <H> >- bdepth{'t} >= 1 } -->
   sequent { <H> >- mk_lambda{'t} in LambdaTerm }

interactive mk_apply_wf  {| intro[] |} :
   sequent { <H> >- 't in LambdaTerm } -->
   sequent { <H> >- 's in LambdaTerm } -->
   sequent { <H> >- bdepth{'t} = bdepth{'s} in nat } -->
   sequent { <H> >- mk_apply{'t;'s} in LambdaTerm }

define unfold_beta_redex: beta_redex{'redex;'contractum} <-->
   exst f:LambdaTerm. exst b:LambdaTerm.
    ( bdepth{'f} = bdepth{'b} in nat & bdepth{'f} >= 1 &
      ('redex = mk_apply{ mk_lambda{'f}; 'b} in LambdaTerm &
       'contractum = subst{'f;'b} in LambdaTerm))

interactive beta_redex_wf {| intro[] |}:
   sequent{ <H> >- 't in LambdaTerm } -->
   sequent{ <H> >- 's in LambdaTerm } -->
   sequent{ <H> >- beta_redex{'t;'s} Type }

(*interactive beta_redex_bterm:
   sequent{ <H> >- bterm{| <K>; x:term >- 'f['x] |} in LambdaTerm } -->
   sequent{ <H> >- bterm{| <K> >- 'b |} in LambdaTerm } -->
   sequent { <H> >- if_quoted_op{ bterm{| <K>; x:term >- 'f['x] |}; "true" } } -->
   sequent { <H> >- if_quoted_op{ bterm{| <K> >- 'b |}; "true" } } -->
   sequent{ <H> >- beta_redex{bterm{| <K> >- apply[@]{lambda[@]{x.'f['x]}; 'b} |}; bterm{| <K> >- 'f['b] |} } }
*)
define unfold_reduce1: reduce1{'t;'s} <-->
   exst f:LambdaTerm. exst redex:LambdaTerm. exst contractum:LambdaTerm.
    ('t = subst{'f;'redex} in LambdaTerm &
     's = subst{'f;'contractum} in LambdaTerm &
     beta_redex{'redex;'contractum})

interactive beta_reduce1_wf {| intro[] |}:
   sequent{ <H> >- 't in LambdaTerm } -->
   sequent{ <H> >- 's in LambdaTerm } -->
   sequent{ <H> >- reduce1{'t;'s} Type }


(* *********************** *)(*
define fun_op: fun_op <--> operator[("fun"{it;it}):op]
define unfold_mk_fun: mk_fun{'t;'s} <--> let depth=bdepth{'t} in  mk_bterm{'depth; fun_op; 't::'s::nil}
define iform typeTerm: TypeTerm <--> Lang{fun_op::nil}

dform fun_df: fun_op = `"\"fun\""
dform type_df: TypeTerm = `"Term" sub{rightarrow}

interactive lambdaterm_induction  {| elim[] |} 'H:
   sequent { <H>; x: LambdaTerm; <J['x]>; l: nat; r:nat >- 'P[var{'l;'r}] } -->
   sequent { <H>; x: LambdaTerm; <J['x]>; n: nat; t: LambdaTerm; s:LambdaTerm; bdepth{'t} = 'n in int; bdepth{'s} = 'n in nat; (*'P['t]; 'P['s]*)   >- 'P[ mk_bterm{'n; app_op; 't::'s::nil} ] } -->
   sequent { <H>; x: LambdaTerm; <J['x]>; n: nat; t: LambdaTerm; bdepth{'t} = 'n +@ 1in int; (*'P['t]*)   >- 'P[ mk_bterm{'n; lambda_op; 't::nil} ] } -->
                            'P['t] >- 'P[ make_bterm{lambda_op;bdepth{'t}-@1; 't::nil} ] } -->
   sequent { <H>; x: LambdaTerm; <J['x]> >- 'P['x] }

interactive typeterm_induction  {| elim[] |} 'H:
   sequent { <H>; x: TypeTerm; <J['x]>; l: nat; r:nat >- 'P[var{'l;'r}] } -->
   sequent { <H>; x: TypeTerm; <J['x]>; t: LambdaTerm; s:LambdaTerm; bdepth{'t} = bdepth{'s} in nat; (*'P['t]; 'P['s]*)   >- 'P[ mk_fun{'t;'s} ] } -->
   sequent { <H>; x: TypeTerm; <J['x]> >- 'P['x] }

interactive mk_fun_wf  {| intro[] |} :
   sequent { <H> >- 't in TypeTerm } -->
   sequent { <H> >- 's in TypeTerm } -->
   sequent { <H> >- bdepth{'t} = bdepth{'s} in nat } -->
   sequent { <H> >- mk_fun{'t;'s} in TypeTerm }


(* define unfold_is_type: is_type{'t;'Tv; 'T} <-->
*) declare is_type{'t;'Tv; 'T}

interactive_rw is_type_rw {| reduce |}: is_type{'t;'Tv; 'T} <-->
   dest_lambda_term{'t;
              v. 'T = nth{'Tv; right{'v}} in TypeTerm;
              f. exst A:TypeTerm. exst B:TypeTerm. (is_type{'f;'A::'Tv;'B} & 'T=mk_fun{'A;'B} in TypeTerm);
              f,a. exst A:TypeTerm. (is_type{'f;'Tv;mk_fun{'A;'T}} &  is_type{'a;'Tv;'A})}



interactive is_type_wf {| intro[] |}:
   sequent { <H> >- 't in LambdaTerm } -->
   sequent { <H> >- 'Tv in list{TypeTerm} } -->
   sequent { <H> >- 'T in TypeTerm } -->
   sequent { <H> >-  is_type{'t;'Tv;'T} Type }


interactive subject_reduction {| intro[] |} 't:
   sequent { <H> >- 't in LambdaTerm } -->
   sequent { <H> >- 'Tv in list{TypeTerm} } -->
   sequent { <H> >- 'T in TypeTerm } -->
   sequent { <H> >-  is_type{'t;'Tv;'T} } -->
   sequent { <H> >-  reduce1{'t;'s} } -->
   sequent { <H> >-  is_type{'s;'Tv;'T} }



interactive example:
sequent{ <H> >- is_type{bterm{| a:term >- apply[@]{lambda[@]{x.'x};'a} |}; bterm{|A:term >- 'A |}::nil; bterm{|A:term >- 'A |} } }
*)
