(* This theory is a toy example of how we are going to define a language *)

extends Itt_synt_lang
extends Itt_reflection_new
extends Itt_nequal

open Basic_tactics






define app_term : app_term <--> bterm{| >- apply[@]{term[@];term[@]} |}
define lambda_term: lambda_term <-->  bterm{| >- lambda[@]{x.term[@]} |}

dform app_df: app_term = `"\"apply\""
dform lsmbda_df: lambda_term = `"\"" lambda "\""




interactive app_wf {| intro[] |}:
   sequent{ <H> >-  app_term in BOperator }

interactive lambda_wf {| intro[] |}:
   sequent{ <H> >-  lambda_term in BOperator }

interactive_rw shape_of_app {| reduce |}: shape{app_term} <--> (0::0::nil)

interactive_rw shape_of_lam {| reduce |}: shape{lambda_term} <--> (1::nil)

interactive_rw depth_of_app {| reduce |}: op_bdepth{app_term} <--> 0

interactive_rw depth_of_lam {| reduce |}: op_bdepth{lambda_term} <--> 0

interactive lambda_app_diffops {| intro[] |}:
   sequent{ <H> >- app_term <> lambda_term in Operator }

interactive lambda_app_diffops2 {| intro[] |}:
   sequent{ <H> >- lambda_term::app_term::nil in diff_list{Operator} }

define iform lambdaTerm: LambdaTerm <--> Lang{lambda_term::app_term::nil}
dform lambda_df: LambdaTerm = `"Term" sub{lambda}

interactive lambda_term_induction  {| elim[] |} 'H:
   sequent { <H>; <J>; v:Var >- 'P[ 'v ] } -->
   sequent { <H>; <J>; t: LambdaTerm; s:LambdaTerm; bdepth{'t} = bdepth{'s} in nat;
                            'P['t]; 'P['s]   >- 'P[ make_bterm{app_term;bdepth{'t}; 't::'s::nil} ] } -->
   sequent { <H>; <J>; t: LambdaTerm; bdepth{'t} >= 1;
                            'P['t] >- 'P[ make_bterm{lambda_term;bdepth{'t}-@1; 't::nil} ] } -->
   sequent { <H>; x: LambdaTerm; <J> >- 'P['x] }

interactive lambda_intro  {| intro[] |} :
   sequent { <H> >- 't in LambdaTerm } -->
   sequent { <H> >- bdepth {'t} >= 1  } -->
   sequent { <H> >- make_bterm{lambda_term; bdepth{'t}-@1; 't::nil} in LambdaTerm }

interactive lambda_intro2  {| intro[] |} :
   sequent { <H> >- bterm{| <K<||> >; x:term >- 't<|K|>['x] |} in LambdaTerm } -->
   sequent { <H> >- if_quoted_op{ bterm{| <K<||> >; x:term >- 't<|K|>['x] |}; "true" } } -->
   sequent { <H> >- bterm{| <K<||> > >- lambda[@]{x.'t<|K|>['x]} |} in LambdaTerm }

interactive app_intro  {| intro[] |} :
   sequent { <H> >- 't in LambdaTerm } -->
   sequent { <H> >- 's in LambdaTerm } -->
   sequent { <H> >- bdepth {'t} = bdepth {'s} in int  } -->
   sequent { <H> >- make_bterm{app_term; bdepth{'t}; 't::'s::nil} in LambdaTerm }

interactive app_intro2  {| intro[] |} :
   sequent { <H> >- bterm{| <K<||> > >- 't<|K|> |} in LambdaTerm } -->
   sequent { <H> >- bterm{| <K<||> > >- 's<|K|> |} in LambdaTerm } -->
   sequent { <H> >- if_quoted_op{ bterm{| <K<||> > >- 't<|K|> |}; "true" } } -->
   sequent { <H> >- if_quoted_op{ bterm{| <K<||> > >- 's<|K|> |}; "true" } } -->
   sequent { <H> >- bterm{| <K<||> > >- apply[@]{'t<|K|>;'s<|K|>} |} in LambdaTerm }


define unfold_mk_apply: mk_apply{'t;'s} <--> let depth=max{bdepth{'t};bdepth{'s}} in  make_bterm{app_term; 'depth; make_depth{'t;'depth}::make_depth{'s;'depth}::nil}

define unfold_mk_lambda: mk_lambda{'f} <--> let depth=max{bdepth{'f}; 1} in  make_bterm{lambda_term; 'depth -@ 1; make_depth{'f;'depth}::nil}

interactive add_var_lambdaterm {| intro[] |} :
   sequent { <H> >- 's in LambdaTerm } -->
   sequent { <H> >- 'v in Var } -->
   sequent { <H> >- add_var{'s; 'v} in LambdaTerm }

interactive add_new_var_lambdaterm {| intro[] |} :
   sequent { <H> >- 's in LambdaTerm } -->
   sequent { <H> >- add_var{'s} in LambdaTerm }

interactive make_depth_lambdaterm {| intro[] |} :
   sequent { <H> >- 's in LambdaTerm } -->
   sequent { <H> >- 'n in nat } -->
   sequent { <H> >- 'n >= bdepth{'s} } -->
   sequent { <H> >- make_depth{'s;'n} in LambdaTerm }

interactive add_vars_upto_lambdaterm {| intro [] |} :
   sequent { <H> >- 't in LambdaTerm } -->
   sequent { <H> >- 's in LambdaTerm } -->
   sequent { <H> >- bdepth{'t} >= bdepth{'s} } -->
   sequent { <H> >- add_vars_upto{'s;'t} in LambdaTerm }

interactive subst_lambdaterm {| intro [] |} :
   sequent { <H> >- 't in LambdaTerm } -->
   sequent { <H> >- 'v in Vars_of{'t} } -->
   sequent { <H> >- 's in LambdaTerm } -->
   sequent { <H> >- bdepth{'t} >= bdepth{'s} } -->
   sequent { <H> >- subst{'t;'v;'s} in LambdaTerm }

interactive mk_lambda_wf  {| intro[] |} :
   sequent { <H> >- 't in LambdaTerm } -->
   sequent { <H> >- mk_lambda{'t} in LambdaTerm }

interactive mk_apply_wf  {| intro[] |} :
   sequent { <H> >- 't in LambdaTerm } -->
   sequent { <H> >- 's in LambdaTerm } -->
   sequent { <H> >- mk_apply{'t;'s} in LambdaTerm }


define unfold_dest_lambda_term: dest_lambda_term{'t; v.'var_case['v]; f.'lambda_case['f]; a,b.'apply_case['a;'b]} <-->
   dest_bterm{'t;
              v. 'var_case['v];
              op,subterms.
                 if is_same_op{lambda_term;'op}
                  then 'lambda_case[nth{'subterms;0}]
                  else 'apply_case[nth{'subterms;0};nth{'subterms;1}]
             }
