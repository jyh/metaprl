(* This theory is a toy example of how we are going to define a language *)

extends Itt_synt_language
extends Itt_reflection_new

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


declare LambdaTerm
iform lambdaTerm: LambdaTerm <--> Languge{lambda_term::app_term::nil}
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
   sequent { <H> >- bterm{| <K>; x:term >- 't['x] |} in LambdaTerm } -->
   sequent { <H> >- bterm{| <K> >- lambda[@]{x.'t['x]} |} in LambdaTerm }



