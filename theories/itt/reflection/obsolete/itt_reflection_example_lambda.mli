extends Itt_synt_lang
extends Itt_reflection_new

declare mk_apply{'t;'s}
declare mk_lambda{'t}
declare dest_lambda_term{'t; v.'var_case['v]; f.'lambda_case['f]; a,b.'apply_case['a;'b]}

declare app_term
declare lambda_term
define iform lambdaTerm: LambdaTerm <--> Lang{lambda_term::app_term::nil}
