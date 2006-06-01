extends Itt_hoas_lang

declare app_op
declare lambda_op
define iform lambdaTerm: LambdaTerm <--> Lang{SubOp{lambda_op::app_op::nil}}

declare mk_apply{'t;'s}
declare mk_lambda{'t}
declare dest_lambda_term{'t; v.'var_case['v]; l,r.'var_case['l; 'r]; a,b.'apply_case['a;'b]}

declare beta_redex{'redex;'contractum}
declare reduce1{'t;'s}
