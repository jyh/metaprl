extends Base_reflection

open Basic_tactics

declare is_bterm{'bt}
declare BTerm
declare subterms{'t}
declare make_bterm{'bt; 'btl}
declare same_op{'b1; 'b2}
declare simple_bterm{'bt}
declare var_bterm{'bt}
declare subst{'bt; 't}

declare var_arity
declare subterms_arity{'bt}
declare depth

topval unfold_is_bterm : conv
topval unfold_subterms : conv
topval reduce_subterms : conv
topval unfold_make_bterm : conv
topval unfold_subst : conv
topval unfold_same_op : conv
topval unfold_simple_bterm : conv
topval unfold_var_bterm : conv

topval unfold_var_arity : conv
topval unfold_subterms_arity : conv
topval unfold_depth : conv

topval fold_var_arity : conv
topval fold_subterms_arity : conv
topval fold_depth : conv
