open Basic_tactics

declare is_bterm{'bt}
declare bterm
declare subterms{'t}
declare make_bterm{'bt; 'btl}
declare same_op{'b1; 'b2}
declare simple_bterm{'bt}
declare var_bterm{'bt}

declare arity{'bt}

topval unfold_is_bterm : conv
topval unfold_subterms : conv
topval reduce_subterms : conv
topval unfold_make_bterm : conv
topval unfold_same_op : conv
topval unfold_simple_bterm : conv
topval unfold_var_bterm : conv

topval unfold_arity : conv