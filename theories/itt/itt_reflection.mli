extends Base_reflection

open Basic_tactics

declare is_bterm{'bt}
declare BTerm
declare itbterm
declare is_var_bterm{'bt}
declare var_bterm{'bt}
declare Var
declare OpBTerm
declare subterms{'t}
declare is_same_op{'b1; 'b2}
declare same_op{'b1; 'b2}
declare is_simple_bterm{'bt}
declare simple_bterm{'bt}
declare Term
declare BBTerm
declare subst{'bt; 't}

declare var_arity{'t}
declare subterms_arity{'bt}
declare depth{'t}

declare make_bterm{'bt; 'btl}
declare are_compatible_shapes_aux{'diff; 'l1; 'l2}
declare are_compatible_shapes{'bt; 'l}
declare compatible_shapes{'bt; 'l}

topval compatible_shapes_varC : term -> conv

topval unfold_is_bterm : conv
topval unfold_itbterm : conv
topval unfold_is_var_bterm : conv
topval unfold_var_bterm : conv
topval fold_var_bterm : conv
topval unfold_var : conv
topval unfold_opbterm : conv
topval unfold_subterms : conv
topval reduce_subterms : conv
topval unfold_subst : conv
topval unfold_is_same_op : conv
topval unfold_same_op : conv
topval unfold_is_simple_bterm : conv
topval unfold_simple_bterm : conv
topval unfold_term : conv
topval unfold_bbterm : conv

topval fold_itbterm : conv

topval unfold_var_arity : conv
topval unfold_subterms_arity : conv
topval unfold_depth : conv

topval fold_var_arity : conv
topval fold_subterms_arity : conv
topval fold_depth : conv

topval unfold_make_bterm : conv
topval unfold_are_compatible_shapes_aux : conv
topval fold_are_compatible_shapes_aux : conv
topval unfold_are_compatible_shapes : conv
topval unfold_compatible_shapes : conv

topval sameOpSymT : tactic
topval sameOpTransT : term -> tactic
topval splitBTermVT : term -> int -> tactic
topval splitBTermTT : term -> int -> tactic
