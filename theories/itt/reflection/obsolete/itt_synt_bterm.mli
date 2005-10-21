extends Itt_synt_var
extends Itt_synt_operator

open Basic_tactics

declare BTerm

declare make_bterm{'op; 'subterms}

declare bterm_ind{'bt; v.'var_case['v];
                       op,subterms,ind. 'op_case['op; 'subterms; 'ind] }
declare compatible_shapes{'op; 'btl}

declare bdepth{'bt}

declare Vars_of{'bt}

declare is_var_bterm{'bt}
declare var_bterm{'bt}

declare OpBTerm
declare op_of{'t}
declare subterms{'t}
declare is_same_op_of{'b1; 'b2}
declare same_op_of{'b1; 'b2}

define iform bterm: BTerm{'n} <--> { bt:BTerm | bdepth{'bt} = 'n in nat }
define iform bterm_plus: BTerm_plus{'n} <--> { bt:BTerm | bdepth{'bt} >= 'n }

define iform make_bterm: make_bterm{'op;'bdepth;'subterms} <--> make_bterm{inject{'op;'bdepth};'subterms}

define iform dest_bterm:
   dest_bterm{'bt; v.'var_case['v];
                   op,subterms. 'op_case['op; 'subterms] }
   <--> bterm_ind{'bt; v.'var_case['v];
                       op,subterms,ind. 'op_case['op; 'subterms] }

topval sameOpOfSymT : tactic
topval sameOpOfTransT : term -> tactic
