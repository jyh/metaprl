extends Itt_synt_var
extends Itt_synt_operator

declare BTerm
declare make_bterm{'op; 'subterms}
declare make_bterm{'op;'bdepth;'subterms}

declare bterm_ind{'bt; v.'var_case['v];
                       op,subterms,ind. 'op_case['op; 'subterms; 'ind] }
declare compatible_shapes{'op; 'btl}

declare bdepth{'bt}
declare dest_bterm{'bt; v.'var_case['v]; op,subterms. 'op_case['op; 'subterms] }

declare Vars_of{'bt}

declare is_var_bterm{'bt}
declare var_bterm{'bt}

declare OpBTerm
declare op_of{'t}
declare subterms{'t}
declare is_same_op{'b1; 'b2}
declare same_op{'b1; 'b2}

iform make_bterm: make_bterm{'op;'bdepth;'subterms} <--> make_bterm{inject{'op;'bdepth};'subterms}

iform dest_bterm:
   dest_bterm{'bt; v.'var_case['v];
                   op,subterms. 'op_case['op; 'subterms] }
   <--> bterm_ind{'bt; v.'var_case['v];
                       op,subterms,ind. 'op_case['op; 'subterms] }
