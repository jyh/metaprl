extends Itt_synt_var
extends Itt_synt_operator

declare BTerm
declare make_bterm{'op; 'subterms}
declare bterm_ind{'bt; v.'var_case['v];
                       op,subterms,ind. 'op_case['op; 'subterms; 'ind] }
declare compatible_shapes{'op; 'btl}

declare bdepth{'bt}
declare dest_bterm{'bt; v.'var_case['v]; op,subterms. 'op_case['op; 'subterms] }

declare Vars_of{'bt}

declare is_var_bterm{'bt}
declare var_bterm{'bt}
