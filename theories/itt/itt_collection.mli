extends Itt_bool
extends Itt_esquash
extends Itt_quotient
extends Itt_logic

open Basic_tactics

topval colEqSymT : tactic
topval colEqTransT : term -> tactic

topval fold_col : conv
topval fold_col_member : conv
topval fold_Col : conv
topval fold_add : conv
