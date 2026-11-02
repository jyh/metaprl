(* accepted: a production whose terms are well typed *)
extends Itt_logic
declare ft_h{'a : Term} : Term
declare ft_e : Dform
declare ft_g : Term
declare ft_tok : Terminal
declare ft_nt{'a : Term} : Nonterminal
production ft_nt{ft_g} <-- ft_tok
