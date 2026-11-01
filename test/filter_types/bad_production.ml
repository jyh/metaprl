(* refused: a production whose result passes a Dform where a Term is taken *)
extends Itt_logic
declare ft_h{'a : Term} : Term
declare ft_e : Dform
declare ft_g : Term
declare ft_tok : Terminal
declare ft_nt{'a : Term} : Nonterminal
production ft_nt{ft_e} <-- ft_tok
