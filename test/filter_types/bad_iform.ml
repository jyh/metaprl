(* refused: an input form whose right side passes a Dform where a Term is taken *)
extends Itt_logic
declare ft_h{'a : Term} : Term
declare ft_e : Dform
declare ft_g : Term
iform ft_i : ft_g <--> ft_h{ft_e}
