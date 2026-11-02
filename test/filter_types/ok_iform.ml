(* accepted: an input form between well-typed terms *)
extends Itt_logic
declare ft_h{'a : Term} : Term
declare ft_e : Dform
declare ft_g : Term
iform ft_i : ft_g <--> ft_h{ft_g}
