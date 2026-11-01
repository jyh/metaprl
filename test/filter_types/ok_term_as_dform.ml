(* accepted: a Term where a Dform is taken (perv declares Dform <- Term) *)
extends Itt_logic
declare ft_h{'a : Dform} : Term
declare ft_g : Term
prim_rw unfold_ft : ft_g <--> ft_h{ft_g}
