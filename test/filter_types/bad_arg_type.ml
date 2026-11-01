(* refused: a Dform where the operator takes a Term *)
extends Itt_logic
declare ft_h{'a : Term} : Term
declare ft_e : Dform
declare ft_g : Term
prim_rw unfold_ft : ft_g <--> ft_h{ft_e}
