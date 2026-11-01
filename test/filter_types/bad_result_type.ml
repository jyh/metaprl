(* refused: a Dform-typed term where a Term is required *)
extends Itt_logic
declare ft_f{'a : Dform} : Dform
declare ft_g : Term
prim_rw unfold_ft : ft_g <--> ft_f{ft_g}
