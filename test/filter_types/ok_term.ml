(* accepted: a term-typed operator applied to a term *)
extends Itt_logic
declare ft_f{'a : Term} : Term
declare ft_g : Term
prim_rw unfold_ft : ft_g <--> ft_f{ft_g}
