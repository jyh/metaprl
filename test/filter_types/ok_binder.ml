(* accepted: a binder whose bound variable is a Term, used as a Term *)
extends Itt_logic
declare ft_b{x : Term. 'e : Term} : Term
declare ft_f{'a : Term} : Term
declare ft_g : Term
prim_rw unfold_ft : ft_g <--> ft_b{x. ft_f{'x}}
