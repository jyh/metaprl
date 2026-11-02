(* refused: a type rewrite whose redex passes a Term where a Ty is taken *)
extends Itt_logic
declare ft_h{'a : Term} : Term
declare ft_e : Dform
declare ft_g : Term
declare type ft_ty{'a : Ty} : Ty
 declare rewrite ft_ty{ft_g} <--> Term
