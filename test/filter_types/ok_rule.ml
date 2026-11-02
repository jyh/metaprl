(* accepted: a rule whose goal is well typed *)
extends Itt_logic
declare ft_h{'a : Term} : Term
declare ft_e : Dform
declare ft_g : Term
interactive ft_rule :
   sequent { <H> >- ft_h{ft_g} }
