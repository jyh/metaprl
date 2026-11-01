(* refused: a rule whose goal passes a Dform where a Term is taken *)
extends Itt_logic
declare ft_h{'a : Term} : Term
declare ft_e : Dform
declare ft_g : Term
interactive ft_rule :
   sequent { <H> >- ft_h{ft_e} }
