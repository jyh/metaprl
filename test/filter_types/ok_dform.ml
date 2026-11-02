(* accepted: a display form for a well-typed term *)
extends Itt_logic
declare ft_h{'a : Term} : Term
declare ft_e : Dform
declare ft_g : Term
dform ft_h_df : ft_h{'a} =
   `"ft_h" 'a
