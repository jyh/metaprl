(*
 * Additional Boolean functions on integers.
 *)

include Itt_bool
include Itt_int
include Itt_logic

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*
 * Boolean valued predicates.
 *)
declare eq_int{'i; 'j}
declare lt_int{'i; 'j}
declare le_int{'i; 'j}
declare gt_int{'i; 'j}
declare ge_int{'i; 'j}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

rewrite reduceEQInt : eq_int{natural_number[@i:n]; natural_number[@j:n]} <--> bool_flag[@i = @j]
rewrite reduceLTInt : lt_int{natural_number[@i:n]; natural_number[@j:n]} <--> bool_flag[@i < @j]
rewrite reduceGTInt : gt_int{natural_number[@i:n]; natural_number[@j:n]} <--> bool_flag[@j < @i]
rewrite reduceLEInt : le_int{'i; 'j} <--> bor{eq_int{'i; 'j}; lt_int{'i; 'j}}
rewrite reduceGEInt : le_int{'i; 'j} <--> bor{eq_int{'i; 'j}; gt_int{'i; 'j}}

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
