(*
 * Additional Boolean functions on integers.
 *)

include Itt_bool
include Itt_int
include Itt_logic

open Itt_logic

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

primrw reduceEQInt : eq_int{natural_number[@i:n]; natural_number[@j:n]} <--> bool_flag[@i = @j]
primrw reduceLTInt : lt_int{natural_number[@i:n]; natural_number[@j:n]} <--> bool_flag[@i < @j]
primrw reduceGTInt : gt_int{natural_number[@i:n]; natural_number[@j:n]} <--> bool_flag[@j < @i]
primrw reduceLEInt : le_int{'i; 'j} <--> bor{eq_int{'i; 'j}; lt_int{'i; 'j}}
primrw reduceGEInt : le_int{'i; 'j} <--> bor{eq_int{'i; 'j}; gt_int{'i; 'j}}

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform eq_int_df : mode[prl] :: parens :: "prec"[prec_implies] :: eq_int{'i; 'j} =
   slot{'i} " " `"=" " " slot{'j}

dform lt_int_df : mode[prl] :: parens :: "prec"[prec_implies] :: lt_int{'i; 'j} =
   slot{'i} " " `"<" " " slot{'j}

dform le_int_df : mode[prl] :: parens :: "prec"[prec_implies] :: le_int{'i; 'j} =
   slot{'i} " " Nuprl_font!le " " slot{'j}

dform gt_int_df : mode[prl] :: parens :: "prec"[prec_implies] :: gt_int{'i; 'j} =
   slot{'i} " " `">" " " slot{'j}

dform ge_int_df : mode[prl] :: parens :: "prec"[prec_implies] :: ge_int{'i; 'j} =
   slot{'i} " " Nuprl_font!ge " " slot{'j}

(*
 * $Log$
 * Revision 1.1  1998/06/12 18:36:40  jyh
 * Working factorial proof.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
