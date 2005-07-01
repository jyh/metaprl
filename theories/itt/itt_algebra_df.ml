doc <:doc<
   @begin[doc]
   @module[Itt_algebra_df]

   This theory does not contain any mathematical object.
   It defines only display forms for the most common algebraic operations.
   @end[doc]
>>

extends Itt_record
extends Itt_labels

doc docoff

(** carrier **)

dform car_df : except_mode[src] :: ('g^car)
 = `"|"'g`"|"

(** relations **)

(* < *)

dform less1_df : parens :: except_mode[src] :: ('a <['ord] 'b)
 = 'a  tt[" <"]sub{'ord} `" " 'b

dform less2_df : parens :: except_mode[src] :: ('a <[self{'self}] 'b)
 = 'a  tt[" <"] `" " 'b

dform less3_df : parens :: except_mode[src] :: (label["<":t] 'a 'b)
 = 'a  tt[" < "] 'b

(* = *)

dform eq1_df : parens :: except_mode[src] :: ('a =['ord] 'b)
 = 'a  tt[" ="]sub{'ord} `" " 'b

dform eq2_df : parens :: except_mode[src] :: ('a =[self{'self}] 'b)
 = 'a  tt[" ="] `" " 'b

dform eq3_df : parens :: except_mode[src] :: (label["=":t] 'a 'b)
 = 'a  tt[" = "] 'b
