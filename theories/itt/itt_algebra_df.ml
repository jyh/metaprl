doc <:doc< 
   @begin[doc]
   @module[Itt_algebra_df]
  
   This theory does not contain any mathematical object.
   It defines only display forms for the most common algebraic operations.
   @end[doc]
>>

extends Itt_record

doc <:doc< @docoff >>

open Printf
open Mp_debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError
open Mp_resource

open Var
open Tactic_type
open Tactic_type.Tacticals
open Base_dtactic
open Tactic_type.Conversionals
open Top_conversionals

open Itt_record


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


