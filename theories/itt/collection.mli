include Itt_theory
open Itt_equal

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
open Tacticals
open Conversionals
open Sequent

topval substT : term -> int -> tactic
topval hypSubstT : int -> int -> tactic
topval revHypSubstT : int -> int -> tactic


topval unhideT : int -> tactic
topval reverseT : tactic
topval  cutMemberT:  term -> tactic
topval  cutMember1T :  term -> tactic
topval useAssumptionT : int -> tactic
topval memberTypeT : term -> tactic
topval autoRT : tactic
topval univTypeT : term -> tactic
topval  equalRefComplT : term -> tactic

topval mem_col_memT : term -> tactic
      
topval d_colT : int -> tactic
topval cutColT : term -> tactic
topval cutColS : term -> tactic
      
topval fold_Col : conv
   
topval member_ColT : tactic





















