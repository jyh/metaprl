
extends Itt_record
extends Itt_algebra_df
extends Itt_srec
extends Itt_bisect
extends Itt_struct

(*! @docoff *)

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

open Base_auto_tactic

open Itt_record
open Itt_bisect
open Itt_srec
open Itt_union
open Itt_struct



declare Node{'T}


declare BinTree


declare emptytree

declare tree{'node}

declare tree_ind{'tree; 'empty; L,R,node. 'f['L;'R;'node]}

declare match_tree{'t; 'empty_case; self.'nonempty_case['self]}
declare leftSubtree{'t}
declare   rightSubtree{'t}
declare weight{'t}
declare  node{'l;'r;'nd}
declare Node{'T;'A}
declare Node{'T;l,r.'R['l;'r]}
declare BinTree{l,r.'R['l;'r]}
declare  BinTree{'R}
declare BinTree{'A; t.'P['t]}

declare simpletree

val match_tree : conv
val leftSubtree : conv
val rightSubtree : conv







