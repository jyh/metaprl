include Czf_itt_group
include Czf_itt_equiv

open Printf
open Mp_debug
open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermAddr
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.Refine
open Refiner.Refiner.RefineError
open Mp_resource
open Simple_print

open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Sequent
open Tactic_type.Conversionals
open Mptop
open Var

open Base_dtactic
open Base_auto_tactic

(* Build a group h from group g. The underlying set of h is s;
 * the operation and equivalence relation in h are the same as
 * in g.
 *)
declare group_bvd{'h; 'g; 's}

rewrite unfold_group_bvd : group_bvd{'h; 'g; 's} <-->
   (group{'h} & group{'g} & isset{'s} & equal{car{'h}; 's} & (all a: set. all b: set. (mem{'a; car{'h}} => mem{'b; car{'h}} => equiv{car{'h}; eqG{'h}; op{'h; 'a; 'b}; op{'g; 'a; 'b}})) & (all a: set. all b: set. (equiv{car{'h}; eqG{'h}; 'a; 'b} => equiv{car{'g}; eqG{'g}; 'a; 'b})) & (all a: set. all b: set. (mem{'a; car{'h}} => mem{'b; car{'h}} => equiv{car{'g}; eqG{'g}; 'a; 'b} => equiv{car{'h}; eqG{'h}; 'a; 'b})))
