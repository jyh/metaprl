include Czf_itt_hom

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

declare iso{'g1; 'g2; x. 'f['x]}

(*
 * An isomorphism f: G1 -> G2 is a homomorphism that is
 * one-to-one and onto G2. That is, An isomorphism
 * f: G1 -> G2 is a homomorphism where f is a bijection.
 *)
rewrite unfold_iso : iso{'g1; 'g2; x. 'f['x]} <-->
   (hom{'g1; 'g2; x. 'f['x]} & (all c: set. all d: set. (mem{'c; car{'g1}} => mem{'d; car{'g1}} => equiv{car{'g2}; eqG{'g2}; 'f['c]; 'f['d]} => equiv{car{'g1}; eqG{'g1}; 'c; 'd})) & (all e: set. (mem{'e; car{'g2}} => (exst p: set. (mem{'p; car{'g1}} & equiv{car{'g2}; eqG{'g2}; 'e; 'f['p]})))))
