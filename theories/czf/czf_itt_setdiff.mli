extends Czf_itt_set
extends Czf_itt_member
extends Czf_itt_empty
extends Czf_itt_nat
extends Czf_itt_sep
extends Itt_bool

open Refiner.Refiner.RefineError
open Refiner.Refiner.Term

open Tactic_type.Sequent
open Tactic_type.Conversionals
open Tactic_type.Tacticals
open Var

open Dtactic
open Auto_tactic

open Itt_rfun
open Itt_logic

declare setdiff{'s1; 's2}

rewrite unfold_setdiff : setdiff{'s1; 's2} <-->
   sep{'s1; x. "implies"{mem{'x; 's2}; ."false"}}
(*   set_ind{'s1; T1, f1, g1.
         collect{'T1; x. ifthenelse{mem{.'f1 'x; 's2}; empty; .'f1 'x}}} *)

topval fold_setdiff : conv
