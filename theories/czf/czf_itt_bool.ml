extends Czf_itt_set
extends Czf_itt_eq
extends Czf_itt_empty
extends Czf_itt_singleton
extends Czf_itt_setdiff
extends Czf_itt_union
extends Czf_itt_isect
extends Itt_bool
extends Itt_logic
extends Itt_theory

open Printf
open Lm_debug
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

open Dtactic
open Auto_tactic

open Itt_squash

declare boolset
declare strue
declare sfalse
declare snot{'x}
declare sand{'a; 'b}
declare sor{'a; 'b}
declare sprop{'x}
declare simplies{'a; 'b}
declare siff{'a; 'b}
declare scand{'a; 'b}
declare scor{'a; 'b}
declare sxor{'a; 'b}
declare sxand{'a; 'b}

prim_rw unfold_boolset   : boolset <--> collect{bool; x. ifthenelse{'x; sing{empty}; empty}}
prim_rw unfold_strue  : strue <--> collect{unit; x. empty}
prim_rw unfold_sfalse : sfalse <--> collect{void; x. 'x}
prim_rw unfold_snot   : snot{'x} <--> setdiff{sing{empty}; 'x}
prim_rw unfold_sor    : sor{'a; 'b} <--> "union"{'a; 'b}
prim_rw unfold_sand   : sand{'a; 'b} <--> "isect"{'a; 'b}
prim_rw unfold_sprop  : sprop{'x} <--> eq{'x; strue}
prim_rw unfold_simplies : simplies{'a; 'b} <--> sor{snot{'a}; 'b}
prim_rw unfold_siff   : siff{'a; 'b} <--> sand{simplies{'a; 'b}; simplies{'b; 'a}}
prim_rw unfold_scand  : scand{'a; 'b} <--> sand{'a; 'b}
prim_rw unfold_scor   : scor{'a; 'b} <--> sor{'a; sand{snot{'a}; 'b}}
prim_rw unfold_sxor   : sxor{'a; 'b} <--> sor{sand{'a; snot{'b}}; sand{snot{'a}; 'b}}
prim_rw unfold_sxand   : sxand{'a; 'b} <--> sor{sand{'a; 'b}; sand{snot{'a}; snot{'b}}}
(* prim_rw unfold_sxand  : sxand{'a; 'b} <--> snot{sxor{'a; 'b}} *)

let fold_boolset  = makeFoldC << boolset >> unfold_boolset
let fold_strue    = makeFoldC << strue >> unfold_strue
let fold_sfalse   = makeFoldC << sfalse >> unfold_sfalse
let fold_snot     = makeFoldC << snot{'x} >> unfold_snot
let fold_sor      = makeFoldC << sor{'a; 'b} >> unfold_sor
let fold_sand     = makeFoldC << sand{'a; 'b} >> unfold_sand
let fold_sprop    = makeFoldC << sprop{'x} >> unfold_sprop
let fold_simplies = makeFoldC << simplies{'a; 'b} >> unfold_simplies
let fold_siff     = makeFoldC << siff{'a; 'b} >> unfold_siff
let fold_scand    = makeFoldC << scand{'a; 'b} >> unfold_scand
let fold_scor     = makeFoldC << scor{'a; 'b} >> unfold_scor
let fold_sxor     = makeFoldC << sxor{'a; 'b} >> unfold_sxor
let fold_sxand    = makeFoldC << sxand{'a; 'b} >> unfold_sxand

prec prec_snot
prec prec_sand
prec prec_sxand
prec prec_sxor
prec prec_sor
prec prec_simplies
prec prec_siff
prec prec_sprop

prec prec_simplies < prec_siff
prec prec_siff  < prec_sor
prec prec_sor   < prec_sxor
prec prec_sxor  < prec_sxand
prec prec_sxand < prec_sand
prec prec_sand  < prec_snot
prec prec_snot  < prec_sprop

dform boolset_df : except_mode[src] :: boolset =
   `"boolset"

dform strue_df : except_mode[src] :: strue =
   `" True" subz

dform sfalse_df : except_mode[src] :: sfalse =
   `" False" subz

dform snot_df1 : parens :: "prec"[prec_snot] :: except_mode[src] :: snot{'x} =
   tneg subz slot["le"]{'x}

dform snot_df2 : mode[src] :: parens :: "prec"[prec_simplies] :: snot{'x} =
   `"snot " slot["le"]{'x}

dform sor_df : parens :: "prec"[prec_sor] :: except_mode[src] :: sor{'a; 'b} =
   slot["le"]{'a} " " vee subz " " slot["le"]{'b}

dform sand_df : parens :: "prec"[prec_sand] :: except_mode[src] :: sand{'a; 'b} =
   slot["le"]{'a} " " wedge subz " " slot["le"]{'b}

dform sprop_df : parens :: "prec"[prec_sprop] :: except_mode[src] :: sprop{'x} =
   downarrow subz slot{'x}

dform simplies_df : parens :: "prec"[prec_simplies] :: except_mode[src] :: simplies{'a; 'b} =
   slot["le"]{'a} " " Rightarrow subz " " slot["le"]{'b}

dform siff_df : parens :: "prec"[prec_siff] :: siff{'a; 'b} =
   slot["le"]{'a} " " Leftrightarrow subz " " slot["le"]{'b}

dform scor_df : parens :: "prec"[prec_sor] :: except_mode[src] :: scor{'a; 'b} =
   slot["le"]{'a} " " vee `"c" subz " " slot["le"]{'b}

dform scand_df : parens :: "prec"[prec_sand] :: except_mode[src] :: scand{'a; 'b} =
   slot["le"]{'a} " " wedge `"c" subz " " slot["le"]{'b}

dform sxor_df : parens :: "prec"[prec_sxor] :: except_mode[src] :: sxor{'a; 'b} =
   slot["le"]{'a} " " vee `"x" subz " " slot["le"]{'b}

dform sxand_df : parens :: "prec"[prec_sxand] :: except_mode[src] :: sxand{'a; 'b} =
   slot["le"]{'a} " " wedge `"x" subz " " slot["le"]{'b}

(*
(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let strue_term = << strue >>
let strue_opname = opname_of_term strue_term
let is_strue_term = is_no_subterms_term strue_opname

let sfalse_term = << sfalse >>
let sfalse_opname = opname_of_term sfalse_term
let is_sfalse_term = is_no_subterms_term sfalse_opname

let sor_term = << sor{'a; 'b} >>
let sor_opname = opname_of_term sor_term
let is_sor_term = is_dep0_dep0_term sor_opname
let dest_sor = dest_dep0_dep0_term sor_opname
let mk_sor_term = mk_dep0_dep0_term sor_opname

let sand_term = << sand{'a; 'b} >>
let sand_opname = opname_of_term sand_term
let is_sand_term = is_dep0_dep0_term sand_opname
let dest_sand = dest_dep0_dep0_term sand_opname
let mk_sand_term = mk_dep0_dep0_term sand_opname

let scor_term = << scor{'a; 'b} >>
let scor_opname = opname_of_term scor_term
let is_scor_term = is_dep0_dep0_term scor_opname
let dest_scor = dest_dep0_dep0_term scor_opname
let mk_scor_term = mk_dep0_dep0_term scor_opname

let scand_term = << scand{'a; 'b} >>
let scand_opname = opname_of_term scand_term
let is_scand_term = is_dep0_dep0_term scand_opname
let dest_scand = dest_dep0_dep0_term scand_opname
let mk_scand_term = mk_dep0_dep0_term scand_opname

let simplies_term = << simplies{'a; 'b}>>
let simplies_opname = opname_of_term simplies_term
let is_simplies_term = is_dep0_dep0_term simplies_opname
let dest_simplies = dest_dep0_dep0_term simplies_opname
let mk_simplies_term = mk_dep0_dep0_term simplies_opname

let siff_term = << siff{'a; 'b} >>
let siff_opname = opname_of_term siff_term
let is_siff_term = is_dep0_dep0_term siff_opname
let dest_siff = dest_dep0_dep0_term siff_opname
let mk_siff_term = mk_dep0_dep0_term siff_opname

let snot_term = << snot{'a} >>
let snot_opname = opname_of_term snot_term
let is_snot_term = is_dep0_term snot_opname
let dest_snot = dest_dep0_term snot_opname
let mk_snot_term = mk_dep0_term snot_opname

let sprop_term = << sprop{'t} >>
let sprop_opname = opname_of_term sprop_term
let mk_sprop_term = mk_dep0_term sprop_opname
let is_sprop_term = is_dep0_term sprop_opname
let dest_sprop = dest_dep0_term sprop_opname
*)

(* ************************** rules ************************* *)
interactive boolset_isset {| intro [] |} :
   sequent { <H> >- isset{boolset} }

interactive boolset_elim {| elim [] |} 'H :
   [main] sequent { <H>; x: mem{'y; boolset}; <J['x]>; w: eq{'y; strue} >- 'C['x] } -->
   [main] sequent { <H>; x: mem{'y; boolset}; <J['x]>; w: eq{'y; sfalse} >- 'C['x] } -->
   sequent { <H>; x: mem{'y; boolset}; <J['x]> >- 'C['x] }

interactive sprop_type {| intro [] |} :
   sequent { <H> >- isset{'s} } -->
   sequent { <H> >- "type"{sprop{'s}} }

interactive sprop_fun {| intro [] |} :
   sequent { <H> >- fun_prop{z.sprop{'z}} }

(* ?? *)
interactive sprop_intro 'H :
   sequent { <H>; x: eq{'s; strue} >- sprop{'s} }

(* ************************** strue ************************* *)
interactive strue_isset {| intro [] |} :
   sequent { <H> >- isset{strue} }

interactive strue_fun {| intro [] |} :
   sequent { <H> >- fun_set{z. strue} }

interactive strue_in_boolset {| intro [] |} :
   sequent { <H> >- mem{strue; boolset} }

interactive strue_intro {| intro [] |} :
   sequent { <H> >- sprop{strue} }

interactive strue_member_intro {| intro [] |} :
   ["wf"] sequent { <H> >- isset{'s} } -->
   sequent { <H> >- eq{'s; empty} } -->
   sequent { <H> >- mem{'s; strue} }

interactive strue_member_elim {| elim [] |} 'H :
   sequent { <H>; x: mem{'y; strue}; <J['x]>; w: eq{'y; empty} >- 'T['x] } -->
   sequent { <H>; x: mem{'y; strue}; <J['x]> >- 'T['x] }

(* ************************** sfalse ************************* *)
interactive sfalse_isset {| intro [] |} :
   sequent { <H> >- isset{sfalse} }

interactive sfalse_fun {| intro [] |} :
   sequent { <H> >- fun_set{z. sfalse} }

interactive sfalse_in_boolset {| intro [] |} :
   sequent { <H> >- mem{sfalse; boolset} }

interactive sfalse_elim {| elim [] |} 'H :
   sequent { <H>; x: sprop{sfalse}; <J['x]> >- 'C['x] }

interactive sfalse_member_elim {| elim [] |} 'H :
   sequent { <H>; x: mem{'y; sfalse}; <J['x]> >- 'T['x] }

interactive strue_neq_sfalse {| elim [] |} 'H :
   sequent { <H>; x: eq{strue; sfalse}; <J['x]> >- 'C['x] }

interactive sfalse_neq_strue {| elim [] |} 'H :
   sequent { <H>; x: eq{sfalse; strue}; <J['x]> >- 'C['x] }

(* ************************** snot ************************* *)
interactive snot_isset {| intro [] |} :
   sequent { <H> >- isset{'x} } -->
   sequent { <H> >- isset{snot{'x}} }

interactive snot_fun {| intro [] |} :
   sequent { <H> >- fun_set{z. 's['z]} } -->
   sequent { <H> >- fun_set{z. snot{'s['z]}} }

interactive snot_sprop {| intro [] |} :
   sequent { <H> >- fun_prop{z.sprop{snot{'z}}} }

interactive snot_strue {| intro[] |} :
   sequent { <H> >- eq{snot{strue}; sfalse} }

interactive snot_sfalse {| intro[] |} :
   sequent { <H> >- eq{snot{sfalse}; strue} }

interactive snot_in_boolset {| intro [] |} :
   ["wf"] sequent { <H> >- isset{'x} } -->
   sequent { <H> >- mem{'x; boolset} } -->
   sequent { <H> >- mem{snot{'x}; boolset} }

(* ?? *)
interactive boolset_contradiction {| elim [] |} 'H :
   ["wf"] sequent { <H>; x: sprop{'a}; y: sprop{snot{'a}}; <J> >- isset{'a} } -->
   sequent { <H>; x: sprop{'a}; y: sprop{snot{'a}}; <J> >- 'C }

interactive snot_intro {| intro [] |} :
   ["wf"] sequent { <H> >- isset{'s} } -->
   sequent { <H> >- mem{'s; boolset} } -->
   sequent { <H>; x: sprop{'s} >- "false" } -->
   sequent { <H> >- sprop{snot{'s}} }

interactive snot_elim {| elim [] |} 'H :
   ["wf"] sequent { <H>; x: sprop{snot{'s}}; <J> >- isset{'s} } -->
   sequent { <H>; x: sprop{snot{'s}}; <J> >- sprop{'s} } -->
   sequent { <H>; x: sprop{snot{'s}}; <J> >- 'C }

interactive snot_member_intro {| intro [] |} 'x :
   ["wf"] sequent { <H> >- isset{'x} } -->
   ["wf"] sequent { <H> >- isset{'s} } -->
   sequent { <H> >- mem{'x; sing{empty}}} -->
   sequent { <H>; y: mem{'x; 's} >- "false" } -->
   sequent { <H> >- mem{'x; snot{'s}} }

interactive snot_member_elim {| elim [] |} 'H :
   ["wf"] sequent { <H>; x: mem{'y; snot{'s}}; <J['x]> >- isset{'y} } -->
   ["wf"] sequent { <H>; x: mem{'y; snot{'s}}; <J['x]> >- isset{'s} } -->
   sequent { <H>; x: mem{'y; snot{'s}}; <J['x]>; u: mem{'y; sing{empty}}; v: "implies"{mem{'y; 's}; ."false"} >- 'T['x] } -->
   sequent { <H>; x: mem{'y; snot{'s}}; <J['x]> >- 'T['x] }

(* ************************** sor ************************* *)
interactive sor_isset {| intro [] |} :
   sequent { <H> >- isset{'a} } -->
   sequent { <H> >- isset{'b} } -->
   sequent { <H> >- isset{sor{'a; 'b}} }

interactive sor_fun {| intro [] |} :
   sequent { <H> >- fun_set{z. 's1['z]} } -->
   sequent { <H> >- fun_set{z. 's2['z]} } -->
   sequent { <H> >- fun_set{z. sor{'s1['z]; 's2['z]}} }

interactive sor_sprop1 {| intro [] |} :
   sequent { <H> >- isset{'s} } -->
   sequent { <H> >- fun_prop{z. sprop{sor{'z; 's}}} }

interactive sor_sprop2 {| intro [] |} :
   sequent { <H> >- isset{'s} } -->
   sequent { <H> >- fun_prop{z. sprop{sor{'s; 'z}}} }

interactive sor_in_boolset {| intro [] |} :
   sequent { <H> >- isset{'a} } -->
   sequent { <H> >- mem{'a; boolset} } -->
   sequent { <H> >- isset{'b} } -->
   sequent { <H> >- mem{'b; boolset} } -->
   sequent { <H> >- mem{sor{'a; 'b}; boolset} }

interactive sor_intro_left {| intro [SelectOption 1] |} :
   ["wf"] sequent { <H> >- isset{'s1} } -->
   ["wf"] sequent { <H> >- isset{'s2} } -->
   sequent { <H> >- mem{'s2; boolset} } -->
   sequent { <H> >- sprop{'s1} } -->
   sequent { <H> >- sprop{sor{'s1; 's2}} }

interactive sor_intro_right {| intro [SelectOption 2] |} :
   ["wf"] sequent { <H> >- isset{'s1} } -->
   ["wf"] sequent { <H> >- isset{'s2} } -->
   sequent { <H> >- mem{'s1; boolset} } -->
   sequent { <H> >- sprop{'s2} } -->
   sequent { <H> >- sprop{sor{'s1; 's2}} }

interactive sor_elim {| elim [] |} 'H :
   ["wf"] sequent { <H>; x: sprop{sor{'s1; 's2}}; <J['x]> >- isset{'s1} } -->
   ["wf"] sequent { <H>; x: sprop{sor{'s1; 's2}}; <J['x]> >- isset{'s2} } -->
   sequent { <H>; x: sprop{sor{'s1; 's2}}; <J['x]> >- mem{'s1; boolset} } -->
   sequent { <H>; x: sprop{sor{'s1; 's2}}; <J['x]> >- mem{'s2; boolset} } -->
   sequent { <H>; x: sprop{sor{'s1; 's2}}; <J['x]>; y: sprop{'s1} >- 'T['x] } -->
   sequent { <H>; x: sprop{sor{'s1; 's2}}; <J['x]>; z: sprop{'s2} >- 'T['x] } -->
   sequent { <H>; x: sprop{sor{'s1; 's2}}; <J['x]> >- 'T['x] }

interactive sor_member_intro_left {| intro [SelectOption 1] |} :
   ["wf"] sequent { <H> >- isset{'x} } -->
   ["wf"] sequent { <H> >- isset{'s1} } -->
   ["wf"] sequent { <H> >- isset{'s2} } -->
   sequent { <H> >- mem{'x; 's1} } -->
   sequent { <H> >- mem{'x; sor{'s1; 's2}} }

interactive sor_member_intro_right {| intro [SelectOption 2] |} :
   ["wf"] sequent { <H> >- isset{'x} } -->
   ["wf"] sequent { <H> >- isset{'s1} } -->
   ["wf"] sequent { <H> >- isset{'s2} } -->
   sequent { <H> >- mem{'x; 's2} } -->
   sequent { <H> >- mem{'x; sor{'s1; 's2}} }

interactive sor_member_elim {| elim [] |} 'H :
   ["wf"] sequent { <H>; x: mem{'y; sor{'s1; 's2}}; <J['x]> >- isset{'y} } -->
   ["wf"] sequent { <H>; x: mem{'y; sor{'s1; 's2}}; <J['x]> >- isset{'s1} } -->
   ["wf"] sequent { <H>; x: mem{'y; sor{'s1; 's2}}; <J['x]> >- isset{'s2} } -->
   sequent { <H>; x: mem{'y; sor{'s1; 's2}}; <J['x]>; z: mem{'y; 's1} >- 'T['x] } -->
   sequent { <H>; x: mem{'y; sor{'s1; 's2}}; <J['x]>; z: mem{'y; 's2} >- 'T['x] } -->
   sequent { <H>; x: mem{'y; sor{'s1; 's2}}; <J['x]> >- 'T['x] }

(* ************************** sand ************************* *)
interactive sand_isset {| intro [] |} :
   sequent { <H> >- isset{'a} } -->
   sequent { <H> >- isset{'b} } -->
   sequent { <H> >- isset{sand{'a; 'b}} }

interactive sand_fun {| intro [] |} :
   sequent { <H> >- fun_set{z. 's1['z]} } -->
   sequent { <H> >- fun_set{z. 's2['z]} } -->
   sequent { <H> >- fun_set{z. sand{'s1['z]; 's2['z]}} }

interactive sand_sprop1 {| intro [] |} :
   sequent { <H> >- isset{'s} } -->
   sequent { <H> >- fun_prop{z. sprop{sand{'z; 's}}} }

interactive sand_sprop2 {| intro [] |} :
   sequent { <H> >- isset{'s} } -->
   sequent { <H> >- fun_prop{z. sprop{sand{'s; 'z}}} }

interactive sand_in_boolset {| intro [] |} :
   sequent { <H> >- isset{'a} } -->
   sequent { <H> >- mem{'a; boolset} } -->
   sequent { <H> >- isset{'b} } -->
   sequent { <H> >- mem{'b; boolset} } -->
   sequent { <H> >- mem{sand{'a; 'b}; boolset} }

interactive sand_intro {| intro [] |} :
   ["wf"] sequent { <H> >- isset{'s1} } -->
   ["wf"] sequent { <H> >- isset{'s2} } -->
   sequent { <H> >- sprop{'s1} } -->
   sequent { <H> >- sprop{'s2} } -->
   sequent { <H> >- sprop{sand{'s1; 's2}} }

interactive sand_elim {| elim [] |} 'H :
   ["wf"] sequent { <H>; x: sprop{sand{'s1; 's2}}; <J['x]> >- isset{'s1} } -->
   ["wf"] sequent { <H>; x: sprop{sand{'s1; 's2}}; <J['x]> >- isset{'s2} } -->
   sequent { <H>; x: sprop{sand{'s1; 's2}}; <J['x]> >- mem{'s1; boolset} } -->
   sequent { <H>; x: sprop{sand{'s1; 's2}}; <J['x]> >- mem{'s2; boolset} } -->
   sequent { <H>; x: sprop{sand{'s1; 's2}}; <J['x]>; y: sprop{'s1}; z: sprop{'s2} >- 'T['x] } -->
   sequent { <H>; x: sprop{sand{'s1; 's2}}; <J['x]> >- 'T['x] }

interactive strue_sand_strue {| intro [] |} :
   sequent { <H> >- sprop{sand{strue; strue}} }

interactive strue_sand_sfalse {| elim [] |} 'H :
   sequent { <H>; x: sprop{sand{strue; sfalse}}; <J['x]> >- 'C['x] }

interactive sfalse_sand_strue {| elim [] |} 'H :
   sequent { <H>; x: sprop{sand{strue; sfalse}}; <J['x]> >- 'C['x] }

interactive sfalse_sand_sfalse {| elim [] |} 'H :
   sequent { <H>; x: sprop{sand{sfalse; sfalse}}; <J['x]> >- 'C['x] }

interactive sand_strue_intro1 'H :
   sequent { <H>; s: set; x: sprop{'s} >- sprop{sand{strue; 's}} }

interactive sand_strue_intro2 'H :
   sequent { <H>; s: set; x: sprop{'s} >- sprop{sand{strue; 's}} }

interactive sand_sfalse_elim1 {| elim [] |} 'H :
   ["wf"] sequent { <H>; x: sprop{sand{sfalse; 's}}; <J['x]> >- isset{'s} } -->
   sequent { <H>; x: sprop{sand{sfalse; 's}}; <J['x]> >- mem{'s; boolset} } -->
   sequent { <H>; x: sprop{sand{sfalse; 's}}; <J['x]> >- 'C['x] }

interactive sand_sfalse_elim2 {| elim [] |} 'H :
   ["wf"] sequent { <H>; x: sprop{sand{'s; sfalse}}; <J['x]> >- isset{'s} } -->
   sequent { <H>; x: sprop{sand{'s; sfalse}}; <J['x]> >- mem{'s; boolset} } -->
   sequent { <H>; x: sprop{sand{'s; sfalse}}; <J['x]> >- 'C['x] }

interactive sand_member_intro {| intro [] |} :
   ["wf"] sequent { <H> >- isset{'x} } -->
   ["wf"] sequent { <H> >- isset{'s1} } -->
   ["wf"] sequent { <H> >- isset{'s2} } -->
   sequent { <H> >- mem{'x; 's1} } -->
   sequent { <H> >- mem{'x; 's2} } -->
   sequent { <H> >- mem{'x; sand{'s1; 's2}} }

interactive sand_member_elim {| elim [] |} 'H :
   ["wf"] sequent { <H>; x: mem{'y; sand{'s1; 's2}}; <J['x]> >- isset{'y} } -->
   ["wf"] sequent { <H>; x: mem{'y; sand{'s1; 's2}}; <J['x]> >- isset{'s1} } -->
   ["wf"] sequent { <H>; x: mem{'y; sand{'s1; 's2}}; <J['x]> >- isset{'s2} } -->
   sequent { <H>; x: mem{'y; sand{'s1; 's2}}; <J['x]>; z: mem{'y; 's1} >- 'T['x] } -->
   sequent { <H>; x: mem{'y; sand{'s1; 's2}}; <J['x]>; z: mem{'y; 's2} >- 'T['x] } -->
   sequent { <H>; x: mem{'y; sand{'s1; 's2}}; <J['x]> >- 'T['x] }

(* ************************** simplies ************************* *)
interactive simplies_isset {| intro [] |} :
   sequent { <H> >- isset{'a} } -->
   sequent { <H> >- isset{'b} } -->
   sequent { <H> >- isset{simplies{'a; 'b}} }

interactive simplies_fun {| intro [] |} :
   sequent { <H> >- fun_set{z. 's1['z]} } -->
   sequent { <H> >- fun_set{z. 's2['z]} } -->
   sequent { <H> >- fun_set{z. simplies{'s1['z]; 's2['z]}} }

interactive simplies_sprop1 {| intro [] |} :
   sequent { <H> >- isset{'s} } -->
   sequent { <H> >- fun_prop{z. sprop{simplies{'s; 'z}}} }

interactive simplies_sprop2 {| intro [] |} :
   sequent { <H> >- isset{'s} } -->
   sequent { <H> >- fun_prop{z. sprop{simplies{'z; 's}}} }

interactive simplies_in_boolset {| intro [] |} :
   sequent { <H> >- isset{'a} } -->
   sequent { <H> >- isset{'b} } -->
   sequent { <H> >- mem{'a; boolset} } -->
   sequent { <H> >- mem{'b; boolset} } -->
   sequent { <H> >- mem{simplies{'a; 'b}; boolset} }

interactive simplies_intro {| intro [] |} :
   ["wf"] sequent { <H> >- isset{'s1} } -->
   ["wf"] sequent { <H> >- isset{'s2} } -->
   sequent { <H> >- mem{'s1; boolset} } -->
   sequent { <H> >- mem{'s2; boolset} } -->
   sequent { <H>; x: sprop{'s1} >- sprop{'s2} } -->
   sequent { <H> >- sprop{simplies{'s1; 's2}} }

interactive simplies_elim {| elim [] |} 'H :
   ["wf"] sequent { <H>; x: sprop{simplies{'s1; 's2}}; <J['x]> >- isset{'s1} } -->
   ["wf"] sequent { <H>; x: sprop{simplies{'s1; 's2}}; <J['x]> >- isset{'s2} } -->
   sequent { <H>; x: sprop{simplies{'s1; 's2}}; <J['x]> >- mem{'s1; boolset} } -->
   sequent { <H>; x: sprop{simplies{'s1; 's2}}; <J['x]> >- mem{'s2; boolset} } -->
   sequent { <H>; x: sprop{simplies{'s1; 's2}}; <J['x]> >- sprop{'s1} } -->
   sequent { <H>; x: sprop{simplies{'s1; 's2}}; <J['x]>; y: sprop{'s2} >- 'C['x] } -->
   sequent { <H>; x: sprop{simplies{'s1; 's2}}; <J['x]> >- 'C['x] }

(* ************************** siff ************************* *)
interactive siff_isset {| intro [] |} :
   sequent { <H> >- isset{'a} } -->
   sequent { <H> >- isset{'b} } -->
   sequent { <H> >- isset{siff{'a; 'b}} }

interactive siff_fun {| intro [] |} :
   sequent { <H> >- fun_set{z. 's1['z]} } -->
   sequent { <H> >- fun_set{z. 's2['z]} } -->
   sequent { <H> >- fun_set{z. siff{'s1['z]; 's2['z]}} }

interactive siff_sprop1 {| intro [] |} :
   sequent { <H> >- isset{'s} } -->
   sequent { <H> >- fun_prop{z. sprop{siff{'z; 's}}} }

interactive siff_sprop2 {| intro [] |} :
   sequent { <H> >- isset{'s} } -->
   sequent { <H> >- fun_prop{z. sprop{siff{'s; 'z}}} }

interactive siff_in_boolset {| intro [] |} :
   sequent { <H> >- isset{'a} } -->
   sequent { <H> >- isset{'b} } -->
   sequent { <H> >- mem{'a; boolset} } -->
   sequent { <H> >- mem{'b; boolset} } -->
   sequent { <H> >- mem{siff{'a; 'b}; boolset} }

interactive siff_intro {| intro [] |} :
   ["wf"] sequent { <H> >- isset{'s1} } -->
   ["wf"] sequent { <H> >- isset{'s2} } -->
   sequent { <H> >- mem{'s1; boolset} } -->
   sequent { <H> >- mem{'s2; boolset} } -->
   sequent { <H> >- sprop{simplies{'s1; 's2}} } -->
   sequent { <H> >- sprop{simplies{'s2; 's1}} } -->
   sequent { <H> >- sprop{siff{'s1; 's2}} }

interactive siff_elim {| elim [] |} 'H :
   ["wf"] sequent { <H>; x: sprop{siff{'s1; 's2}}; <J['x]> >- isset{'s1} } -->
   ["wf"] sequent { <H>; x: sprop{siff{'s1; 's2}}; <J['x]> >- isset{'s2} } -->
   sequent { <H>; x: sprop{siff{'s1; 's2}}; <J['x]> >- mem{'s1; boolset} } -->
   sequent { <H>; x: sprop{siff{'s1; 's2}}; <J['x]> >- mem{'s2; boolset} } -->
   sequent { <H>; x: sprop{siff{'s1; 's2}}; <J['x]>; y: sprop{simplies{'s1; 's2}}; z: sprop{simplies{'s2; 's1}} >- 'C['x] } -->
   sequent { <H>; x: sprop{siff{'s1; 's2}}; <J['x]> >- 'C['x] }

(* ************************** scand ************************* *)
interactive scand_isset {| intro [] |} :
   sequent { <H> >- isset{'a} } -->
   sequent { <H> >- isset{'b} } -->
   sequent { <H> >- isset{scand{'a; 'b}} }

interactive scand_fun {| intro [] |} :
   sequent { <H> >- fun_set{z. 's1['z]} } -->
   sequent { <H> >- fun_set{z. 's2['z]} } -->
   sequent { <H> >- fun_set{z. scand{'s1['z]; 's2['z]}} }

interactive scand_sprop1 {| intro [] |} :
   sequent { <H> >- isset{'s} } -->
   sequent { <H> >- fun_prop{z. sprop{scand{'z; 's}}} }

interactive scand_sprop2 {| intro [] |} :
   sequent { <H> >- isset{'s} } -->
   sequent { <H> >- fun_prop{z. sprop{scand{'s; 'z}}} }

interactive scand_in_boolset {| intro [] |} :
   sequent { <H> >- isset{'a} } -->
   sequent { <H> >- mem{'a; boolset} } -->
   sequent { <H> >- isset{'b} } -->
   sequent { <H> >- mem{'b; boolset} } -->
   sequent { <H> >- mem{scand{'a; 'b}; boolset} }

interactive scand_intro {| intro [] |} :
   ["wf"] sequent { <H> >- isset{'s1} } -->
   ["wf"] sequent { <H> >- isset{'s2} } -->
   sequent { <H> >- sprop{'s1} } -->
   sequent { <H>; x: sprop{'s1} >- sprop{'s2} } -->
   sequent { <H> >- sprop{scand{'s1; 's2}} }

interactive scand_elim {| elim [] |} 'H :
   ["wf"] sequent { <H>; x: sprop{scand{'s1; 's2}}; <J['x]> >- isset{'s1} } -->
   ["wf"] sequent { <H>; x: sprop{scand{'s1; 's2}}; <J['x]> >- isset{'s2} } -->
   sequent { <H>; x: sprop{scand{'s1; 's2}}; <J['x]> >- mem{'s1; boolset} } -->
   sequent { <H>; x: sprop{scand{'s1; 's2}}; <J['x]> >- mem{'s2; boolset} } -->
   sequent { <H>; x: sprop{scand{'s1; 's2}}; <J['x]>; y: sprop{'s1}; z: sprop{'s2} >- 'T['x] } -->
   sequent { <H>; x: sprop{scand{'s1; 's2}}; <J['x]> >- 'T['x] }

interactive scand_strue {| elim [] |} 'H :
   ["wf"] sequent { <H>; x: sprop{scand{strue; 's}}; <J['x]> >- isset{'s} } -->
   sequent { <H>; x: sprop{scand{strue; 's}}; <J['x]> >- mem{'s; boolset} } -->
   sequent { <H>; x: sprop{scand{strue; 's}}; <J['x]>; y: sprop{'s} >- 'C['x] } -->
   sequent { <H>; x: sprop{scand{strue; 's}}; <J['x]> >- 'C['x] }

interactive scand_sfalse1 'H 'J :
   ["wf"] sequent { <H>; x: sprop{scand{'s1; 's2}}; <J['x]> >- isset{'s1} } -->
   ["wf"] sequent { <H>; x: sprop{scand{'s1; 's2}}; <J['x]> >- isset{'s2} } -->
(*   sequent { <H>; x: sprop{scand{'s1; 's2}}; <J['x]> >- mem{'s1; boolset} } --> *)
   sequent { <H>; x: sprop{scand{'s1; 's2}}; <J['x]> >- mem{'s2; boolset} } -->
   sequent { <H>; x: sprop{scand{'s1; 's2}}; <J['x]>; y: eq{'s1; sfalse} >- 'C['x] }

interactive scand_sfalse2 {| elim [] |} 'H :
   ["wf"] sequent { <H>; x: sprop{scand{sfalse; 's}}; <J['x]> >- isset{'s} } -->
   sequent { <H>; x: sprop{scand{sfalse; 's}}; <J['x]> >- mem{'s; boolset} } -->
   sequent { <H>; x: sprop{scand{sfalse; 's}}; <J['x]> >- 'C['x] }

(* ************************** scor ************************* *)
interactive scor_isset {| intro [] |} :
   sequent { <H> >- isset{'a} } -->
   sequent { <H> >- isset{'b} } -->
   sequent { <H> >- isset{scor{'a; 'b}} }

interactive scor_fun {| intro [] |} :
   sequent { <H> >- fun_set{z. 's1['z]} } -->
   sequent { <H> >- fun_set{z. 's2['z]} } -->
   sequent { <H> >- fun_set{z. scor{'s1['z]; 's2['z]}} }

interactive scor_sprop1 {| intro [] |} :
   sequent { <H> >- isset{'s} } -->
   sequent { <H> >- fun_prop{z. sprop{scor{'z; 's}}} }

interactive scor_sprop2 {| intro [] |} :
   sequent { <H> >- isset{'s} } -->
   sequent { <H> >- fun_prop{z. sprop{scor{'s; 'z}}} }

interactive scor_in_boolset {| intro [] |} :
   sequent { <H> >- isset{'a} } -->
   sequent { <H> >- mem{'a; boolset} } -->
   sequent { <H> >- isset{'b} } -->
   sequent { <H> >- mem{'b; boolset} } -->
   sequent { <H> >- mem{scor{'a; 'b}; boolset} }

interactive scor_intro_left {| intro [SelectOption 1] |} :
   ["wf"] sequent { <H> >- isset{'s2} } -->
   ["wf"] sequent { <H> >- isset{'s1} } -->
   sequent { <H> >- mem{'s1; boolset} } -->
   sequent { <H> >- mem{'s2; boolset} } -->
   sequent { <H> >- sprop{'s1} } -->
   sequent { <H> >- sprop{scor{'s1; 's2}} }

interactive scor_intro_right {| intro [SelectOption 2] |} :
   ["wf"] sequent { <H> >- isset{'s1} } -->
   ["wf"] sequent { <H> >- isset{'s2} } -->
   sequent { <H> >- mem{'s1; boolset} } -->
   sequent { <H> >- sprop{snot{'s1}} } -->
   sequent { <H>; x: sprop{snot{'s1}} >- sprop{'s2} } -->
   sequent { <H> >- sprop{scor{'s1; 's2}} }

interactive scor_elim {| elim [] |} 'H :
   ["wf"] sequent { <H>; x: sprop{scor{'s1; 's2}}; <J['x]> >- isset{'s1} } -->
   ["wf"] sequent { <H>; x: sprop{scor{'s1; 's2}}; <J['x]> >- isset{'s2} } -->
   sequent { <H>; x: sprop{scor{'s1; 's2}}; <J['x]> >- mem{'s1; boolset} } -->
   sequent { <H>; x: sprop{scor{'s1; 's2}}; <J['x]> >- mem{'s2; boolset} } -->
   sequent { <H>; x: sprop{scor{'s1; 's2}}; <J['x]>; y: sprop{'s1} >- 'T['x] } -->
   sequent { <H>; x: sprop{scor{'s1; 's2}}; <J['x]>; y: sprop{snot{'s1}}; z: sprop{'s2} >- 'T['x] } -->
   sequent { <H>; x: sprop{scor{'s1; 's2}}; <J['x]> >- 'T['x] }

(* ************************** sxor ************************* *)
interactive sxor_isset {| intro [] |} :
   sequent { <H> >- isset{'a} } -->
   sequent { <H> >- isset{'b} } -->
   sequent { <H> >- isset{sxor{'a; 'b}} }

interactive sxor_fun {| intro [] |} :
   sequent { <H> >- fun_set{z. 's1['z]} } -->
   sequent { <H> >- fun_set{z. 's2['z]} } -->
   sequent { <H> >- fun_set{z. sxor{'s1['z]; 's2['z]}} }

interactive sxor_sprop1 {| intro [] |} :
   sequent { <H> >- isset{'s} } -->
   sequent { <H> >- fun_prop{z. sprop{sxor{'z; 's}}} }

interactive sxor_sprop2 {| intro [] |} :
   sequent { <H> >- isset{'s} } -->
   sequent { <H> >- fun_prop{z. sprop{sxor{'s; 'z}}} }

interactive sxor_in_boolset {| intro [] |} :
   sequent { <H> >- isset{'a} } -->
   sequent { <H> >- isset{'b} } -->
   sequent { <H> >- mem{'a; boolset} } -->
   sequent { <H> >- mem{'b; boolset} } -->
   sequent { <H> >- mem{sxor{'a; 'b}; boolset} }

interactive sxor_intro {| intro [] |} :
   ["wf"] sequent { <H> >- isset{'s1} } -->
   ["wf"] sequent { <H> >- isset{'s2} } -->
   sequent { <H> >- mem{'s1; boolset} } -->
   sequent { <H> >- mem{'s2; boolset} } -->
   sequent { <H>; x: sprop{'s1} >- sprop{snot{'s2}} } -->
   sequent { <H>; x: sprop{snot{'s1}} >- sprop{'s2} } -->
   sequent { <H> >- sprop{sxor{'s1; 's2}} }

interactive sxor_elim {| elim [] |} 'H :
   ["wf"] sequent { <H>; x: sprop{sxor{'s1; 's2}}; <J['x]> >- isset{'s1} } -->
   ["wf"] sequent { <H>; x: sprop{sxor{'s1; 's2}}; <J['x]> >- isset{'s2} } -->
   sequent { <H>; x: sprop{sxor{'s1; 's2}}; <J['x]> >- mem{'s1; boolset} } -->
   sequent { <H>; x: sprop{sxor{'s1; 's2}}; <J['x]> >- mem{'s2; boolset} } -->
   sequent { <H>; x: sprop{sxor{'s1; 's2}}; <J['x]>; y: sprop{'s1}; z: sprop{snot{'s2}} >- 'T['x] } -->
   sequent { <H>; x: sprop{sxor{'s1; 's2}}; <J['x]>; y: sprop{snot{'s1}}; z: sprop{'s2} >- 'T['x] } -->
   sequent { <H>; x: sprop{sxor{'s1; 's2}}; <J['x]> >- 'T['x] }

interactive sxor_hyp_assoc1 'H :
   sequent { <H>; x: sprop{sxor{'a; sxor{'b; 'c}}}; <J> >- isset{'a} } -->
   sequent { <H>; x: sprop{sxor{'a; sxor{'b; 'c}}}; <J> >- isset{'b} } -->
   sequent { <H>; x: sprop{sxor{'a; sxor{'b; 'c}}}; <J> >- isset{'c} } -->
   sequent { <H>; x: sprop{sxor{'a; sxor{'b; 'c}}}; <J> >- mem{'a; boolset} } -->
   sequent { <H>; x: sprop{sxor{'a; sxor{'b; 'c}}}; <J> >- mem{'b; boolset} } -->
   sequent { <H>; x: sprop{sxor{'a; sxor{'b; 'c}}}; <J> >- mem{'c; boolset} } -->
   [main] sequent { <H>; x: sprop{sxor{'a; sxor{'b; 'c}}}; <J>; u: sprop{sxor{sxor{'a; 'b}; 'c}} >- 'T } -->
   sequent { <H>; x: sprop{sxor{'a; sxor{'b; 'c}}}; <J> >- 'T }

interactive sxor_concl_assoc1 :
   [wf] sequent { <H> >- isset{'a} } -->
   [wf] sequent { <H> >- isset{'b} } -->
   [wf] sequent { <H> >- isset{'c} } -->
   sequent { <H> >- mem{'a; boolset} } -->
   sequent { <H> >- mem{'b; boolset} } -->
   sequent { <H> >- mem{'c; boolset} } -->
   sequent { <H> >- sprop{sxor{sxor{'a; 'b}; 'c}} } -->
   sequent { <H> >- sprop{sxor{'a; sxor{'b; 'c}}} }

let sxorHypAssoc1T = sxor_hyp_assoc1

let sxorConclAssoc1T = sxor_concl_assoc1

let sxorAssoc1T i =
   if i = 0 then
      sxorConclAssoc1T
   else
      sxorHypAssoc1T i

interactive test 'H :
   sequent { <H> >- isset{'a} } -->
   sequent { <H> >- isset{'b} } -->
   sequent { <H> >- isset{'c} } -->
   sequent { <H> >- mem{'a; boolset} } -->
   sequent { <H> >- mem{'b; boolset} } -->
   sequent { <H> >- mem{'c; boolset} } -->
   sequent { <H>; x: sprop{sxor{'a; sxor{'b; 'c}}} >- sprop{sor{sand{sxor{'a; 'b}; snot{'c}}; sand{snot{sxor{'a; 'b}}; 'c}}} }

interactive test2 'H :
   sequent { <H> >- isset{'a} } -->
   sequent { <H> >- isset{'b} } -->
   sequent { <H> >- isset{'c} } -->
   sequent { <H> >- mem{'a; boolset} } -->
   sequent { <H> >- mem{'b; boolset} } -->
   sequent { <H> >- mem{'c; boolset} } -->
   sequent { <H>; x: sprop{sxor{sxor{'a; 'b}; 'c}} >- sprop{sor{sand{'a; snot{sxor{'b; 'c}}}; sand{snot{'a}; sxor{'b; 'c}}}} }

(* ************************** sxand ************************* *)
interactive sxand_isset {| intro [] |} :
   sequent { <H> >- isset{'a} } -->
   sequent { <H> >- isset{'b} } -->
   sequent { <H> >- isset{sxand{'a; 'b}} }

interactive sxand_fun {| intro [] |} :
   sequent { <H> >- fun_set{z. 's1['z]} } -->
   sequent { <H> >- fun_set{z. 's2['z]} } -->
   sequent { <H> >- fun_set{z. sxand{'s1['z]; 's2['z]}} }

interactive sxand_sprop1 {| intro [] |} :
   sequent { <H> >- isset{'s} } -->
   sequent { <H> >- fun_prop{z. sprop{sxand{'z; 's}}} }

interactive sxand_sprop2 {| intro [] |} :
   sequent { <H> >- isset{'s} } -->
   sequent { <H> >- fun_prop{z. sprop{sxand{'s; 'z}}} }

interactive sxand_in_boolset {| intro [] |} :
   sequent { <H> >- isset{'a} } -->
   sequent { <H> >- isset{'b} } -->
   sequent { <H> >- mem{'a; boolset} } -->
   sequent { <H> >- mem{'b; boolset} } -->
   sequent { <H> >- mem{sxand{'a; 'b}; boolset} }

interactive sxand_intro {| intro [] |} :
   ["wf"] sequent { <H> >- isset{'s1} } -->
   ["wf"] sequent { <H> >- isset{'s2} } -->
   sequent { <H> >- mem{'s1; boolset} } -->
   sequent { <H> >- mem{'s2; boolset} } -->
   sequent { <H>; x: sprop{'s1} >- sprop{'s2} } -->
   sequent { <H>; x: sprop{snot{'s1}} >- sprop{snot{'s2}} } -->
   sequent { <H> >- sprop{sxand{'s1; 's2}} }

interactive sxand_elim {| elim [] |} 'H :
   ["wf"] sequent { <H>; x: sprop{sxand{'s1; 's2}}; <J['x]> >- isset{'s1} } -->
   ["wf"] sequent { <H>; x: sprop{sxand{'s1; 's2}}; <J['x]> >- isset{'s2} } -->
   sequent { <H>; x: sprop{sxand{'s1; 's2}}; <J['x]> >- mem{'s1; boolset} } -->
   sequent { <H>; x: sprop{sxand{'s1; 's2}}; <J['x]> >- mem{'s2; boolset} } -->
   sequent { <H>; x: sprop{sxand{'s1; 's2}}; <J['x]>; y: sprop{'s1}; z: sprop{'s2} >- 'T['x] } -->
   sequent { <H>; x: sprop{sxand{'s1; 's2}}; <J['x]>; y: sprop{snot{'s1}}; z: sprop{snot{'s2}} >- 'T['x] } -->
   sequent { <H>; x: sprop{sxand{'s1; 's2}}; <J['x]> >- 'T['x] }

interactive sxand_hyp_assoc1 'H :
   sequent { <H>; x: sprop{sxand{'a; sxand{'b; 'c}}}; <J> >- isset{'a} } -->
   sequent { <H>; x: sprop{sxand{'a; sxand{'b; 'c}}}; <J> >- isset{'b} } -->
   sequent { <H>; x: sprop{sxand{'a; sxand{'b; 'c}}}; <J> >- isset{'c} } -->
   sequent { <H>; x: sprop{sxand{'a; sxand{'b; 'c}}}; <J> >- mem{'a; boolset} } -->
   sequent { <H>; x: sprop{sxand{'a; sxand{'b; 'c}}}; <J> >- mem{'b; boolset} } -->
   sequent { <H>; x: sprop{sxand{'a; sxand{'b; 'c}}}; <J> >- mem{'c; boolset} } -->
   [main] sequent { <H>; x: sprop{sxand{'a; sxand{'b; 'c}}}; <J>; u: sprop{sxand{sxand{'a; 'b}; 'c}} >- 'T } -->
   sequent { <H>; x: sprop{sxand{'a; sxand{'b; 'c}}}; <J> >- 'T }

interactive sxand_concl_assoc1 :
   [wf] sequent { <H> >- isset{'a} } -->
   [wf] sequent { <H> >- isset{'b} } -->
   [wf] sequent { <H> >- isset{'c} } -->
   sequent { <H> >- mem{'a; boolset} } -->
   sequent { <H> >- mem{'b; boolset} } -->
   sequent { <H> >- mem{'c; boolset} } -->
   sequent { <H> >- sprop{sxand{sxand{'a; 'b}; 'c}} } -->
   sequent { <H> >- sprop{sxand{'a; sxand{'b; 'c}}} }

let sxandHypAssoc1T = sxand_hyp_assoc1
let sxandConclAssoc1T = sxand_concl_assoc1

let sxandAssoc1T i =
   if i = 0 then
      sxandConclAssoc1T
   else
      sxandHypAssoc1T i

(* ************************** exercises ************************* *)
interactive test_sxandAssocTi 'H :
   sequent { <H> >- isset{'a} } -->
   sequent { <H> >- isset{'b} } -->
   sequent { <H> >- isset{'c} } -->
   sequent { <H> >- mem{'a; boolset} } -->
   sequent { <H> >- mem{'b; boolset} } -->
   sequent { <H> >- mem{'c; boolset} } -->
   sequent { <H>; x: sprop{sxand{'a; sxand{'b; 'c}}} >- sprop{sor{sand{sxand{'a; 'b}; 'c}; sand{snot{sxand{'a; 'b}}; snot{'c}}}} }

interactive test_sxandAssocT0 'H :
   sequent { <H> >- isset{'a} } -->
   sequent { <H> >- isset{'b} } -->
   sequent { <H> >- isset{'c} } -->
   sequent { <H> >- mem{'a; boolset} } -->
   sequent { <H> >- mem{'b; boolset} } -->
   sequent { <H> >- mem{'c; boolset} } -->
   sequent { <H>; x: sprop{sxand{sxand{'a; 'b}; 'c}} >- sprop{sor{sand{'a; sxand{'b; 'c}}; sand{snot{'a}; snot{sxand{'b; 'c}}}}} }

interactive morgan1 'H :
   sequent { <H> >- isset{'a} } -->
   sequent { <H> >- isset{'b} } -->
   sequent { <H> >- mem{'a; boolset} } -->
   sequent { <H> >- mem{'b; boolset} } -->
   sequent { <H>; u: sprop{sor{snot{'a}; snot{'b}}} >- sprop{snot{sand{'a; 'b}}} }

interactive test1 :
   sequent { <H> >- isset{'a} } -->
   sequent { <H> >- isset{'b} } -->
   sequent { <H> >- isset{'c} } -->
   sequent { <H> >- mem{'a; boolset} } -->
   sequent { <H> >- mem{'b; boolset} } -->
   sequent { <H> >- mem{'c; boolset} } -->
   sequent { <H> >- sprop{siff{sor{sor{sand{'a; 'b}; sand{snot{'b}; 'c}}; sand{'a; 'c}}; sor{sand{'a; 'b}; sand{snot{'b}; 'c}}}} }

interactive sxandAssoc :
   sequent { <H> >- isset{'a} } -->
   sequent { <H> >- isset{'b} } -->
   sequent { <H> >- isset{'c} } -->
   sequent { <H> >- mem{'a; boolset} } -->
   sequent { <H> >- mem{'b; boolset} } -->
   sequent { <H> >- mem{'c; boolset} } -->
   sequent { <H> >- sprop{siff{sxand{sxand{'a; 'b}; 'c}; sxand{'a; sxand{'b; 'c}}}} }

(* interactive xor_assoc :
   sequent { <H> >- isset{'a} } -->
   sequent { <H> >- isset{'b} } -->
   sequent { <H> >- isset{'c} } -->
   sequent { <H> >- mem{'a; boolset} } -->
   sequent { <H> >- mem{'b; boolset} } -->
   sequent { <H> >- mem{'c; boolset} } -->
   sequent { <H> >- sprop{siff{sxor{sxor{'a; 'b}; 'c}; sxor{'a; sxor{'b; 'c}}}} }
*)
