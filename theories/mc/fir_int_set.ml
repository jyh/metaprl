(*
 * Functional Intermediate Representation formalized in MetaPRL.
 * Brian Emre Aydemir, emre@its.caltech.edu
 *
 * Define a limited version of the int_set type in the FIR.
 *
 * Todo:
 *    - Consider some sort of parentheses for the display forms.
 *)

include Base_theory
include Itt_theory
include Fir_ty

(*************************************************************************
 * Declarations.
 *************************************************************************)

(* Intervals. *)
declare interval{ 'left; 'right }

(* The set. *)
declare int_set{ 'intervals }

(* Member test. *)
define unfold_in_interval : in_interval{ 'num; interval{'l; 'r} } <-->
   band{ le_bool{'l; 'num}; le_bool{'num; 'r} }
declare member{ 'num; 'int_set }

(* int_set representations of ftrue and ffalse. *)
define unfold_ftrueSet : ftrueSet <--> int_set{cons{interval{1; 1}; nil}}
define unfold_ffalseSet : ffalseSet <--> int_set{cons{interval{0; 0}; nil}}

(*************************************************************************
 * Display.
 *************************************************************************)

(* Intervals. *)
dform interval_df : except_mode[src] :: interval{ 'l; 'r }  =
   lzone `"[" slot{'l} `"," slot{'r} `"]" ezone

(* The set. *)
dform int_set_df : except_mode[src] :: int_set{ 'intervals } =
   pushm[0] szone slot{'intervals} ezone popm

(* Member test. *)
dform in_interval_df : except_mode[src] :: in_interval{'n; 'interval} =
   lzone slot{'n} Nuprl_font!member slot{'interval} ezone
dform member_df : except_mode[src] :: member{ 'n; 'set } =
   szone slot{'n} Nuprl_font!member slot{'set} ezone

(*************************************************************************
 * Rewrites.
 *************************************************************************)

(*
 * Member test.
 * Inductive and base case reductions.
 *)
prim_rw reduce_member_ind : member{ 'num; int_set{ cons{'i; 'el} } } <-->
   ifthenelse{ in_interval{ 'num; 'i }; btrue; member{ 'num; int_set{'el} } }
prim_rw reduce_member_base : member{ 'num; int_set{ nil } } <--> bfalse

(*************************************************************************
 * Automation.
 *************************************************************************)

let resource reduce += [
   << in_interval{ 'num; interval{'l; 'r} } >>, unfold_in_interval;
   << member{ 'num; int_set{ cons{'i; 'el} } } >>, reduce_member_ind;
   << member{ 'num; int_set{ nil } } >>, reduce_member_base;
   << ftrueSet >>, unfold_ftrueSet;
   << ffalseSet >>, unfold_ffalseSet
]
