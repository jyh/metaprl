(*
 * Functional Intermediate Representation formalized in MetaPRL.
 * Brian Emre Aydemir, emre@its.caltech.edu
 *
 * Define a limited version of the int_set type in the FIR.
 *)

include Base_theory
include Itt_theory

(*************************************************************************
 * Declarations.
 *************************************************************************)

(* Intervals. *)
declare interval{ 'left; 'right }

(* The set. *)
declare int_set{ 'intervals }

(* Short form. *)
declare int_set{ 'a; 'b }

(* Member test. *)
define unfold_in_interval : in_interval{ 'num; interval{'l; 'r} } <-->
   band{ le_bool{'l; 'num}; le_bool{'num; 'r} }
declare member{ 'num; 'int_set }

(*************************************************************************
 * Display.
 *************************************************************************)

(* Intervals. *)
dform interval_df : except_mode[src] :: interval{ 'l; 'r }  =
   lzone `"[" slot{'l} `"," slot{'r} `"]" ezone

(* The set. *)
dform int_set_df1 : except_mode[src] :: int_set{ 'intervals } =
   pushm[0] szone slot{'intervals} ezone popm

(* Short form. *)
dform int_set_df2 : except_mode[src] :: int_set{ 'a; 'b } =
   `"[[" slot{'a} `", " slot{'b} `"]]"

(* Member test. *)
dform in_interval_df : except_mode[src] :: in_interval{'num; 'interval} =
   lzone slot{'num} `" " Nuprl_font!member `" " slot{'interval} ezone
dform member_df : except_mode[src] :: member{ 'num; 'set } =
   szone slot{'num} space Nuprl_font!member space slot{'set} ezone

(*************************************************************************
 * Rewrites.
 *************************************************************************)

prim_rw reduce_member_cons : member{ 'num; int_set{ cons{'i; 'el} } } <-->
   ifthenelse{ in_interval{ 'num; 'i }; btrue; member{ 'num; int_set{'el} } }
prim_rw reduce_member_nil : member{ 'num; int_set{ nil } } <--> bfalse
prim_rw reduce_short_int_set :
   int_set{ 'a; 'b } <-->
   int_set{ cons{ interval{'a; 'b}; nil } }

(*************************************************************************
 * Automation.
 *************************************************************************)

let resource reduce += [
   << in_interval{ 'num; interval{'l; 'r} } >>, unfold_in_interval;
   << member{ 'num; int_set{ cons{'i; 'el} } } >>, reduce_member_cons;
   << member{ 'num; int_set{ nil } } >>, reduce_member_nil;
   << int_set{ 'a; 'b } >>, reduce_short_int_set
]
