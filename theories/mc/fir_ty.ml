(*
 * Functional Intermediate Representation formalized in MetaPRL.
 * Brian Emre Aydemir, emre@its.caltech.edu
 *
 * Define the type system in the FIR.
 * See fir_ty.mli for a description of the terms below.
 *
 * Todo:
 *    - use the MetaPRL mechanisms for parentheses instead of just
 *      hard coding them in the display forms.
 *)

include Base_theory
include Itt_theory

open Tactic_type.Conversionals

(*************************************************************************
 * Declarations.
 *************************************************************************)

(*
 * Types.
 *)

(* Integer type. *)
declare tyInt

(* Enumeration type. *)
declare tyEnum{ 'num }

(* Function type. *)
declare tyFun{ 'ty_list; 'ty }

(* Union type. *)
declare normalUnion
declare exnUnion
declare unionElt{ 'ty; 'bool }
declare tyUnion{ 'union_ty; 'elts }

(* Array type. *)
declare tyArray{ 'ty }

(* Subscripting. *)
declare tySubscript{ 't1; 't2 }

(* Blocks / memory. *)
declare block{ 'tag; 'args }

(* Boolean type. *)
define unfold_tyBool : tyBool <-->
   tyUnion{ normalUnion; cons{ nil; cons{ nil; nil } } }
define unfold_ftrue : ftrue <--> block{ 1; nil }
define unfold_ffalse : ffalse <--> block{ 0; nil }

(*
 * Normal values.
 *)

(* Integer atom. *)
declare atomInt{ 'int }

(* Variable atom. *)
declare atomVar{ 'var }

(*************************************************************************
 * Display forms.
 *************************************************************************)

(* Integer type. *)
dform tyInt_df : except_mode[src] :: tyInt = `"TyInt"

(* Enumeration type. *)
dform tyEnum_df : except_mode[src] :: tyEnum{ 'num } =
   lzone `"TyEnum(0.." slot{'num} `")" ezone

(* Function type. *)
dform tyFun_df : except_mode[src] :: tyFun{ 'ty_list; 'ty } =
   szone `"TyFun" slot{'ty_list} `"->" slot{'ty} ezone

(* Union type. *)
dform normalUnion_df : except_mode[src] :: normalUnion = `"NormalUnion"
dform exnUnion_df : except_mode[src] :: exnUnion = `"ExnUnion"
dform unionElt_df : except_mode[src] :: unionElt{ 'ty; 'bool } =
   lzone `"(" slot{'ty} `" * " slot{'bool} ")" ezone
dform tyUnion_df : except_mode[src] :: tyUnion{ 'union_ty; 'elts } =
   szone `"(TyUnion of " slot{'union_ty} `" * " slot{'elts} `")" ezone

(* Array type. *)
dform tyArray_df : except_mode[src] :: tyArray{ 'ty } =
   lzone `"(TyArray of " slot{'ty} `")" ezone

(* Subscripting. *)
dform tySubscript_df : except_mode[src] :: tySubscript{ 't1; 't2 } =
   lzone `"(TySubscript of " slot{'t1} `" * " slot{'t2} `")" ezone

(* Blocks / memory. *)
dform block_df : except_mode[src] :: block{ 'tag; 'args } =
   lzone `"block{" slot{'tag} `"; " slot{'args} `"}" ezone

(* Boolean type. *)
dform tyBool_df : except_mode[src] :: tyBool = `"TyBool"
dform ftrue_df : except_mode[src] :: ftrue = `"fTrue"
dform ffalse_df : except_mode[src] :: ffalse = `"fFalse"

(* Integer atom. *)
dform atomInt_df : except_mode[src] :: atomInt{ 'int } =
   lzone `"(AtomInt of " slot{'int} `")" ezone

(* Variable atom. *)
dform atomVar_df : except_mode[src] :: atomVar{ 'var } =
   lzone `"(AtomVar of " slot{'var} `")" ezone

(*************************************************************************
 * Rewrites.
 *************************************************************************)

prim_rw reduce_atomInt : atomInt{ 'num } <--> 'num

(*************************************************************************
 * Automation.
 *************************************************************************)

let resource reduce += [
   << tyBool >>, unfold_tyBool;
   << ftrue >>,  unfold_ftrue;
   << ffalse >>, unfold_ffalse;
   << atomInt{ 'num } >>, reduce_atomInt;
]
