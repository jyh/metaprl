(*
 * Functional Intermediate Representation formalized in MetaPRL.
 * Brian Emre Aydemir, emre@its.caltech.edu
 *
 * Define the type system for the FIR.
 * See fir_ty.mli for a description of the terms below.
 *)

include Base_theory
include Itt_theory

open Tactic_type.Conversionals

(*************************************************************************
 * Declarations.
 *************************************************************************)

(* Integer type. *)
declare tyInt

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
define unfold_eq_fbool : eq_fbool{ block{'a1; nil}; block{'a2; nil} } <-->
   beq_int{ 'a1; 'a2 }

(* Integer atom. *)
declare atomInt{ 'int }

(* Variable atom. *)
declare atomVar{ 'var; 'ty }

(*************************************************************************
 * Display forms.
 *************************************************************************)

(* Integer type. *)
dform tyInt_df : tyInt = `"TyInt"

(* Function type. *)
dform tyFun_df : tyFun{ 'ty_list; 'ty } =
   szone `"TyFun" slot{'ty_list} `"->" slot{'ty} ezone

(* Union type. *)
dform normalUnion_df : normalUnion = `"NormalUnion"
dform exnUnion_df : exnUnion = `"ExnUnion"
dform unionElt_df : unionElt{ 'ty; 'bool } =
   lzone `"(" slot{'ty} `" * " slot{'bool} ")" ezone
dform tyUnion_df : tyUnion{ 'union_ty; 'elts } =
   szone `"(TyUnion of " slot{'union_ty} `" * " slot{'elts} `")" ezone

(* Array type. *)
dform tyArray_df : tyArray{ 'ty } =
   lzone `"(TyArray of " slot{'ty} `")" ezone

(* Subscripting. *)
dform tySubscript_df : tySubscript{ 't1; 't2 } =
   lzone `"(TySubscript of " slot{'t1} `" * " slot{'t2} `")" ezone

(* Blocks / memory. *)
dform block_df : block{ 'tag; 'args } =
   lzone `"block{" slot{'tag} `"; " slot{'args} `"}" ezone

(* Boolean type. *)
dform tyBool_df : tyBool = `"TyBool"
dform ftrue_df : ftrue = `"fTrue"
dform ffalse_df : ffalse = `"fFalse"
dform eq_fbool_df : eq_fbool{ 'a1; 'a2 } =
   lzone `"(" slot{'a1} `"=" slot{'a2} `")" ezone

(* Integer atom. *)
dform atomInt_df : atomInt{ 'int } =
   lzone `"(AtomInt of " slot{'int} `")" ezone

(* Variable atom. *)
dform atomVar_df : atomVar{ 'var; 'ty } =
   lzone `"(AtomVar of " slot{'var} `", " slot{'ty} `")" ezone

(*************************************************************************
 * Automation.
 *************************************************************************)

let resource reduce +=
   [<< tyBool >>, unfold_tyBool;
    << ftrue >>,  unfold_ftrue;
    << ffalse >>, unfold_ffalse;
    << eq_fbool{ block{'a1; nil}; block{'a2; nil} } >>, unfold_eq_fbool]
