(*
 * Functional Intermediate Representation formalized in MetaPRL.
 * Brian Emre Aydemir, emre@its.caltech.edu
 *
 * Define the type system in the FIR.
 *)

include Base_theory
include Itt_theory
include Fir_int_set

(*************************************************************************
 * Declarations.
 *************************************************************************)

(* Integer type. *)
declare tyInt

(* Enumeration type. *)
declare tyEnum{ 'num }

(* Function type. *)
declare tyFun{ 'ty_list; 'ty }

(* Tuples. *)
declare tyUnion{ 'union_ty; 'ty_list; 'int_opt }
declare tyTuple{ 'ty_list }
declare tyArray{ 'ty }

(* Polymorphism. *)
declare tyVar{ 'ty_var }
declare tyApply{ 'ty_var; 'ty_list }
declare tyExists{ 'ty_var_list; 'ty }
declare tyAll{ 'ty_var_list; 'ty }
declare tyProject{ 'ty_var; 'num }

(* Subscripting. *)
declare tySubscript{ 'ty1; 'ty2 }

(* Delayed type. *)
declare tyDelayed

(* Union tags. *)
declare normalUnion
declare exnUnion

(* Defining types. *)
declare unionElt{ 'ty; 'bool }
declare tyDefUnion{ 'ty_var_list; 'union_ty; 'elts }
declare tyDefLambda{ 'ty_var_list; 'ty }

(* Boolean type. *)
define unfold_true_set : true_set <--> int_set{ 1; 1 }
define unfold_false_set : false_set <--> int_set{ 0; 0 }
define unfold_val_true : val_true <--> 1
define unfold_val_false : val_false <--> 0

define unfold_tyBool : tyBool <-->
   tyUnion{ normalUnion; cons{ nil; cons{ nil; nil } }; int_set{ nil } }
define unfold_tyBool2 : tyBool2 <--> tyEnum{ 2 }
define unfold_tyTrue : tyTrue <-->
   tyUnion{ normalUnion; cons{ nil; cons{ nil; nil } }; true_set }
define unfold_tyFalse : tyFalse <-->
   tyUnion{ normalUnion; cons{ nil; cons{ nil; nil } }; false_set }

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

(* Tuples. *)
dform tyUnion_df : except_mode[src] ::
   tyUnion{ 'union_ty; 'ty_list; 'int_opt } =
   szone `"TyUnion(" slot{'union_ty} `", " slot{'ty_list}
   `", " slot{'int_opt} `")" ezone
dform tyTuple_df : except_mode[src] :: tyTuple{ 'ty_list } =
   lzone `"TyTuple" slot{'ty_list} ezone
dform tyArray_df : except_mode[src] :: tyArray{ 'ty } =
   lzone `"TyArray(" slot{'ty} `")" ezone

(* Subscripting. *)
dform tySubscript_df : except_mode[src] :: tySubscript{ 'ty1; 'ty2 } =
   lzone `"TySubscript(" slot{'ty1} `", " slot{'ty2} `")" ezone

(* Delayed type. *)
dform tyDelayed_df : except_mode[src] :: tyDelayed = `"TyDelayed"

(* Union tags. *)
dform normalUnion_df : except_mode[src] :: normalUnion = `"NormalUnion"
dform exnUnion_df : except_mode[src] :: exnUnion = `"ExnUnion"

(* Defining types. *)
dform unionElt_df : except_mode[src] :: unionElt{ 'ty; 'bool } =
   lzone `"(" slot{'ty} `" * " slot{'bool} ")" ezone
dform tyDefUnion_df : except_mode[src] ::
   tyDefUnion{ 'ty_var_list; 'union_ty; 'elts } =
   szone `"TyDefUnion(" slot{'ty_var_list} `", " slot{'union_ty}
   `", " slot{'elts} `")" ezone
dform tyDefLambda_df : except_mode[src] :: tyDefLambda{ 'ty_var_list; 'ty } =
   szone `"TyDefLambda(" slot{'ty_var_list} `", " slot{'ty} `")" ezone

(* Boolean type *)
dform true_set_df : except_mode[src] :: true_set = `"true_set"
dform false_set_df : except_mode[src] :: false_set = `"false_set"
dform val_true_df : except_mode[src] :: val_true = `"val_true"
dform val_false_df : except_mode[src] :: val_false = `"val_false"

dform tyBool_df : except_mode[src] :: tyBool = `"TyBool(Union)"
dform tyBool2_df : except_mode[src] :: tyBool2 = `"TyBool(Enum)"
dform tyTrue_df : except_mode[src] :: tyTrue = `"TyTrue"
dform tyFalse_df : except_mode[src] :: tyFalse = `"TyFalse"

(*************************************************************************
 * Automation.
 *************************************************************************)

let resource reduce += [
   << true_set >>, unfold_true_set;
   << false_set >>, unfold_false_set;
   << val_true >>, unfold_val_true;
   << val_false >>, unfold_val_false;
   << tyBool >>, unfold_tyBool;
   << tyBool2 >>, unfold_tyBool2;
   << tyTrue >>, unfold_tyTrue;
   << tyFalse >>, unfold_tyFalse;
]
