(*
 * Functional Intermediate Representation formalized in MetaPRL.
 * Brian Emre Aydemir, emre@its.caltech.edu
 *
 * Define the type system in the FIR.
 *)

include Base_theory
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
declare tyUnion{ 'ty_var; 'ty_list; 'int_set }
declare tyTuple{ 'ty_list }
declare tyArray{ 'ty }
declare tyRawData

(* Polymorphism. *)
declare tyVar{ 'ty_var }
declare tyApply{ 'ty_var; 'ty_list }
declare tyExists{ 'ty_var_list; 'ty }
declare tyAll{ 'ty_var_list; 'ty }
declare tyProject{ 'ty_var; 'num }

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

(* Functions. *)
declare lambda{ x. 'f['x] }
declare apply{ 'f; 'x }
declare fix{ f. 'b['f] }

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
   szone `"TyFun" `"(" slot{'ty_list} `" -> " slot{'ty} `")" ezone

(* Tuples. *)
dform tyUnion_df : except_mode[src] ::
   tyUnion{ 'ty_var; 'ty_list; 'int_set } =
   szone `"TyUnion(" slot{'ty_var} `", " slot{'ty_list}
   `", " slot{'int_set} `")" ezone
dform tyTuple_df : except_mode[src] :: tyTuple{ 'ty_list } =
   lzone `"TyTuple(" slot{'ty_list} `")" ezone
dform tyArray_df : except_mode[src] :: tyArray{ 'ty } =
   lzone `"TyArray(" slot{'ty} `")" ezone
dform tyRawData : except_mode[src] :: tyRawData =
   `"TyRawData"

(* Polymorphism. *)
dform tyVar_df : except_mode[src] :: tyVar{ 'ty_var } =
   `"TyVar(" slot{'ty_var} `")"
dform tyApply_df : except_mode[src] :: tyApply{ 'ty_var; 'ty_list } =
   `"TyApply(" slot{'ty_var} `", " slot{'ty_list} `")"
dform tyExists_df : except_mode[src] :: tyExists{ 'ty_var_list; 'ty } =
   `"TyExists(" slot{'ty_var_list} `", " slot{'ty} `")"
dform tyAll_df : except_mode[src] :: tyAll{ 'ty_var_list; 'ty } =
   `"TyAll(" slot{'ty_var_list} `", " slot{'ty} `")"
dform tyProject_df : except_mode[src] :: tyProject{ 'ty_var; 'num } =
   `"TyProject(" slot{'ty_var} `", " slot{'num} `")"

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

(* Functions. *)
dform lambda_df : except_mode[src] :: lambda{ x. 'f } =
   `"(" Nuprl_font!lambda slot{'x} `"." slot{'f} `")"
dform apply_df : except_mode[src] :: apply{ 'f; 'x } =
   `"(" slot{'f} `" " slot{'x} `")"
dform fix_df : except_mode[src] :: fix{ f. 'b } =
   pushm[0] szone push_indent `"(fix " slot{'f} `"." hspace
   szone slot{'b} `")" ezone popm
   ezone popm

(*************************************************************************
 * Rewrites.
 *************************************************************************)

prim_rw reduce_tyVar : tyVar{ 'ty_var } <--> 'ty_var

prim_rw beta_reduce : apply{ lambda{ x. 'f['x] }; 'y } <--> 'f['y]
prim_rw reduce_fix : fix{ f. 'b['f] } <--> 'b[ fix{ f. 'b['f] } ]

(*************************************************************************
 * Automation.
 *************************************************************************)

let resource reduce += [
   << true_set >>, unfold_true_set;
   << false_set >>, unfold_false_set;
   << val_true >>, unfold_val_true;
   << val_false >>, unfold_val_false;
   << tyVar{ 'ty_var } >>, reduce_tyVar;
   << apply{ lambda{ x. 'f['x] }; 'y } >>, beta_reduce;
   << fix{ f. 'b['f] } >>, reduce_fix
]
