(*
 * Functional Intermediate Representation formalized in MetaPRL.
 * Brian Emre Aydemir, emre@its.caltech.edu
 *
 * Define and implement the basic expression forms in the FIR.
 *)

include Base_theory
include Itt_theory
include Fir_state
include Fir_int_set
include Fir_ty

(*************************************************************************
 * Declarations.
 *************************************************************************)

(* Identity (polymorphic). *)
declare idOp

(* Pointer equality. *)
declare eqEqOp
declare neqEqOp

(* Subscript operators. *)
declare blockPolySub
declare rawDataSub
declare rawFunctionSub

(* Allocation operators. *)
declare allocTuple{ 'ty; 'atom_list }
declare allocArray{ 'ty; 'atom_list }
declare allocUnion{ 'ty; 'ty_var; 'num; 'atom_list }
declare allocMalloc{ 'atom }

(* Normal values. *)
declare atomInt{ 'int }
declare atomEnum{ 'bound; 'num }
declare atomConst{ 'ty; 'ty_var; 'num }
declare atomVar{ 'var }

(*
 * Expressions.
 *)

(* Primitive operations. *)
declare unop_exp{ 'op; 'a1 }
declare binop_exp{ 'op; 'a1; 'a2 }
declare letUnop{ 'state; 'op; 'ty; 'a1; s, v. 'exp['s; 'v] }
declare letBinop{ 'state; 'op; 'ty; 'a1; 'a2; s, v. 'exp['s; 'v] }

(* Function application. *)
declare letExt{ 'ty; 'string; 'ty_str; 'atom_list; v. 'exp['v] }
declare tailCall{ 'var; 'atom_list }

(* Control. *)
declare matchCase{ 'set; s. 'exp['s] }
declare match_int{ 'state; 'key; 'cases }
declare match_block{ 'state; 'key; 'cases }

(* Allocation. *)
declare letAlloc{ 'state; 'alloc_op; s, v. 'exp['s; 'v] }

(* Subscripting. *)
declare letSubscript{ 'state; 'subop; 'ty; 'ref; 'index; s, v. 'exp['s; 'v] }
declare setSubscript{ 'state; 'subop; 'ty; 'ref; 'index;
                      'new_val; s. 'exp['s] }

(*************************************************************************
 * Display forms.
 *************************************************************************)

(* Identity (polymorphic). *)
dform idOp_df : except_mode[src] :: idOp = `"id"

(* Pointer equality. *)
dform eqEqOp_df : except_mode[src] :: eqEqOp = `"EqEqOp"
dform neqEqOp_df : except_mode[src] :: neqEqOp = `"NeqEqOp"

(* Subscript operators. *)
dform blockPolySub_df : except_mode[src] :: blockPolySub =
   `"BlockPolySub"
dform rawDataSub_df : except_mode[src] :: rawDataSub =
   `"RawDataSub"
dform rawFunctionSub : except_mode[src] :: rawFunctionSub =
   `"RawFunctionSub"

(* Allocation operators. *)
dform allocTuple_df : except_mode[src] :: allocTuple{ 'ty; 'atom_list } =
   szone `"AllocTuple(" slot{'ty} `", " slot{'atom_list} `")" ezone
dform allocArray_df : except_mode[src] :: allocArray{ 'ty; 'atom_list } =
   szone `"AllocArray(" slot{'ty} `", " slot{'atom_list} `")" ezone
dform allocUnion_df : except_mode[src] ::
   allocUnion{ 'ty; 'ty_var; 'num; 'atom_list } =
   szone `"AllocUnion(" slot{'ty} `", " slot{'ty_var} `", "
   slot{'num} `", " slot{'atom_list } `")" ezone
dform allocMalloc_df : except_mode[src] :: allocMalloc{ 'atom } =
   `"AllocMalloc(" slot{'atom} `")"

(* Normal values. *)
dform atomInt_df : except_mode[src] :: atomInt{ 'int } =
   lzone `"AtomInt(" slot{'int} `")" ezone
dform atomEnum_df : except_mode[src] :: atomEnum{ 'bound; 'num } =
   lzone `"AtomEnum(" slot{'bound} `", " slot{'num} `")" ezone
dform atomConst_df : except_mode[src] :: atomConst{ 'ty; 'ty_var; 'num } =
   lzone `"AtomConst(" slot{'ty} `", " slot{'ty_var} `", "
   slot{'num} `")" ezone
dform atomVar_df : except_mode[src] :: atomVar{ 'var } =
   szone `"AtomVar(" slot{'var} `")" ezone

(*
 * Expressions.
 *)

(* Primitive operations. *)
dform unop_exp_df : except_mode[src] :: unop_exp{ 'op; 'a1 } =
   slot{'op} `"(" slot{'a1} `")"
dform binop_exp_df : except_mode[src] :: binop_exp{ 'op; 'a1; 'a2 } =
   `"(" slot{'a1} `" " slot{'op} `" " slot{'a2} `")"
dform letUnop_df : except_mode[src] ::
   letUnop{ 'state; 'op; 'ty; 'a1; s, v. 'exp } =
   pushm[0] szone push_indent `"let " slot{'v} `":" slot{'ty} `" =" hspace
   lzone slot{'op} `"(" slot{'a1} `")" ezone popm hspace
   `"with state " slot{'state} hspace
   push_indent `"in" hspace
   szone slot{'exp} ezone popm
   ezone popm
dform letBinop_df : except_mode[src] ::
   letBinop{ 'state; 'op; 'ty; 'a1; 'a2; s, v. 'exp } =
   pushm[0] szone push_indent `"let " slot{'v} `":" slot{'ty} `" =" hspace
   lzone `"(" slot{'a1} `" " slot{'op} `" " slot{'a2} `")" ezone popm hspace
   `"with state " slot{'state} hspace
   push_indent `"in" hspace
   szone slot{'exp} ezone popm
   ezone popm

(* Function application. *)
dform letExt_df : except_mode[src] ::
   letExt{ 'ty; 'string; 'ty_str; 'atom_list; v. 'exp } =
   pushm[0] szone push_indent `"let " slot{'v} `":" slot{'ty} `" =" hspace
   szone slot{'string} `":" slot{'ty_str} `"(" slot{'atom_list} `")" ezone popm
   ezone popm
dform tailCall_df : except_mode[src] :: tailCall{ 'var; 'atom_list } =
   szone `"TailCall(" slot{'var} `", " slot{'atom_list} `")" ezone

(* Control. *)
dform matchCase_df : except_mode[src] :: matchCase{ 'set; s. 'exp } =
   pushm[0] szone push_indent slot{'set} `" ->" hspace
   szone slot{'exp} ezone popm
   ezone popm
dform match_int_df : except_mode[src] :: match_int{ 'state; 'a; 'cases } =
   pushm[0] szone push_indent `"match" hspace
   szone slot{'a} ezone popm hspace
   push_indent `"with state" hspace
   szone slot{'state} ezone popm hspace
   push_indent `"in" hspace
   szone slot{'cases} ezone popm
   ezone popm
dform match_block_df : except_mode[src] :: match_block{ 'state; 'a; 'cases } =
   pushm[0] szone push_indent `"match" hspace
   szone slot{'a} ezone popm hspace
   push_indent `"with state" hspace
   szone slot{'state} ezone popm hspace
   push_indent `"in" hspace
   szone slot{'cases} ezone popm
   ezone popm

(* Allocation *)
dform letAlloc_df : except_mode[src] ::
   letAlloc{ 'state; 'alloc_op; s, v. 'exp } =
   pushm[0] szone push_indent `"let " slot{'v} `" =" hspace
   lzone slot{'alloc_op} ezone popm hspace
   `"with state " slot{'state} hspace
   push_indent `"in" hspace
   szone slot{'exp} ezone popm
   ezone popm

(* Subscripting. *)
dform letSubscript_df : except_mode[src] ::
   letSubscript{ 'state; 'subop; 'ty; 'ref; 'index; s, v. 'exp } =
   pushm[0] szone push_indent `"let " slot{'v} `":" slot{'ty} `" =" hspace
   lzone slot{'ref} `"[" slot{'index} `"]" ezone popm hspace
   `"with subop " slot{'subop} hspace
   `"with state " slot{'state} hspace
   push_indent `"in" hspace
   szone slot{'exp} ezone popm
   ezone popm
dform setSubscript_df : except_mode[src] ::
   setSubscript{ 'state; 'subop; 'ty; 'ref; 'index; 'new_val; s. 'exp } =
   szone slot{'ref} `"[" slot{'index} `"]" Nuprl_font!leftarrow
   slot{'new_val} hspace
   `"with subop " slot{'subop} hspace
   `"with state " slot{'state} `";" hspace
   slot{'exp} ezone

(*************************************************************************
 * Rewrites.
 *************************************************************************)

(* Identity (polymorphic). *)
prim_rw reduce_idOp : unop_exp{ idOp; 'a1 } <--> 'a1

(* Pointer equality. *)
prim_rw reduce_eqEqOp : binop_exp{ eqEqOp; 'a1; 'a2 } <-->
   ifthenelse{ beq_int{'a1; 'a2}; val_true; val_false }
prim_rw reduce_neqEqOp : binop_exp{ neqEqOp; 'a1; 'a2 } <-->
   ifthenelse{ beq_int{'a1; 'a2}; val_false; val_true }

(* Normal values. *)
prim_rw reduce_atomInt : atomInt{ 'num } <--> 'num
prim_rw reduce_atomEnum : atomEnum{ 'bound; 'num } <--> 'num
prim_rw reduce_atomVar : atomVar{ 'var } <--> 'var

(* Primitive operations. *)
prim_rw reduce_letUnop :
   letUnop{ 'state; 'op; 'ty; 'a1; s, v. 'exp['s; 'v] } <-->
   'exp[ 'state; unop_exp{ 'op; 'a1 } ]
prim_rw reduce_letBinop :
   letBinop{ 'state; 'op; 'ty; 'a1; 'a2; s, v. 'exp['s; 'v] } <-->
   'exp[ 'state; binop_exp{ 'op; 'a1; 'a2 } ]

(* Function application. *)
prim_rw reduce_letExt :
   letExt{ 'ty; 'string; 'ty_str; 'atom_list; v. 'exp } <-->
   'exp

(* Control. *)
prim_rw reduce_match_int :
   match_int{ 'state; 'key; cons{ matchCase{'set; s. 'e['s] }; 'el } } <-->
   ifthenelse{ member{ 'key; 'set };
      'e['state];
      match_int{ 'state; 'key; 'el } }
prim_rw reduce_match_block :
   match_block{ 'state; block{'i; 'args}; 'cases } <-->
   match_int{ 'state; 'i; 'cases }

(* Allocation. *)
prim_rw reduce_allocTuple :
   letAlloc{ 'state; allocTuple{ 'ty; 'atom_list }; s, v. 'exp['s; 'v] } <-->
   smatch{ alloc{ 'state; 0; 'atom_list }; s, v. 'exp['s; 'v] }
prim_rw reduce_allocArray :
   letAlloc{ 'state; allocArray{ 'ty; 'atom_list }; s, v. 'exp['s; 'v] } <-->
   smatch{ alloc{ 'state; 0; 'atom_list }; s, v. 'exp['s; 'v] }
prim_rw reduce_allocUnion :
   letAlloc{ 'state; allocUnion{ 'ty; 'ty_var; 'num; 'atom_list };
      s, v. 'exp['s; 'v] } <-->
   smatch{ alloc{ 'state; 'num; 'atom_list }; s, v. 'exp['s; 'v] }

(* Subscripting. *)
prim_rw reduce_letSubscript :
   letSubscript{ 'state; 'subop; 'ty; 'ref; 'index; s, v. 'exp['s; 'v] } <-->
   smatch{ fetch{ 'state; 'ref; 'index }; s, v. 'exp['s; 'v] }
prim_rw reduce_setSubscript :
   setSubscript{ 'state; 'subop; 'ty; 'ref; 'index;
      'new_val; s. 'exp['s] } <-->
   smatch{ store{ 'state; 'ref; 'index; 'new_val }; s, v. 'exp['s] }

(*************************************************************************
 * Automation.
 *************************************************************************)

let resource reduce += [
   << unop_exp{ idOp; 'a1 } >>, reduce_idOp;
   << binop_exp{ eqEqOp; 'a1; 'a2 } >>, reduce_eqEqOp;
   << binop_exp{ neqEqOp; 'a1; 'a2 } >>, reduce_neqEqOp;
   << atomInt{ 'num } >>, reduce_atomInt;
   << atomEnum{ 'bound; 'num } >>, reduce_atomEnum;
   << atomVar{ 'var } >>, reduce_atomVar;
   << letUnop{ 'state; 'op; 'ty; 'a1; s, v. 'exp['s; 'v] } >>,
      reduce_letUnop;
   << letBinop{ 'state; 'op; 'ty; 'a1; 'a2; s, v. 'exp['s; 'v] } >>,
      reduce_letBinop;
   << letExt{ 'ty; 'string; 'ty_str; 'atom_list; v. 'exp } >>,
      reduce_letExt;
   << match_int{ 'state; 'key; cons{ matchCase{'set; s. 'e['s] }; 'el } } >>,
      reduce_match_int;
   << match_block{ 'state; block{'i; 'args}; 'cases } >>, reduce_match_block;
   << letAlloc{ 'state; allocTuple{ 'ty; 'atom_list }; s, v. 'exp['s; 'v] } >>,
      reduce_allocTuple;
   << letAlloc{ 'state; allocArray{ 'ty; 'atom_list }; s, v. 'exp['s; 'v] } >>,
      reduce_allocArray;
   << letAlloc{ 'state; allocUnion{ 'ty; 'ty_var; 'num; 'atom_list };
         s, v. 'exp['s; 'v] } >>,
      reduce_allocUnion;
   << letSubscript{ 'state; 'subop; 'ty; 'ref; 'index; s, v. 'exp['s; 'v] } >>,
      reduce_letSubscript;
   << setSubscript{ 'state; 'subop; 'ty; 'ref; 'index;
      'new_val; s. 'exp['s] } >>,
      reduce_setSubscript
]
