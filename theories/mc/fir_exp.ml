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

(* Program. *)
declare prog{ 'state; 'exp }

(* Program value. *)
declare value{ 'v }

(* Identity (polymorphic). *)
declare idOp

(* Allocation operators. *)
declare allocTuple{ 'ty; 'atom_list }
declare allocArray{ 'ty; 'atom_list }
declare allocUnion{ 'ty; 'ty_var; 'num; 'atom_list }
define unfold_copy : copy{ 'len; 'init } <-->
   ind{'len; i, j. nil; nil; i, j. cons{'init; 'j}}

(*
 * Normal values.
 *)

(* Subscript ops. *)
declare rawSubscript
declare intSubscript

(* Normal atoms. *)
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
declare letUnop{ 'op; 'ty; 'a1; v. 'exp['v] }
declare letBinop{ 'op; 'ty; 'a1; 'a2; v. 'exp['v] }

(* Function application. *)
declare tailCall{ 'var; 'atom_list }

(* Control. *)
declare matchCase{ 'set; 'exp }
declare "match"{ 'key; 'cases }

(* Allocation. *)
declare letAlloc{ 'alloc_op; v. 'exp['v] }

(* Subscripting. *)
declare letSubscript{ 'ref; 'index; v. 'exp['v] }
declare setSubscript{ 'ref; 'index; 'new_val; 'exp }

(*************************************************************************
 * Display forms.
 *************************************************************************)

(* Program. *)
dform prog_df : except_mode[src] :: prog{ 'state; 'exp } =
   `"prog(" slot{'state} `", " slot{'exp} `")"

(* Program value. *)
dform value_df : except_mode[src] :: value{ 'v } =
   `"value(" slot{'v} `")"

(* Identity (polymorphic). *)
dform idOp_df : except_mode[src] :: idOp = `"id"

(* Allocation operators. *)
dform allocTuple_df : except_mode[src] :: allocTuple{ 'ty; 'atom_list } =
   szone `"AllocTuple(" slot{'ty} `", " slot{'atom_list} `")" ezone
dform allocArray_df : except_mode[src] :: allocArray{ 'ty; 'atom_list } =
   szone `"AllocArray(" slot{'ty} `", " slot{'atom_list} `")" ezone
dform allocUnion_df : except_mode[src] ::
   allocUnion{ 'ty; 'ty_var; 'num; 'atom_list } =
   szone `"AllocUnion(" slot{'ty} `", " slot{'ty_var} `", "
   slot{'num} `", " slot{'atom_list } `")" ezone
dform copy_df : except_mode[src] :: copy{ 'len; 'init} =
   lzone `"copy(" slot{'len} `", " slot{'init} `")" ezone

(*
 * Normal values.
 *)

(* Subscript ops. *)
dform rawSubscript_df : except_mode[src] :: rawSubscript = `"RawSubscript"
dform intSubscript_df : except_mode[src] :: intSubscript = `"IntSubscript"

(* Normal atoms. *)
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
   letUnop{ 'op; 'ty; 'a1; v. 'exp } =
   pushm[0] szone push_indent `"let " slot{'v} `":" slot{'ty} `" =" hspace
   lzone slot{'op} `"(" slot{'a1} `")" ezone popm hspace
   push_indent `"in" hspace
   szone slot{'exp} ezone popm
   ezone popm
dform letBinop_df : except_mode[src] ::
   letBinop{ 'op; 'ty; 'a1; 'a2; v. 'exp } =
   pushm[0] szone push_indent `"let " slot{'v} `":" slot{'ty} `" =" hspace
   lzone `"(" slot{'a1} `" " slot{'op} `" " slot{'a2} `")" ezone popm hspace
   push_indent `"in" hspace
   szone slot{'exp} ezone popm
   ezone popm

(* Function application. *)
dform tailCall_df : except_mode[src] :: tailCall{ 'var; 'atom_list } =
   szone `"TailCall(" slot{'var} `", " slot{'atom_list} `")" ezone

(* Control. *)
dform matchCase_df : except_mode[src] :: matchCase{ 'set; 'exp } =
   pushm[0] szone push_indent slot{'set} `" ->" hspace
   szone slot{'exp} ezone popm
   ezone popm
dform match_df : except_mode[src] :: "match"{'a; 'cases } =
   pushm[0] szone push_indent `"match" hspace
   szone slot{'a} ezone popm hspace
   push_indent `"in" hspace
   szone slot{'cases} ezone popm
   ezone popm

(* Allocation *)
dform letAlloc_df : except_mode[src] :: letAlloc{ 'alloc_op; v. 'exp } =
   pushm[0] szone push_indent `"let " slot{'v} `" =" hspace
   lzone slot{'alloc_op} ezone popm hspace
   push_indent `"in" hspace
   szone slot{'exp} ezone popm
   ezone popm

(* Subscripting. *)
dform letSubscript_df : except_mode[src] ::
   letSubscript{ 'ref; 'index; v. 'exp } =
   pushm[0] szone push_indent `"let " slot{'v} `" =" hspace
   lzone slot{'ref} `"[" slot{'index} `"]" ezone popm hspace
   push_indent `"in" hspace
   szone slot{'exp} ezone popm
   ezone popm
dform setSubscript_df : except_mode[src] ::
   setSubscript{ 'ref; 'index; 'new_val; 'exp } =
   szone slot{'ref} `"[" slot{'index} `"]" Nuprl_font!leftarrow
   slot{'new_val} `";" hspace slot{'exp} ezone

(*************************************************************************
 * Rewrites.
 *************************************************************************)

(* Program value. *)
prim_rw reduce_value : prog{ 's; value{ 'v } } <--> 'v

(* Identity (polymorphic). *)
prim_rw reduce_idOp : unop_exp{ idOp; 'a1 } <--> 'a1

(* Integer atom. *)
prim_rw reduce_atomInt : atomInt{ 'num } <--> 'num

(* Enumeration atom. *)
prim_rw reduce_atomEnum : atomEnum{ 'bound; 'num } <--> 'num

(* Primitive operations. *)
prim_rw reduce_letUnop :
   letUnop{ 'op; 'ty; 'a1; v. 'exp['v] } <-->
   'exp[ unop_exp{ 'op; 'a1 } ]
prim_rw reduce_letBinop :
   letBinop{ 'op; 'ty; 'a1; 'a2; v. 'exp['v] } <-->
   'exp[ binop_exp{ 'op; 'a1; 'a2 } ]

(* Allocation. *)
prim_rw reduce_allocTuple :
   prog{ 'state; letAlloc{ allocTuple{ 'ty; 'atom_list }; v. 'exp['v] } } <-->
   smatch{ alloc{ 'state; 0; 'atom_list }; s2, v2.
      prog{ 's2; 'exp['v2] } }
prim_rw reduce_allocArray :
   prog{ 'state; letAlloc{ allocArray{ 'ty; 'atom_list }; v. 'exp['v] } } <-->
   smatch{ alloc{ 'state; 0; 'atom_list }; s2, v2.
      prog{ 's2; 'exp['v2] } }

(* Control *)
prim_rw reduce_match_num :
   "match"{ number[i:n]; cons{matchCase{'set; 'exp}; 'el} } <-->
   ifthenelse{ member{number[i:n]; 'set}; 'exp; ."match"{number[i:n]; 'el} }
prim_rw reduce_match_block :
   "match"{ block{ 'i; 'args }; cons{matchCase{'set; 'exp}; 'el} } <-->
   ifthenelse{ member{'i; 'set}; 'exp; ."match"{block{'i; 'args}; 'el} }

(* Subscripting. *)
prim_rw reduce_letSubscript :
   prog{ 'state; letSubscript{ 'ref; 'index; v. 'exp['v] } } <-->
   smatch{ fetch{ 'state; 'ref; 'index }; s2, v2.
      prog{ 's2; 'exp['v2] } }
prim_rw reduce_setSubscript :
   prog{ 'state; setSubscript{ 'ref; 'index; 'new_val; 'exp } } <-->
   smatch{ store{ 'state; 'ref; 'index; 'new_val }; s2, v2.
      prog{ 's2; 'exp } }

(*************************************************************************
 * Automation.
 *************************************************************************)

let resource reduce += [
   <<  prog{ 's; value{ 'v } } >>, reduce_value;
   << unop_exp{ idOp; 'a1 } >>, reduce_idOp;
   << letUnop{ 'op; 'ty; 'a1; v. 'exp['v] } >>, reduce_letUnop;
   << letBinop{ 'op; 'ty; 'a1; 'a2; v. 'exp['v] } >>, reduce_letBinop;
   << prog{'state; letAlloc{ allocTuple{ 'ty; 'atom_list }; v. 'exp['v] }} >>,
      reduce_allocTuple;
   << prog{'state; letAlloc{ allocArray{ 'ty; 'atom_list }; v. 'exp['v] }} >>,
      reduce_allocArray;
   << copy{ 'len; 'init } >>, unfold_copy;
   << "match"{ number[i:n]; cons{matchCase{'set; 'exp}; 'el} } >>,
      reduce_match_num;
   << "match"{ block{ 'i; 'args }; cons{matchCase{'set; 'exp}; 'el} } >>,
      reduce_match_block;
   << prog{ 'state; letSubscript{ 'ref; 'index; v. 'exp['v] } } >>,
      reduce_letSubscript;
   << prog{ 'state; setSubscript{ 'ref; 'index; 'new_val; 'exp } } >>,
      reduce_setSubscript
]
