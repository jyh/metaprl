(*
 * Functional Intermediate Representation formalized in MetaPRL.
 * Brian Emre Aydemir, emre@its.caltech.edu
 *
 * Define and implement the basic expression forms in the FIR.
 *)

include Base_theory
include Itt_theory
include Fir_int_set
include Fir_ty

(*************************************************************************
 * Declarations.
 *************************************************************************)

(* Identity (polymorphic). *)
declare idOp

(* Subscripts. *)
declare plusSubIntOp
declare minusSubIntOp
declare minusSubSubOp
declare composeSubOp

(* Pointer equality. *)
declare eqEqOp

(* Allocation operators. *)
declare allocTuple{ 'ty; 'atom_list }
declare allocArray{ 'ty; 'atom_list }
declare allocUnion{ 'ty; 'ty_var; 'num; 'atom_list }
define unfold_copy : copy{ 'len; 'init } <-->
   ind{'len; i, j. nil; nil; i, j. cons{'init; 'j}}

(*
 * Normal values.
 *)

(* Subscript atoms. *)
declare atomSubType{ 'ty }
declare atomSubIndex{ 'sub; 'int }
declare atomSubOffset{ 'sub; 'int }
declare atomSubscript{ 'sub }

(* Subscript ops. *)
declare aggrSubscript
declare intSubscript

(* Normal atoms. *)
declare atomInt{ 'int }
declare atomEnum{ 'bound; 'num }
declare atomConst{ 'ty; 'ty_var; 'num }
declare atomVar{ 'var }

(*
 * Expressions.
 *)

(* Function application. *)
declare unOp{ 'op; 'a1; v. 'exp['v] }
declare binOp{ 'op; 'a1; 'a2; v. 'exp['v] }
declare tailCall{ 'var; 'atom_list }

(* Control. *)
declare matchCase{ 'set; 'exp }
declare "match"{ 'key; 'cases }

(* Allocation. *)
declare letAlloc{ 'alloc_op; v. 'exp['v] }

(* Subscripting. *)
declare letSubscript{ 'block; 'index; v. 'exp['v] }
(*declare setSubscript{ 'a1; 'a2; 'a3; 'exp }*)
declare letSubCheck{ 'a1; 'a2; v1, v2. 'exp['v1; 'v2] }

(*************************************************************************
 * Display forms.
 *************************************************************************)

(* Identity (polymorphic). *)
dform idOp_df : except_mode[src] :: idOp = `"id"

(* Subscripts. *)
dform plusSubIntOp_df : except_mode[src] :: plusSubIntOp = `"PlusSubIntOp"
dform minusSubIntOp_df : except_mode[src] :: minusSubIntOp = `"MinusSubIntOp"
dform minusSubSubOp_df : except_mode[src] :: minusSubSubOp = `"MinusSubSubOp"
dform composeSubOp_df : except_mode[src] :: composeSubOp = `"ComposeSubOp"

(* Pointer equality. *)
dform eqEqOp_df : except_mode[src] :: eqEqOp = `"EqEqOp"

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

(* Subscript atoms. *)
dform atomSubType_df : except_mode[src] :: atomSubType{ 'ty } =
   lzone `"AtomSubType(" slot{'ty} `")" ezone
dform atomSubIndex_df : except_mode[src] :: atomSubIndex{ 'sub; 'int } =
   lzone `"AtomSubIndex(" slot{'sub} `", " slot{'int} `")" ezone
dform atomSubOffset_df : except_mode[src] :: atomSubOffset{ 'sub; 'int } =
   lzone `"AtomSubOffset(" slot{'sub} `", " slot{ 'int } `")" ezone
dform atomSubscript_df : except_mode[src] :: atomSubscript{ 'sub } =
   lzone `"AtomSubscript(" slot{'sub} `")" ezone

(* Subscript ops. *)
dform aggrSubscript_df : except_mode[src] :: aggrSubscript = `"AggrSubscript"
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

(* Function application. *)
dform unOp_df : except_mode[src] :: unOp{ 'op; 'a1; v. 'exp } =
   pushm[0] szone push_indent `"let " slot{'v} `" =" hspace
   lzone slot{'op} `"(" slot{'a1} `")" ezone popm hspace
   push_indent `"in" hspace
   szone slot{'exp} ezone popm
   ezone popm
dform binOp_df : except_mode[src] :: binOp{ 'op; 'a1; 'a2; v. 'exp } =
   pushm[0] szone push_indent `"let " slot{'v} `" =" hspace
   lzone `"(" slot{'a1} `" " slot{'op} `" " slot{'a2} `")" ezone popm hspace
   push_indent `"in" hspace
   szone slot{'exp} ezone popm
   ezone popm
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
   letSubscript{ 'block; 'index; v. 'exp } =
   pushm[0] szone push_indent `"let " slot{'v} `" =" hspace
   lzone slot{'block} `"[" slot{'index} `"]" ezone popm hspace
   push_indent `"in" hspace
   szone slot{'exp} ezone popm
   ezone popm

(*************************************************************************
 * Rewrites.
 *************************************************************************)

(* Identity (polymorphic). *)
prim_rw reduce_idOp : unOp{ idOp; 'a1; v. 'exp['v] } <--> 'exp['a1]

(* Integer atom. *)
prim_rw reduce_atomInt : atomInt{ 'num } <--> 'num

(* Enumeration atom. *)
prim_rw reduce_atomEnum : atomEnum{ 'bound; 'num } <--> 'num

(* Allocation. *)
prim_rw reduce_allocTuple :
   letAlloc{ allocTuple{ 'ty; 'atom_list }; v. 'exp['v] } <-->
   'exp[ block{ 0; 'atom_list } ]
prim_rw reduce_allocArray :
   letAlloc{ allocArray{ 'ty; 'atom_list }; v. 'exp['v] } <-->
   'exp[ block{ 0; 'atom_list } ]

(* Control *)
prim_rw reduce_match_num :
   "match"{ number[i:n]; cons{matchCase{'set; 'exp}; 'el} } <-->
   ifthenelse{ member{number[i:n]; 'set}; 'exp; ."match"{number[i:n]; 'el} }
prim_rw reduce_match_block :
   "match"{ block{ 'i; 'args }; cons{matchCase{'set; 'exp}; 'el} } <-->
   ifthenelse{ member{'i; 'set}; 'exp; ."match"{block{'i; 'args}; 'el} }

(* Subscripting. *)
prim_rw reduce_letSubscript :
   letSubscript{ block{'tag; 'args}; 'index; v. 'exp['v] } <-->
   'exp[ nth{'args; 'index} ]
prim_rw reduce_letSubCheck :
   letSubCheck{ 'a1; 'a2; v1, v2. 'exp['v1; 'v2] } <-->
   'exp['a1; 'a2]

(*************************************************************************
 * Automation.
 *************************************************************************)

let resource reduce += [
   << unOp{ idOp; 'a1; v. 'exp['v] } >>, reduce_idOp;

   << letAlloc{ allocTuple{ 'ty; 'atom_list }; v. 'exp['v] } >>,
      reduce_allocTuple;
   << letAlloc{ allocArray{ 'ty; 'atom_list }; v. 'exp['v] } >>,
      reduce_allocArray;
   << copy{ 'len; 'init } >>, unfold_copy;

   << "match"{ number[i:n]; cons{matchCase{'set; 'exp}; 'el} } >>,
      reduce_match_num;
   << "match"{ block{ 'i; 'args }; cons{matchCase{'set; 'exp}; 'el} } >>,
      reduce_match_block;

   << letSubscript{ block{'tag; 'args}; 'index; v. 'exp['v] } >>,
      reduce_letSubscript;
   << letSubCheck{ 'a1; 'a2; v1, v2. 'exp['v1; 'v2] } >>, reduce_letSubCheck
]
