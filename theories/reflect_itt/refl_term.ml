(*
 * Define terms.
 *)

include Itt_theory

open Conversionals

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

(*
 * Parts of terms.
 *)
declare opname{'l}
declare opname_eq{'op1; 'op2}
declare opname_type

declare level{'i; 'levels}
declare level_type

declare "pstring"{'s}
declare "ptoken"{'t}
declare "pvar"{'v}
declare "pint"{'i}
declare "plevel"{'l}
declare "mstring"{'s}
declare "mtoken"{'s}
declare "mvar"{'s}
declare "mint"{'s}
declare "mlevel"{'s}
declare param_type

declare operator{'name; 'params}
declare operator_type

declare bterm{'sl; 't}
declare bterm_type{'t}

declare term{'op; 'bterms}
declare term_type

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

dform opname_type_df : mode[prl] :: opname_type =
   `"OpnameType"

dform level_type_df : mode[prl] :: level_type =
   `"LevelType"

dform level_df1 : mode[prl] :: level{0; 'l} =
   `"level(" slot{'l} `")"

dform level_df2 : mode[prl] :: level{'i; 'l} =
   `"level(" pushm[0] slot{'i} `";" space slot{'l} `")" popm

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

primrw unfold_level : level{'i; 'levels} <--> pair{'i; 'levels}
primrw unfold_level_type : level_type <--> (int * list{.atom * int})

primrw unfold_param : param_type <-->
   (atom        (* string *)
    + atom      (* token *)
    + atom      (* var *)
    + int       (* int *)
    + level     (* level *)
    + atom      (* mstring *)
    + atom      (* mtoken *)
    + atom      (* mvar *)
    + atom      (* mint *)
    + atom      (* mlevel *)
    + void)
primrw unfold_pstring : pstring{'s} <--> inl{'s}
primrw unfold_ptoken  : ptoken{'t}  <--> inr{inl{'t}}
primrw unfold_pvar    : pvar{'v}    <--> inr{inr{inl{'v}}}
primrw unfold_pint    : pint{'i}    <--> inr{inr{inr{inl{'i}}}}
primrw unfold_plevel  : plevel{'l}  <--> inr{inr{inr{inr{inl{'l}}}}}
primrw unfold_mstring : mstring{'s} <--> inr{inr{inr{inr{inr{inl{'s}}}}}}
primrw unfold_mtoken  : mtoken{'s}  <--> inr{inr{inr{inr{inr{inr{inl{'s}}}}}}}
primrw unfold_mvar    : mvar{'s}    <--> inr{inr{inr{inr{inr{inr{inr{inl{'s}}}}}}}}
primrw unfold_mint    : mint{'s}    <--> inr{inr{inr{inr{inr{inr{inr{inr{inl{'s}}}}}}}}}
primrw unfold_mlevel  : mlevel{'s}  <--> inr{inr{inr{inr{inr{inr{inr{inr{inr{inl{'s}}}}}}}}}}

primrw unfold_operator : operator{'name; 'params} <--> pair{'name; 'params}
primrw unfold_operator_type : operator_type <--> (opname_type * param_type list)

primrw unfold_bterm : bterm{'sl; 't} <--> pair{'sl, 't}
primrw unfold_bterm_type : bterm_type{'T} <--> (list{atom} * 'T)

primrw unfold_term : term{'op; 'bterms} <--> pair{'op; 'bterms}
primrw unfold_term_type : term_type <--> srec{T. operator_type * list{bterm_type{'T}}}

let fold_level = makeFoldC << level{'i; 'levels} >> unfold_level
let fold_level_type = makeFoldC << level_type >> unfold_level_type

let fold_param = makeFoldC << param_type >> unfold_param
let fold_pstring = makeFoldC << "pstring"{'s} >> unfold_pstring
let fold_ptoken = makeFoldC << "ptoken"{'s} >> unfold_ptoken
let fold_pvar = makeFoldC << "pvar"{'s} >> unfold_pvar
let fold_pint = makeFoldC << "pint"{'s} >> unfold_pint
let fold_plevel = makeFoldC << "plevel"{'s} >> unfold_plevel
let fold_mstring = makeFoldC << "mstring"{'s} >> unfold_mstring
let fold_mtoken = makeFoldC << "mtoken"{'s} >> unfold_mtoken
let fold_mvar = makeFoldC << "mvar"{'s} >> unfold_mvar
let fold_mint = makeFoldC << "mint"{'s} >> unfold_mint
let fold_mlevel = makeFoldC << "mlevel"{'s} >> unfold_mlevel

let fold_operator = makeFoldC << operator{'name; 'params} >> unfold_operator
let fold_operator_type = makeFoldC << operator_type >> unfold_operator_type

let fold_bterm = makeFoldC << bterm{'sl; 't} >> unfold_bterm
let fold_bterm_type = makeFoldC << bterm_type{'T} >> unfold_bterm_type

let fold_term = makeFoldC << term{'op; 'bterms} >> unfold_term
let fold_term_type = makeFoldC << term_type >> unfold_term_type

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Opnames are an arbitrary type.
 *)
prim opname_type 'H : :
   sequent ['ext] { 'H >- "type"{opname_type} } = it

(*
 * Opnames have a decidable equality.
 *)
prim opname_eq_wf 'H :
   sequent [squash] { 'H >- 'op1 = 'op3 in opname_type } -->
   sequent [squash] { 'H >- 'op2 = 'op4 in opname_type } -->
   sequent ['ext] { 'H >- opname_eq{'op1; 'op2} = opname_eq{'op3; 'op4} in bool } =
   it

prim opname_eq_intro 'H :
   sequent [squash] { 'H >- 'op1 = 'op2 in opname_type } -->
   sequent ['ext] { 'H >- "assert"{opname_eq{'op1; 'op2}} } =
   it

prim opname_eq_elim 'H 'J 'y :
   ('t['y] : sequent ['ext] { 'H; x: "assert"{opname_eq{'op1; 'op2}}; 'J['x]; y: 'op1 = 'op2 in opname_type >- 'C['x] }) -->
   sequent ['ext] { 'H; x: "assert"{opname_eq{'op1; 'op2}}; 'J['x] >- 'C['x] } =
   't[it]

(*
 * String lists are a subtype of opnames.
 *)
prim opname_intro 'H :
   sequent [squash] { 'H >- 'l1 = 'l2 in list{atom} } -->
   sequent ['ext] { 'H >- opname{'l1} = opname{'l2} in opname_type } =
   it

(*
 * Levels.
 *)
interactive level_type2 'H : :
   sequent ['ext] { 'H >- "type"{level_type} }

interactive level_intro2 'H :
   sequent [squash] { 'H >- 'i1 = 'i2 in int } -->
   sequent [squash] { 'H >- 'l1 = 'l2 in list{.atom * int} } -->
   sequent ['ext] { 'H >- level{'i1; 'l1} = level{'i2; 'l2} in level_type }

interactive level_elim2 'H 'J :
   sequent ['ext] { 'H; i: int; l: list{.atom * int}; 'J[level{'i; 'l}] >- 'C[level{'i; 'l}] } -->
   sequent ['ext] { 'H; x: level_type; 'J['x] >- 'C['x] }

(*
 * Params.
 *)
interactive param_type 'H : :
   sequent ['ext] { 'H >- "type"{param_type} }

interactive pstring_intro 'H :
   sequent [squash] { 'H >- 's1 = 's2 in atom } -->
   sequent ['ext] { 'H >- "pstring"{'s1} = "pstring"{'s2} in param_type }

interactive ptoken_intro 'H :
   sequent [squash] { 'H >- 's1 = 's2 in atom } -->
   sequent ['ext] { 'H >- "ptoken"{'s1} = "ptoken"{'s2} in param_type }

interactive pvar_intro 'H :
   sequent [squash] { 'H >- 's1 = 's2 in atom } -->
   sequent ['ext] { 'H >- "pvar"{'s1} = "pvar"{'s2} in param_type }

interactive pint_intro 'H :
   sequent [squash] { 'H >- 's1 = 's2 in int } -->
   sequent ['ext] { 'H >- "pint"{'s1} = "pint"{'s2} in param_type }

interactive plevel_intro 'H :
   sequent [squash] { 'H >- 's1 = 's2 in level } -->
   sequent ['ext] { 'H >- "plevel"{'s1} = "plevel"{'s2} in param_type }

interactive mstring_intro 'H :
   sequent [squash] { 'H >- 's1 = 's2 in atom } -->
   sequent ['ext] { 'H >- "mstring"{'s1} = "mstring"{'s2} in param_type }

interactive mtoken_intro 'H :
   sequent [squash] { 'H >- 's1 = 's2 in atom } -->
   sequent ['ext] { 'H >- "mtoken"{'s1} = "mtoken"{'s2} in param_type }

interactive mint_intro 'H :
   sequent [squash] { 'H >- 's1 = 's2 in atom } -->
   sequent ['ext] { 'H >- "mint"{'s1} = "mint"{'s2} in param_type }

interactive mvar_intro 'H :
   sequent [squash] { 'H >- 's1 = 's2 in atom } -->
   sequent ['ext] { 'H >- "mvar"{'s1} = "mvar"{'s2} in param_type }

interactive mlevel_intro 'H :
   sequent [squash] { 'H >- 's1 = 's2 in atom } -->
   sequent ['ext] { 'H >- "mlevel"{'s1} = "mlevel"{'s2} in param_type }

interactive param_elim 'H 'J 's :
   sequent ['ext] { 'H; s: atom;  'J[pstring{'s}] >- 'C[pstring{'s}] } -->
   sequent ['ext] { 'H; s: atom;  'J[ptoken{'s}]  >- 'C[ptoken{'s}] } -->
   sequent ['ext] { 'H; s: atom;  'J[pvar{'s}]    >- 'C[pvar{'s}] } -->
   sequent ['ext] { 'H; s: int;   'J[pint{'s}]    >- 'C[pint{'s}] } -->
   sequent ['ext] { 'H; s: level; 'J[plevel{'s}]  >- 'C[plevel{'s}] } -->
   sequent ['ext] { 'H; s: atom;  'J[mstring{'s}] >- 'C[mstring{'s}] } -->
   sequent ['ext] { 'H; s: atom;  'J[mtoken{'s}]  >- 'C[mtoken{'s}] } -->
   sequent ['ext] { 'H; s: atom;  'J[mvar{'s}]    >- 'C[mvar{'s}] } -->
   sequent ['ext] { 'H; s: atom;  'J[mint{'s}]    >- 'C[mint{'s}] } -->
   sequent ['ext] { 'H; s: atom;  'J[mlevel{'s}]  >- 'C[mlevel{'s}] } -->
   sequent ['ext] { 'H; x: param_type; 'J['x] >- 'C['x] }

(*
 * Operators.
 *)
interactive operator_type 'H : :
   sequent ['ext] { 'H >- "type"{operator_type} }

interactive operator_intro 'H :
   sequent [squash] { 'H >- 'name1 = 'name2 in opname_type } -->
   sequent [squash] { 'H >- 'params1 = 'params2 in list{param_type} } -->
   sequent ['ext] { 'H >- operator{'name1; 'params1} = operator{'name2; 'params2} in operator_type }

interactive operator_elim 'H 'J :
   sequent ['ext] { 'H; y: opname_type; z: list{param_type}; 'J[operator{'y; 'z}] >- 'C[operator{'y; 'z}] } -->
   sequent ['ext] { 'H; x: operator; 'J['x] >- 'C['x] }

(*
 * Terms.
 *)
interactive term_type 'H : :
   sequent ['ext] { 'H >- "type"{term_type} }

interactive term_intro 'H :
   sequent [squash] { 'H >- 'op1 = 'op2 in operator } -->
   sequent [squash] { 'H >- 'bterms1 = 'bterms2 in list{.(list{atom} * term_type)} } -->
   sequent ['ext] { 'H >- term{'op1; 'bterms1} = term{'op2; 'bterms2} in term_type }

interactive term_elim 'H 'J 'y 'l 'z :
   sequent ['ext] { 'H; y: operator_type; l: list{.(list{atom} * term_type)}; 'J[term{'y; 'l}];
      z: list_ind{'l; ."true"; h, t, g. 'C[snd{'h}] & 'g} >- 'C[term{'y; 'l}] } -->
   sequent ['ext] { 'H; x: term_type; 'J['x] >- 'C['x] }

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
