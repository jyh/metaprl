(*
 * Functional Intermediate Representation formalized in MetaPRL.
 * Brian Emre Aydemir, emre@its.caltech.edu
 *
 * Define and implement the basic expression forms for the FIR.
 * See fir_exp.mli for a description of the terms below.
 *
 * Todo:
 *    - any documentation that should go here and not in the .mli file
 *    - verify that everything is declared, and that we've fully
 *      defined everything related to a declaration
 *    - check the array and subscript stuff (and block by extension)
 *    - display forms may need to be tweaked/changed
 *    - letSubCheck wants a more descriptive arg titles.
 *    - reduce_match needs to have its comparison bit checked for
 *      generality sometime
 *
 * Completed (I claim... of course, this is sans typing):
 *    - idOp, unOp, binOp
 *    - letSubscript, letAlloc, allocSafe, allocArray
 *    - block (our representation of memory/arrays)
 *    - letSubCheck (why is this a no-op?)
 *)

include Base_theory
include Itt_theory

open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.RefineError
open Tactic_type.Conversionals
open Itt_list

(*************************************************************************
 * Declarations.
 *************************************************************************)

(*
 * Memory is allocated in blocks.
 * Each block has a tag and some values (a list).
 *)

declare block{ 'tag; 'args }

(*
 * Inlined operators.
 *)

(* Identity (polymorphic). *)
declare idOp

(*
 * Allocation operators.
 *)

declare allocSafe{ 'tag; 'args }
declare allocArray{ 'len; 'init }
define unfold_copy : copy{ 'len; 'init } <-->
   ind{'len; i, j. nil; nil; i, j. cons{'init; 'j}}

(*
 * Normal values.
 *)

declare atomInt{ 'int }
declare atomVar{ 'var; 'ty }

declare tyInt

(*
 * Expressions.
 *)

(* Function application. *)
declare unOp{ 'op; 'a1; v. 'exp['v] }
declare binOp{ 'op; 'a1; 'a2; v. 'exp['v] }
(*declare tailCall*)

(* Control. *)
declare matchCase{ 'set; 'exp }
declare "match"{ 'a; 'cases }

(* Allocation. *)
declare letAlloc{ 'op; v. 'exp['v] }

(* Subscripting. *)
declare letSubscript{ 'block; 'index; v. 'exp['v] }
(*declare setSubscript{ 'a1; 'a2; 'a3; 'exp }*)
declare letSubCheck{ 'a1; 'a2; 'a3; 'exp }

(*
 * Term operations.
 *)

let matchCase_term = << matchCase{ 'set; 'exp } >>
let matchCase_opname = opname_of_term matchCase_term
let is_matchCase_term = is_dep0_dep0_term matchCase_opname
let mk_matchCase_term = mk_dep0_dep0_term matchCase_opname
let dest_matchCase = dest_dep0_dep0_term matchCase_opname

let match_term = << "match"{ 'a; 'cases } >>
let match_opname = opname_of_term match_term
let is_match_term = is_dep0_dep0_term match_opname
let mk_match_term = mk_dep0_dep0_term match_opname
let dest_match = dest_dep0_dep0_term match_opname

(*************************************************************************
 * Display forms.
 *************************************************************************)

(* Blocks / memory. *)
dform block_df : block{ 'tag; 'args } =
   lzone `"block{" slot{'tag} `"; " slot{'args} `"}" ezone

(* Identity (polymorphic). *)
dform idOp_df : idOp = `"id"

(* Allocation operators. *)
dform allocSafe_df : allocSafe{ 'tag; 'args } =
   lzone `"AllocSafe{" slot{'tag} `"; " slot{'args} `"}" ezone
dform allocArray_df : allocArray{ 'len; 'init } =
   lzone `"AllocArray{" slot{'len} `"; " slot{'init} `"}" ezone
dform copy_df : copy{ 'len; 'init} =
   lzone `"copy{" slot{'len} `"; " slot{'init} `"}" ezone

(* Function application. *)
dform unOp_df : unOp{ 'op; 'a1; v. 'exp } =
   pushm[0] szone push_indent `"let " slot{'v} `" =" hspace
   lzone slot{'op} `"(" slot{'a1} `")" ezone popm hspace
   push_indent `"in" hspace
   szone slot{'exp} ezone popm
   ezone popm
dform binOp_df : binOp{ 'op; 'a1; 'a2; v. 'exp } =
   pushm[0] szone push_indent `"let " slot{'v} `" =" hspace
   lzone `"(" slot{'a1} `" " slot{'op} `" " slot{'a2} `")" ezone popm hspace
   push_indent `"in" hspace
   szone slot{'exp} ezone popm
   ezone popm

(* Control. *)
dform matchCase_df : matchCase{ 'set; 'exp } =
   pushm[0] szone push_indent slot{'set} `" ->" hspace
   szone slot{'exp} ezone popm
   ezone popm
dform match_df : "match"{'a; 'cases } =
   pushm[0] szone push_indent `"match" hspace
   szone slot{'a} ezone popm hspace
   push_indent `"in" hspace
   szone slot{'cases} ezone popm
   ezone popm

(* Allocation *)
dform letAlloc_df : letAlloc{ 'op; v. 'exp } =
   pushm[0] szone push_indent `"let " slot{'v} `" =" hspace
   lzone slot{'op} ezone popm hspace
   push_indent `"in" hspace
   szone slot{'exp} ezone popm
   ezone popm

(* Subscripting. *)
dform letSubscript_df : letSubscript{ 'block; 'index; v. 'exp } =
   pushm[0] szone push_indent `"let " slot{'v} `" =" hspace
   lzone slot{'block} `"[" slot{'index} `"]" ezone popm hspace
   push_indent `"in" hspace
   szone slot{'exp} ezone popm
   ezone popm
(* dform setSubscript_df : *)
(* dform letSubCheck_df : *)

(*************************************************************************
 * Rewrites.
 *************************************************************************)

(* Identity (polymorphic). *)
prim_rw reduce_idOp : unOp{ idOp; 'a1; v. 'exp['v] } <--> 'exp['a1]

(* Allocation. *)
prim_rw reduce_allocSafe : letAlloc{ allocSafe{'tag; 'args}; v. 'exp['v] } <-->
   'exp[ block{'tag; 'args} ]
prim_rw reduce_allocArray :
   letAlloc{ allocArray{'len; 'init}; v. 'exp['v] } <-->
   'exp[ block{0; copy{'len; 'init}} ]

(* Control *)
(*
prim_rw reduce_match : "match"{'arg; cons{matchCase{'set; 'e}; 'el}} <-->
   ifthenelse{eq_bool{'arg; 'set}; 'e; ."match"{'arg; 'el}}
*)

(*
prim_rw reduce_match_bool : "match"{atomVar{'arg; tyBool}; cons{matchCase{'set; 'e}; 'el}} <-->
   ifthenelse{eq_bool{'arg; 'set}; 'e; ."match"{'arg; 'el}}
*)

prim_rw reduce_match_int : "match"{atomVar{'arg; tyInt}; cons{matchCase{'set; 'e}; 'el}} <-->
   ifthenelse{eq_int{'arg; 'set}; 'e; ."match"{'arg; 'el}}

(*
ml_rw reduce_match : ( 'goal : "match"{'a; 'cases} ) =
   let a, cases = dest_match goal in
      if not (is_cons_term cases) then
         (* nothing to match; we're stuck *)
         raise (RefineError ("reduce_match", StringError "no cases"))
      else
         let head, tail = dest_cons cases in
         let set, exp = dest_matchCase head in
            (* if the keys match, return exp, else recurse down the cases *)
            if ( set = a ) then
               exp
            else
               mk_match_term a tail
*)

(* Subscripting. *)
prim_rw reduce_letSubscript :
   letSubscript{ block{'tag; 'args}; 'index; v. 'exp['v] } <-->
   'exp[ nth{'args; 'index} ]
prim_rw reduce_letSubCheck : letSubCheck{'a1; 'a2; 'a3; 'exp} <--> 'exp

(*************************************************************************
 * Automation.
 *************************************************************************)

let resource reduce +=
   [<< unOp{ idOp; 'a1; v. 'exp['v] } >>, reduce_idOp;

    << letAlloc{ allocSafe{'tag; 'args}; v. 'exp['v] } >>, reduce_allocSafe;
    << letAlloc{ allocArray{'len; 'init}; v. 'exp['v] } >>, reduce_allocArray;
    << copy{ 'len; 'init } >>, unfold_copy;

    (*<< "match"{ 'a; 'cases } >>, reduce_match;*)

    << letSubscript{ block{'tag; 'args}; 'index; v. 'exp['v] } >>,
       reduce_letSubscript;
    << letSubCheck{'a1; 'a2; 'a3; 'exp} >>, reduce_letSubCheck]
