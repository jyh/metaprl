(*
 * Quotient type.
 *
 *)

include Tacticals

include Itt_equal
include Itt_set
include Itt_rfun

open Printf
open Nl_debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError
open Resource

open Var
open Sequent
open Tacticals

open Itt_equal
open Itt_subtype

(*
 * Show that the file is loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Itt_quotient%t" eflush

(* debug_string DebugLoad "Loading itt_quotient..." *)

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "quot"{'A; x, y. 'E['x; 'y]}

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

prec prec_quot

dform quot_df1 : mode[prl] :: parens :: "prec"[prec_quot] :: "quot"{'A; x, y. 'E} =
   slot{'x} `", " slot{'y} `":" " " slot{'A} `" // " slot{'E}

dform quot_df2 : mode[src] :: parens :: "prec"[prec_quot] :: "quot"{'A; x, y. 'E} =
   `"quot " slot{'x} `", " slot{'y} `":" slot{'A} `" // " slot{'E}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext quot x, y: A // E
 * by quotientFormation (quot x, y: A // E) z u v
 *
 * H >- A = A in Ui
 * H, x: A, y: A >- E[x, y] = E[x, y] in Ui
 * H, x: A >- E[x, x]
 * H, x: A, y: A, u: E[x, y] >- E[y, x]
 * H, x: A, y: A, z: A, u: E[x, y], v: E[y, z] >- E[x, z]
 *)
prim quotientFormation 'H (quot x, y: 'A // 'E['x; 'y]) 'z 'u 'v :
   sequent [squash] { 'H >- 'A = 'A in univ[@i:l] } -->
   sequent [squash] { 'H; x: 'A; y: 'A >- 'E['x; 'y] = 'E['x; 'y] in univ[@i:l] } -->
   sequent [squash] { 'H; x: 'A >- 'E['x; 'x] } -->
   sequent [squash] { 'H; x: 'A; y: 'A; u: 'E['x; 'y] >- 'E['y; 'x] } -->
   sequent [squash] { 'H; x: 'A; y: 'A; z: 'A; u: 'E['x; 'y]; v: 'E['y; 'z] >- 'E['x; 'z] } -->
   sequent ['ext] { 'H >- univ[@i:l] } =
   quot x, y: 'A // 'E['x; 'y]

(*
 * H >- quot x1, y1: A1 // E1 = quot x2, y2. A2 // E2 in Ui
 * by quotientWeakEquality x y z u v
 *
 * H >- A1 = A2 in Ui
 * H, x: A1, y: A1 >- E1[x, y] = E2[x, y] in Ui
 * H, x: A1 >- E1[x, x]
 * H, x: A1, y: A1, u: E1[x, y] >- E1[y, x]
 * H, x: A1, y: A1, z: A1, u: E1[x, y], v: E1[y, z] >- E1[x, z]
 *)
prim quotientWeakEquality 'H 'x 'y 'z 'u 'v :
   sequent [squash] { 'H >- 'A1 = 'A2 in univ[@i:l] } -->
   sequent [squash] { 'H; x: 'A1; y: 'A1 >- 'E1['x; 'y] = 'E2['x; 'y] in univ[@i:l] } -->
   sequent [squash] { 'H; x: 'A1 >- 'E1['x; 'x] } -->
   sequent [squash] { 'H; x: 'A1; y: 'A1; u: 'E1['x; 'y] >- 'E1['y; 'x] } -->
   sequent [squash] { 'H; x: 'A1; y: 'A1; z: 'A1; u: 'E1['x; 'y]; v: 'E1['y; 'z] >- 'E1['x; 'z] } -->
   sequent ['ext] { 'H >- quot x1, y1: 'A1 // 'E1['x1; 'y1]
                   = quot x2, y2: 'A2 // 'E2['x2; 'y2]
                   in univ[@i:l]
           } =
   it

(*
 * H >- quot x1, y1: A1 // E1 = quot x2, y2. A2 // E2 in Ui
 * by quotientEquality r s v
 *
 * H >- quot x1, y1: A1 // E1 = quot x1, y1: A1 // E1 in Ui
 * H >- quot x2, y2. A2 // E2 = quot x2, y2. A2 // E2 in Ui
 * H >- A1 = A2 in Ui
 * H; v: A1 = A2 in Ui; r: A1; s: A1 >- E1[r, s] -> E2[r, s]
 * H; v: A1 = A2 in Ui; r: A1; s: A1 >- E2[r, s] -> E1[r, s]
 *)
prim quotientEquality 'H 'r 's 'v :
   sequent [squash] { 'H >- quot x1, y1: 'A1 // 'E1['x1; 'y1] = quot x1, y1: 'A1 // 'E1['x1; 'y1] in univ[@i:l] } -->
   sequent [squash] { 'H >- quot x2, y2: 'A2 // 'E2['x2; 'y2] = quot x2, y2: 'A2 // 'E2['x2; 'y2] in univ[@i:l] } -->
   sequent [squash] { 'H >- 'A1 = 'A2 in univ[@i:l] } -->
   sequent [squash] { 'H; v: 'A1 = 'A2 in univ[@i:l]; r: 'A1; s: 'A1 >- 'E1['r; 's] -> 'E2['r; 's] } -->
   sequent [squash] { 'H; v: 'A1 = 'A2 in univ[@i:l]; r: 'A1; s: 'A1 >- 'E2['r; 's] -> 'E1['r; 's] } -->
   sequent ['ext] { 'H >- quot x1, y1: 'A1 // 'E1['x1; 'y1] = quot x2, y2: 'A2 // 'E2['x2; 'y2] in univ[@i:l] } =
   it

(*
 * Typehood.
 *)
prim quotientType 'H 'u 'v 'w 'x1 'x2 :
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent [squash] { 'H; u: 'A; v: 'A >- "type"{'E['u; 'v]} } -->
   sequent [squash] { 'H; u: 'A >- 'E['u; 'u] } -->
   sequent [squash] { 'H; u: 'A; v: 'A; x1: 'E['u; 'v] >- 'E['v; 'u] } -->
   sequent [squash] { 'H; u: 'A; v: 'A; w: 'A; x1: 'E['u; 'v]; x2: 'E['v; 'w] >- 'E['u; 'w] } -->
   sequent ['ext] { 'H >- "type"{.quot x, y: 'A // 'E['x; 'y]} } =
   it

(*
 * H >- quot x, y: A // E ext a
 * by quotient_memberFormation
 *
 * H >- quot x, y: A // E = quot x, y: A // E in Ui
 * H >- A ext a
 *)
prim quotient_memberFormation 'H :
   sequent [squash] { 'H >- "type"{(quot x, y: 'A // 'E['x; 'y])} } -->
   ('a : sequent ['ext] { 'H >- 'A }) -->
   sequent ['ext] { 'H >- quot x, y: 'A // 'E['x; 'y] } =
   'a

(*
 * H >- a1 = a2 in quot x, y: A // E
 * by quotient_memberWeakEquality
 *
 * H >- quot x, y: A // E = quot x, y: A // E in Ui
 * H >- x1 = a2 in A
 *)
prim quotient_memberWeakEquality 'H :
   sequent [squash] { 'H >- "type"{(quot x, y: 'A // 'E['x; 'y])} } -->
   sequent [squash] { 'H >- 'a1 = 'a2 in 'A } -->
   sequent ['ext] { 'H >- 'a1 = 'a2 in quot x, y: 'A // 'E['x; 'y] } =
   it

(*
 * H >- a1 = a2 in quot x, y: A // E
 * by quotient_memberEquality
 *
 * H >- quot x, y: A // E = quot x, y: A // E in Ui
 * H >- a1 = a1 in A
 * H >- a2 = a2 in A
 * H >- E[a1; a2]
 *)
prim quotient_memberEquality 'H :
   sequent [squash] { 'H >- "type"{(quot x, y: 'A // 'E['x; 'y])} } -->
   sequent [squash] { 'H >- 'a1 = 'a1 in 'A } -->
   sequent [squash] { 'H >- 'a2 = 'a2 in 'A } -->
   sequent [squash] { 'H >- 'E['a1; 'a2] } -->
   sequent ['ext] { 'H >- 'a1 = 'a2 in quot x, y: 'A // 'E['x; 'y] } =
   it

(*
 * !!!!CHECK!!!!
 *
 * H, a: quot x, y: A // E, J[x] >- s[a] = t[a] in T[a]
 * by quotientElimination v w z
 *
 * H, a: quot x, y: A // E, J[x] >- T[a] = T[a] in Ui
 * H, a: quot x, y: A // E, J[x], v: A, w: A, z: E[v, w] >- s[v] = t[w] in T[v]
 *)
prim quotientElimination 'H 'J 'v 'w 'z :
   sequent [squash] { 'H; a: quot x, y: 'A // 'E['x; 'y]; 'J['a] >- "type"{'T['a]} } -->
   sequent [squash] { 'H; a: quot x, y: 'A // 'E['x; 'y]; 'J['a];
             v: 'A; w: 'A; z: 'E['v; 'w] >- 's['v] = 't['w] in 'T['v]
           } -->
   sequent ['ext] { 'H; a: quot x, y: 'A // 'E['x; 'y]; 'J['a] >- 's['a] = 't['a] in 'T['a] } =
   it

(*
 * !!!!CHECK!!!!
 *
 * H, x: a1 = a2 in quot x, y: A // E, J[x] >- T[x]
 * by quotient_equalityElimination v
 *
 * H, x: a1 = a2 in quot x, y: A // E, J[x], v: hide(E[a, b]) >- T[x]
 *)
prim quotient_equalityElimination 'H 'J 'v :
   ('g['v] : sequent ['ext] { 'H; x: 'a1 = 'a2 in quot x, y: 'A // 'E['x; 'y]; 'J['x]; v: hide('E['a1; 'a2]) >- 'T['x] }) -->
   sequent ['ext] { 'H; x: 'a1 = 'a2 in quot x, y: 'A // 'E['x; 'y]; 'J['x] >- 'T['x] } =
   'g[it]

(*
 * H >- quot x1, y1: A1 // E1[x1; y1] <= quot x2, y2: A2 // E2[x2; y2]
 * by quotientSubtype
 *
 * H >- A1 <= A2
 * H, x1: A1, y1: A1 >- E1[x1; y1] => E2[x2; y2]
 * H >- quot x1, y1: A1 // E1[x1; y1] in type
 * H >- quot x2, y2: A2 // E2[x2; y2] in type
 *)
prim quotientSubtype 'H 'a1 'a2 :
   sequent [squash] { 'H >- subtype{'A1; 'A2} } -->
   sequent [squash] { 'H; a1: 'A1; a2: 'A1 (* ; 'E1['a1; 'a2] *) >- 'E2['a1; 'a2] } -->
   sequent [squash] { 'H >- "type"{(quot x1, y1: 'A1 // 'E1['x1; 'y1])} } -->
   sequent [squash] { 'H >- "type"{(quot x2, y2: 'A2 // 'E2['x2; 'y2])} } -->
   sequent ['ext] { 'H >- subtype{ (quot x1, y1: 'A1 // 'E1['x1; 'y1]); (quot x2, y2: 'A2 // 'E2['x2; 'y2]) } } =
   it

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let quotient_term = << "quot"{'A; x, y. 'E['x; 'y]} >>
let quotient_opname = opname_of_term quotient_term
let is_quotient_term = is_dep0_dep2_term quotient_opname
let dest_quotient = dest_dep0_dep2_term quotient_opname
let mk_quotient_term = mk_dep0_dep2_term quotient_opname

(*
 * D the conclusion.
 *)
let d_concl_quotient p =
   let count = hyp_count_addr p in
      quotient_memberFormation count p

(*
 * D a hyp.
 * We take the argument.
 *)
let d_hyp_quotient i p =
   let i, j = hyp_indices p i in
      (match maybe_new_vars ["v"; "w"; "z"] (declared_vars p) with
          [v; w; z] ->
             quotientElimination i j v w z
        | _ ->
             failT) p

(*
 * Join them.
 *)
let d_quotientT i =
   if i = 0 then
      d_concl_quotient
   else
      d_hyp_quotient i

let d_resource = d_resource.resource_improve d_resource (quotient_term, d_quotientT)

(*
 * EQCD.
 *)
let eqcd_quotientT p =
   let count = hyp_count_addr p in
      (match maybe_new_vars ["r"; "s"; "t"] (declared_vars p) with
          [r; s; t] ->
             quotientEquality count r s t
             thenT addHiddenLabelT "wf"
        | _ -> failT) p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (quotient_term, eqcd_quotientT)

let quotient_equal_term = << (quot x1, y1: 'A1 // 'E1['x; 'y]) = (quot x2, y2: 'A2 // 'E2['x1; 'x2]) in univ[@i:l] >>

let d_resource = d_resource.resource_improve d_resource (quotient_equal_term, d_wrap_eqcd eqcd_quotientT)

(*
 * Typehood.
 *)
let d_quotient_typeT i p =
   if i = 0 then
      let u, v, w, x1, x2 = maybe_new_vars5 p "u" "v" "w" "x" "y" in
         (quotientType (hyp_count_addr p) u v w x1 x2
          thenLT [addHiddenLabelT "wf";
                  addHiddenLabelT "wf";
                  addHiddenLabelT "antecedent";
                  addHiddenLabelT "antecedent";
                  addHiddenLabelT "antecedent"]) p
   else
      raise (RefineError ("d_quotient_typeT", StringError "no elimination form"))

let quotient_type_term = << "type"{.quot x, y: 'A // 'E['x; 'y]} >>

let d_resource = d_resource.resource_improve d_resource (quotient_type_term, d_quotient_typeT)

(*
 * Membership in a quotient type.
 *)
let d_quotient_equal_memberT i p =
   if i = 0 then
      quotient_memberEquality (hyp_count_addr p) p
   else
      raise (RefineError ("d_quotient_equalT", StringError "no elimination form"))

let quotient_equal_member_term = << 'x = 'y in (quot u, v: 'A // 'E['u; 'v]) >>

let d_resource = d_resource.resource_improve d_resource (quotient_equal_member_term, d_quotient_equal_memberT)

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of quotient.
 *)
let inf_quotient f decl t =
   let x, y, a, e = dest_quotient t in
   let decl', a' = f decl a in
   let decl'', e' = f (add_unify_subst x a (add_unify_subst y a decl')) e in
   let le1, le2 = dest_univ a', dest_univ e' in
      decl'', Itt_equal.mk_univ_term (max_level_exp le1 le2)

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (quotient_term, inf_quotient)

(************************************************************************
 * SUBTYPING                                                            *
 ************************************************************************)

(*
 * Subtyping of two quotient types.
 *)
let quotient_subtypeT p =
   (match maybe_new_vars ["x"; "y"] (declared_vars p) with
       [x; y] ->
          (quotientSubtype (hyp_count_addr p) x y
           thenLT [addHiddenLabelT "subtype";
                   addHiddenLabelT "aux";
                   addHiddenLabelT "wf";
                   addHiddenLabelT "wf"])

     | _ -> failT) p

let sub_resource =
   sub_resource.resource_improve
   sub_resource
   (DSubtype ([<< quot x1, y1: 'A1 // 'E1['x1; 'y1] >>, << quot x2, y2: 'A2 // 'E2['x2; 'y2] >>;
               << 'A1 >>, << 'A2 >>],
              quotient_subtypeT))

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
