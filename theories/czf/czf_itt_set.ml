(*
 * The "set" type is used to relate CZF to the Nuprl type theory.
 * The set type is defined inductively.
 *    The base types are:
 *       1. int
 *       2. fun{A; x.B[x]}
 *       3. exists{A; x.B[x]}
 *       4. union{A; B}
 *       5. equal{A; a; b}
 *
 *    The inductive construction is given by rule:
 *       6. H >- T in U1         H, x:T >- a in set
 *          -------------------------------------
 *               H >- collect{T; x. a[x]} in set
 *
 * We could define this set recursively.  Instead, we define it
 * as a collection of rules.
 *)

include Itt_theory

open Printf
open Debug

open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.Refine
open Resource
open Term_stable

open Tactic_type
open Sequent
open Var

open Itt_equal
open Itt_rfun
open Itt_dprod
open Itt_union

(*
 * Show that the file is loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Itt_equal%t" eflush

let debug_czf_set =
   create_debug (**)
      { debug_name = "czf_set";
        debug_description = "display czf_set operations";
        debug_value = false
      }

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "set"
declare member{'x; 't}

(*
 * These are the small types from which sets are built.
 *)
declare small
declare small_type{'t}

(*
 * The "collect" term is used to build sets.
 *)
declare "collect"{'T; x. 'a['x]}

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform set_df : set =
   `"set"

dform member_df : mode[prl] :: parens :: "prec"[prec_apply] :: member{'x; 't} =
   slot{'x} " " Nuprl_font!member " " slot{'t}

dform small_df : small =
   `"small"

dform small_type_df : small_type{'t} =
   slot{'t} " " `"small_type"

dform collect_df : mode[prl] :: parens :: "prec"[prec_apply] :: collect{'T; x. 'a} =
   szone pushm[3] `"collect" " " slot{'x} `":" " " slot{'T} `"." " " slot{'a} popm ezone

(************************************************************************
 * SMALL TYPE RULES                                                     *
 ************************************************************************)

(*
 * These are the types in the small universe.
 *)
prim hyp_small 'H 'J : :
   sequent ['ext] { 'H; a: small; 'J['a] >- small_type{'a} } =
   it

prim int_small 'H : :
   sequent ['ext] { 'H >- small_type{int} } =
   it

prim fun_small 'H :
   sequent ['ext] { 'H >- small_type{'A} } -->
   sequent ['ext] { 'H; a: 'A >- small_type{'B['a]} } -->
   sequent ['ext] { 'H >- small_type{(a: 'A -> 'B['a])} } =
   it

prim exists_small 'H :
   sequent ['ext] { 'H >- small_type{'A} } -->
   sequent ['ext] { 'H; a: 'A >- small_type{'B['a]} } -->
   sequent ['ext] { 'H >- small_type{(a: 'A * 'B['a])} } =
   it

prim union_small 'H :
   sequent ['ext] { 'H >- small_type{'A} } -->
   sequent ['ext] { 'H >- small_type{'B} } -->
   sequent ['ext] { 'H >- small_type{('A + 'B)} } =
   it

prim equal_small 'H :
   sequent ['ext] { 'H >- small_type{'A} } -->
   sequent ['ext] { 'H >- 'a = 'a in 'A } -->
   sequent ['ext] { 'H >- 'b = 'b in 'A } -->
   sequent ['ext] { 'H >- small_type{('a = 'b in 'A)} } =
   it

(*
 * There are no other small types.
 *)
prim small_elim 'H 'J (a1: 'A1 -> 'B1) (a2:'A2 * 'B2) ('A3 + 'B3) ('a4 = 'b4 in 'A4) :
   sequent ['ext] { 'H; 'J[int] >- 'C[int] } -->
   sequent ['ext] { 'H; A1: small; B1: 'A1 -> small; 'J[(a1:'A1 -> 'B1 'a1)] >- 'C[(a1:'A1 -> 'B1 'a1)] } -->
   sequent ['ext] { 'H; A2: small; B2: 'A2 -> small; 'J[(a2:'A2 * 'B2 'a2)] >- 'C[(a2:'A2 * 'B2 'a2)] } -->
   sequent ['ext] { 'H; A3: small; B3: small; 'J[('A3 + 'B3)] >- 'C[('A3 + 'B3)] } -->
   sequent ['ext] { 'H; A4: small; a4: 'A4; b: 'A4; 'J[('a4 = 'b4 in 'A4)] >- 'C[('a4 = 'b4 in 'A4)] } -->
   sequent ['ext] { 'H; x: small; 'J['x] >- 'C['x] } =
   it

(************************************************************************
 * SET TYPE                                                             *
 ************************************************************************)

(*
 * This is how a set is constructed.
 *)
prim collect_set 'H :
   sequent ['ext] { 'H >- small_type{'T} } -->
   sequent ['ext] { 'H; x: 'T >- member{'a['x]; set} } -->
   sequent ['ext] { 'H >- member{collect{'T; x. 'a['x]}; set} } =
   it

(*
 * Transfinite induction.
 * BUG: we need to work out the induction combinator.
 *)
prim set_elim 'H 'J 'a 'T 'f 'w :
   ('t['a; 'T; 'f; 'w] : sequent ['ext] { 'H; a: set; 'J['a]; T: small; f: 'T -> set; w: (all x : 'T. 'C['f 'x]) >- 'C[collect{'T; x. 'f 'x}] }) -->
   sequent ['ext] { 'H; a: set; 'J['a] >- 'C['a] } =
   it

(************************************************************************
 * PRIMITIVES                                                           *
 ************************************************************************)

let int_opname = opname_of_term Itt_int.int_term
let fun_opname = opname_of_term Itt_rfun.fun_term
let prod_opname = opname_of_term Itt_dprod.dprod_term
let union_opname = opname_of_term Itt_union.union_term
let equal_opname = opname_of_term Itt_equal.equal_term

let set_term = << set >>
let small_term = << small >>

let small_type_term = << small_type{'t} >>
let small_type_opname = opname_of_term small_type_term

let member_term = << member{'x; 't} >>
let member_opname = opname_of_term member_term

let collect_term = << collect{'T; x. 'a['x]} >>
let collect_opname = opname_of_term collect_term

let mk_small_type_term =
   mk_dep0_term small_type_opname

let dest_small_type =
   dest_dep0_term small_type_opname

let mk_member_term =
   mk_dep0_dep0_term member_opname

let dest_member =
   dest_dep0_dep0_term member_opname

let mk_collect_term =
   mk_dep0_dep1_term collect_opname

let dest_collect t =
   dest_dep0_dep1_term collect_opname

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Small intro.
 *)
let d_small_typeT i p =
   eprintf "d_small_typeT%t" eflush;
   if i <> 0 then
      raise (RefineError ("d_small_typeT", StringTermError ("no elimination rule", small_type_term)))
   else
      let t = Sequent.concl p in
      let t = one_subterm t in
      let opname = opname_of_term t in
      let n = hyp_count p in
      let rule =
         if opname == int_opname then
            int_small n
         else if opname == fun_opname then
            fun_small n
         else if opname == prod_opname then
            exists_small n
         else if opname == union_opname then
            union_small n
         else if opname == equal_opname then
            equal_small n thenLT [idT; setLabelT "wf"; setLabelT "wf"]
         else
            raise (RefineError ("d_small_typeT", StringTermError ("no rule applies", t)))
      in
         rule p

let x0_resource = d_resource

let d_resource = d_resource.resource_improve d_resource (small_type_term, d_small_typeT)

let x1_resource = d_resource

(*
 * Small elim.
 *)
let d_smallT i p =
   if i = 0 then
      raise (RefineError ("d_small_T", StringTermError ("no formation rule", small_term)))
   else
      let i, j = hyp_indices p i in
      let v_a, v_b, v_A, v_B = maybe_new_vars4 p "a" "b" "A" "B" in
      let t_a = mk_var_term v_a in
      let t_b = mk_var_term v_b in
      let t_A = mk_var_term v_A in
      let t_B = mk_var_term v_B in
      let fun_t = mk_dfun_term v_a t_A t_B in
      let prod_t = mk_dprod_term v_a t_A t_B in
      let union_t = mk_union_term t_A t_B in
      let equal_t = mk_equal_term t_A t_a t_b in
         small_elim i j fun_t prod_t union_t equal_t p

let d_resource = d_resource.resource_improve d_resource (small_term, d_smallT)

let x2_resource = d_resource

(************************************************************************
 * MEM RESOURCE                                                         *
 ************************************************************************)

(*
 * MEM resource.
 * Use simple table.
 *)
type memd_data = tactic term_stable

resource (term * tactic, tactic, memd_data) memd_resource

(*
 * Extract an MEM tactic from the data.
 * The tactic checks for an optable.
 *)
let extract_data base =
   let tbl = sextract base in
   let memd p =
      let t = concl p in
      let t, _ = dest_member t in
         try
            (* Find and apply the right tactic *)
            if !debug_czf_set then
               eprintf "Czf_itt_set.memd: looking up %s%t" (Simple_print.string_of_opname (opname_of_term t)) eflush;
            let tac = slookup tbl t in
               if !debug_czf_set then
                  eprintf "Czf_itt_set.memd: found a tactic for %s%t" (Simple_print.string_of_opname (opname_of_term t)) eflush;
               tac p
         with
            Not_found ->
               raise (RefineError ("memd", StringTermError ("Memd tactic doesn't know about ", t)))
   in
      memd

(*
 * Wrap up the joiner.
 *)
let rec join_resource { resource_data = data1 } { resource_data = data2 } =
   { resource_data = join_stables data1 data2;
     resource_join = join_resource;
     resource_extract = extract_resource;
     resource_improve = improve_resource
   }

and extract_resource { resource_data = data } =
   extract_data data

and improve_resource { resource_data = data } (t, tac) =
   { resource_data = sinsert data t tac;
     resource_join = join_resource;
     resource_extract = extract_resource;
     resource_improve = improve_resource
   }

(*
 * Resource.
 *)
let memd_resource =
   { resource_data = new_stable ();
     resource_join = join_resource;
     resource_extract = extract_resource;
     resource_improve = improve_resource
   }

(*
 * We inherit the tactic during proofs.
 *)
let memd_of_proof p =
   get_tactic p "memd"

(*
 * Memd on a collection.
 *)
let memd_collectT p =
   collect_set (Sequent.hyp_count p) p

let memd_resource = memd_resource.resource_improve memd_resource (collect_term, memd_collectT)

let memdT = memd_resource.resource_extract memd_resource

(*
 * Set elimination.
 *)
let d_setT i p =
   if i = 0 then
      raise (RefineError ("d_setT", StringTermError ("no formation rule", set_term)))
   else
      let i, j = hyp_indices p i in
      let v_a, _ = nth_hyp p i in
      let v_T, v_f, v_b = maybe_new_vars3 p "T" "f" "b" in
         set_elim i j v_a v_T v_f v_b p

let d_resource = d_resource.resource_improve d_resource (set_term, d_setT)

let x3_resource = d_resource

let dT = d_resource.resource_extract d_resource

(*
 * $Log$
 * Revision 1.2  1998/06/16 16:26:04  jyh
 * Added itt_test.
 *
 * Revision 1.1  1998/06/15 22:32:49  jyh
 * Added CZF.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
