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
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError
open Resource
open Term_stable

open Tacticals
open Tacticals
open Conversionals
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

(*
 * Well-formedness judgements on propositions,
 * and restricted propositions do not range over
 * all sets.
 *    wf{'p}: 'p is a well-formed proposition in CZF
 *    restricted{'p}: 'p is a well-formed restricted proposition in CZF
 *       where restricted means that it contains no unbounded
 *       set quantifications.
 *)
declare wf{'p}
declare restricted{'p}

(*
 * These are the small types from which sets are built.
 *    small: the type of small propositions
 *    small_desc: descriptions of small propositions
 *
 *)
declare small
declare small_type{'t}

(*
 * Sets are built by collecting over small types.
 *   set: the type of all sets
 *   isset{'s}: the judgement that 's is a set
 *   member{'x; 't}:
 *      a. 'x is a set
 *      b. 't is a set
 *      c. 'x is an element of 't
 *   collect{'T; x. 'a['x]}:
 *      the set constructed from the family of sets 'a['x]
 *      where 'x ranges over 'T
 *)
declare set
declare isset{'s}
declare member{'x; 't}
declare collect{'T; x. 'a['x]}

(************************************************************************
 * DEFINITIONS                                                          *
 ************************************************************************)

(*
 * Sets.
 *)
primrw unfold_small_type : small_type{'t} <--> ('t = 't in small)
primrw unfold_set : set <--> w{small; x. 'x}
primrw unfold_isset : isset{'s} <--> ('s = 's in set)
primrw unfold_member : member{'x; 'y} <-->
  (('y = 'y in set) & tree_ind{'y; t, f, g. "exists"{'t; a. 'f 'a = 'x in set}})
primrw unfold_collect : collect{'T; x. 'a['x]} <--> tree{'T; lambda{x. 'a['x]}}

let fold_small_type = makeFoldC << small_type{'t} >> unfold_small_type
let fold_set        = makeFoldC << set >> unfold_set
let fold_isset      = makeFoldC << isset{'t} >> unfold_isset
let fold_member     = makeFoldC << member{'x; 'y} >> unfold_member
let fold_collect    = makeFoldC << collect{'T; x. 'a['x]} >> unfold_collect

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform wf_df : mode[prl] :: parens :: "prec"[prec_apply] :: wf{'A} =
   slot{'A} `" wf"

dform restricted_df : mode[prl] :: parens :: "prec"[prec_apply] :: restricted{'A} =
   slot{'A} `" restricted"

dform small_df : small =
   `"small"

dform small_type_df : small_type{'t} =
   slot{'t} " " `"small_type"

dform set_df : set =
   `"set"

dform isset_df : mode[prl] :: parens :: "prec"[prec_apply] :: isset{'s} =
   slot{'s} `" set"

dform member_df : mode[prl] :: parens :: "prec"[prec_apply] :: member{'x; 't} =
   slot{'x} " " Nuprl_font!member " " slot{'t}

dform collect_df : mode[prl] :: parens :: "prec"[prec_apply] :: collect{'T; x. 'a} =
   szone pushm[3] `"collect" " " slot{'x} `":" " " slot{'T} `"." " " slot{'a} popm ezone

(*
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
*)

(************************************************************************
 * SET TYPE                                                             *
 ************************************************************************)

(*
 * By assumption.
 *)
interactive isset_assum 'H 'J : :
   sequent ['ext] { 'H; x: set; 'J['x] >- isset{'x} }

(*
 * Only sets have elements.
 *)
interactive isset_contains 'H 'x :
   sequent ['ext] { 'H >- member{'x; 'y} } -->
   sequent ['ext] { 'H >- isset{'y} }

(*
 * Elements of a set are also sets.
 *)
interactive isset_member 'H 'y :
   sequent ['ext] { 'H >- member{'x; 'y} } -->
   sequent ['ext] { 'H >- isset{'x} }

(*
 * This is how a set is constructed.
 *)
interactive isset_collect 'H 'y :
   sequent ['ext] { 'H >- small_type{'T} } -->
   sequent ['ext] { 'H; y: 'T >- isset{'a['y]} } -->
   sequent ['ext] { 'H >- isset{collect{'T; x. 'a['x]}} }

(*
 * Induction.
 *)
interactive set_elim 'H 'J 'a 'T 'f 'w :
   sequent ['ext] { 'H;
                    a: set;
                    'J['a];
                    T: small;
                    f: 'T -> set;
                    w: (all x : 'T. 'C['f 'x])
                  >- 'C[collect{'T; x. 'f 'x}]
                  } -->
   sequent ['ext] { 'H; a: set; 'J['a] >- 'C['a] }

(************************************************************************
 * RELATION TO ITT                                                      *
 ************************************************************************)

(*
 * We need the property that every well-formed proposition
 * is a type.  The proof is delayed until the theory is collected
 * and an induction form is given for well-formed formulas.
 *)
interactive wf_type 'H :
   sequent ['ext] { 'H >- wf{'T} } -->
   sequent ['ext] { 'H >- "type"{'T} }

(*
 * A set is a type in ITT.
 *)
interactive set_type 'H : :
   sequent ['ext] { 'H >- "type"{set} }

(*
 * Membership judgment is also a type.
 *)
interactive member_type 'H :
   sequent ['ext] { 'H >- isset{'t} } -->
   sequent ['ext] { 'H >- isset{'a} } -->
   sequent ['ext] { 'H >- "type"{member{'a; 't}} }

(*
 * Equality from sethood.
 *)
interactive equal_set 'H :
   sequent ['ext] { 'H >- isset{'s} } -->
   sequent ['ext] { 'H >- 's = 's in set }

(*
 * Equality from membership.
 *)
interactive equal_member 'H :
   sequent ['ext] { 'H >- member{'x; 's} } -->
   sequent ['ext] { 'H >- 'x = 'x in 's }

(************************************************************************
 * PRIMITIVES                                                           *
 ************************************************************************)

let int_opname = opname_of_term Itt_int.int_term
let fun_opname = opname_of_term Itt_rfun.fun_term
let prod_opname = opname_of_term Itt_dprod.dprod_term
let union_opname = opname_of_term Itt_union.union_term
let equal_opname = opname_of_term Itt_equal.equal_term

let wf_term = << wf{'a} >>
let restricted_term = << restricted{'a} >>
let wf_opname = opname_of_term wf_term
let restricted_opname = opname_of_term restricted_term

let small_term = << small >>
let small_type_term = << small_type{'t} >>
let small_type_opname = opname_of_term small_type_term

let set_term = << set >>
let isset_term = << isset{'s} >>
let member_term = << member{'x; 't} >>
let collect_term = << collect{'T; x. 'a['x]} >>

let isset_opname = opname_of_term isset_term
let member_opname = opname_of_term member_term
let collect_opname = opname_of_term collect_term

(*
 * Testers.
 *)
let is_wf_term =
   is_dep0_term wf_opname

let is_restricted_term =
   is_dep0_term restricted_opname

let is_small_type_term =
   is_dep0_term small_type_opname

let is_isset_term =
   is_dep0_term isset_opname

let is_member_term =
   is_dep0_dep0_term member_opname

let is_collect_term =
   is_dep0_dep1_term collect_opname

(*
 * Constructors.
 *)
let mk_wf_term =
   mk_dep0_term wf_opname

let mk_restricted_term =
   mk_dep0_term restricted_opname

let mk_small_type_term =
   mk_dep0_term small_type_opname

let mk_isset_term =
   mk_dep0_term isset_opname

let mk_member_term =
   mk_dep0_dep0_term member_opname

let mk_collect_term =
   mk_dep0_dep1_term collect_opname

(*
 * Destructors.
 *)
let dest_wf =
   dest_dep0_term wf_opname

let dest_restricted =
   dest_dep0_term restricted_opname

let dest_small_type =
   dest_dep0_term small_type_opname

let dest_isset =
   dest_dep0_term isset_opname

let dest_member =
   dest_dep0_dep0_term member_opname

let dest_collect t =
   dest_dep0_dep1_term collect_opname

(*
(************************************************************************
 * SMALL TACTICS                                                        *
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
            equal_small n thenLT [idT; addHiddenLabelT "wf"; addHiddenLabelT "wf"]
         else
            raise (RefineError ("d_small_typeT", StringTermError ("no rule applies", t)))
      in
         rule p

let d_resource = d_resource.resource_improve d_resource (small_type_term, d_small_typeT)

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
*)

(*
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
   get_tactic_arg p "memd"

let memdT p =
   (memd_of_proof p) p
*)

(************************************************************************
 * ISSET                                                                *
 ************************************************************************)

(*
 * Collect is a set.
 *)
let d_isset_genT tac i p =
   if i = 0 then
      let i = hyp_count p in
         try
            let arg = get_with_arg p in
            let i =
               try get_sel_arg p with
                  Not_found ->
                     1
            in
               if i > 1 then
                  isset_member i arg p
               else
                  isset_contains i arg p
         with
            Not_found ->
               tac i p
   else
      raise (RefineError ("d_issetT", StringError "no elimination rule for isset"))

let d_isset_varT i p =
   let tac i p =
      raise (RefineError ("d_issetT", StringError "use withT to provide an argument"))
   in
      d_isset_genT tac i p

let d_isset_collectT i p =
   let tac i p =
      let v = maybe_new_vars1 p "v" in
         isset_collect i v p
   in
      d_isset_genT tac i p

(*
 * Special case for collection.
 *)
let isset_collect_term = << isset{collect{'T; x. 'a['x]}} >>

let d_resource = d_resource.resource_improve d_resource (isset_term, d_isset_varT)
let d_resource = d_resource.resource_improve d_resource (isset_collect_term, d_isset_collectT)

(************************************************************************
 * OTHER TACTICS                                                        *
 ************************************************************************)

(*
 * H >- set type
 *)
let d_set_typeT i p =
   if i = 0 then
      set_type (Sequent.hyp_count p) p
   else
      raise (RefineError ("d_set_typeT", StringError "no elimination rule"))

let set_type_term = << "type"{set} >>

let d_resource = d_resource.resource_improve d_resource (set_type_term, d_set_typeT)

(*
 * H >- member{a; t} type
 *)
let d_member_typeT i p =
   if i = 0 then
      member_type (Sequent.hyp_count p) p
   else
      raise (RefineError ("d_member_typeT", StringError "no elimination rule"))

let member_type_term = << "type"{member{'a; 't}} >>

let d_resource = d_resource.resource_improve d_resource (member_type_term, d_member_typeT)

(*
 * Set elimination.
 *)
let d_setT i p =
   if i = 0 then
      raise (RefineError ("d_setT", StringTermError ("no formation rule", set_term)))
   else
      let v_a, _ = nth_hyp p i in
      let i, j = hyp_indices p i in
      let v_T, v_f, v_b = maybe_new_vars3 p "T" "f" "b" in
         set_elim i j v_a v_T v_f v_b p

let d_resource = d_resource.resource_improve d_resource (set_term, d_setT)

(*
 * Apply the type rule.
 *)
let wf_typeT p =
   wf_type (Sequent.hyp_count p) p

(*
 * Equal sets.
 *)
let eqSetT p =
   equal_set (hyp_count p) p

(*
 * Membership is equality.
 *)
let eqMemberT p =
   equal_member (hyp_count p) p

(*
 * Assumption.
 *)
let assumSetT i p =
   let i, j = hyp_indices p i in
      isset_assum i j p

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
