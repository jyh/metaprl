(*
 * Equality type.
 *
 *)

include Tactic_type
include Base_theory
include Itt_squash

open Debug
open Opname
open Term
open Rformat
open Simple_print
open Term_stable
open Refine_sig
open Resource

open Tactic_type
open Sequent

(* debug_string DebugLoad "Loading itt_equal..." *)

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "type"{'a}
declare univ[@i:l]
declare equal{'T; 'a; 'b}
declare it

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform equal{'T; 'a; 'b} =
   szone pushm slot{'a} space `"= " slot{'b} space `"in " slot{'T} popm ezone
dform mode[prl] :: it = cdot

dform mode[prl] :: "type" = `"Type"

mldform mode[prl] :: univ[@i:l] term_print buf =
   format_char buf '\134';
   format_simple_level_exp buf i

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext a = b in T
 * by equalityFormation T
 *
 * H >- T ext a
 * H >- T ext b
 *)
prim equalityFormation 'H 'T :
   ('a : sequent ['ext] { 'H >- 'T }) -->
   ('b : sequent ['ext] { 'H >- 'T }) -->
   sequent ['ext] { 'H >- univ[@i:l] } =
   'a = 'b in 'T

(*
 * H >- (a1 = b1 in T1) = (a2 = b2 in T2)
 * by equalityEquality
 *
 * H >- T1 = T2 in Ui
 * H >- a1 = a2 in T1
 * H >- b1 = b2 in T1
 *)
prim equalityEquality 'H :
   sequent [squash] { 'H >- 'T1 = 'T2 in univ[@i:l] }
   sequent [squash] { 'H >- 'a1 = 'a2 in 'T1 }
   sequent [squash] { 'H >- 'b1 = 'b2 in 'T2 } :
   sequent ['ext] { 'H >- ('a1 = 'b1 in 'T1) = ('a2 = 'b2 in 'T2) in univ[@i:l] } =
   it

(*
 * H >- it = it in (a = b in T)
 * by axiomEquality
 *
 * H >- a = b in T
 *)
prim axiomEquality 'H : 
   sequent [squash] { 'H >- 'a = 'b in 'T } :
   sequent ['ext] { 'H >- it = it in ('a = 'b in 'T) } =
   it

(*
 * H, x: a = b in T, J[x] >- C[x]
 * by equalityElimination i
 *
 * H, x: a = b in T; J[it] >- C[it]
 *)
prim equalityElimination 'H 'J :
   ('t : sequent ['ext] { 'H; x: 'a = 'b in 'T; 'J[it] >- 'C[it] }) :
   sequent ['ext] { 'H; x: 'a = 'b in 'T; 'J['x] >- 'C['x] } =
   't

(*
 * H >- T = T in type
 * by typeEquality
 *
 * H >- T
 *)
prim typeEquality 'H :
   sequent [squash] { 'H >- 'T } :
   sequent ['ext] { 'H >- "type"{'T} } =
   it

(*
 * Squash elim.
 *)
prim equality_squashElimination 'H :
   sequent [squash] { 'H >- 'a = 'b in 'T } -->
   sequent ['ext] { 'H >- 'a = 'b in 'T } =
   it

(*
 * There should be only one param, of String type.
 * Get it. 
 *)
let dest_level_param t =
   let { term_op = op } = dest_term t in
      match dest_op op with 
         { op_params = [param] } ->
            begin
               match dest_param param with
                  Level s -> s
                | _ -> raise (TermMatch ("dest_level_param", t, "param type"))
            end
       | { op_params = [] } ->
            raise (TermMatch ("dest_level_param", t, "no params"))
       | _ ->
            raise (TermMatch ("dest_level_param", t, "too many params"))

(* Cumulativity over universes *)
mlterm cumulativity{univ[@j:l]; univ[@i:l]} =
   let i = dest_level_param <:con< univ[@i:l] >> in
   let j = dest_level_param <:con< univ[@j:l] >> in
      if level_cumulativity j i then
         []
      else
         raise (RefineError (StringError "cumulativity"))

 | fun _ extracts ->
      << it >>, extracts

(*
 * H >- Uj = Uj in Ui
 * by universeEquality (side (j < i))
 *)
prim universeEquality 'H :
   cumulativity{univ[@j:l]; univ[@i:l]} :
   sequent ['ext] { 'H >- univ[@j:l] = univ[@j:l] in univ[@i:l] } =
  it

(*
 * H >- Ui ext Uj
 * by universeFormation
 *)
prim universeFormation 'H univ[@j:l] : 
   cumulativity{univ[@j:l]; univ[@i:l]} :
   sequent ['ext] {'H >- univ[@i:l] } =
   univ[@j:l]

(************************************************************************
 * PRIMITIVES                                                           *
 ************************************************************************)

(*
 * Primitives.
 *)
let equal_term = << 'a = 'b in 'c >>
let equal_opname = opname_of_term equal_term
let is_equal_term = is_dep0_dep0_dep0_term equal_opname
let dest_equal = dest_dep0_dep0_dep0_term equal_opname
let mk_equal_term = mk_dep0_dep0_dep0_term equal_opname

let univ_term = << univ[@i:l] >>
let univ1_term = << univ[1:l] >>
let univ_opname = opname_of_term univ_term
let is_univ_term = Term.is_univ_term univ_opname
let dest_univ = Term.dest_univ_term univ_opname
let mk_univ_term = Term.mk_univ_term univ_opname

let it_term = << it >>

(************************************************************************
 * EQCD TACTIC                                                          *
 ************************************************************************)

(*
 * EQCD resource.
 * Use simple table.
 *)
type eqcd_data = tactic term_stable

resource (term * tactic, tactic, eqcd_data) eqcd_resource

(*
 * Extract an EQCD tactic from the data.
 * The tactic checks for an optable.
 *)
let extract_data base =
   let tbl = sextract base in
   let eqcd p =
      let t = concl p in
      let _, l, _ = dest_equal t in
         try
            (* Find and apply the right tactic *)
            let tac = slookup tbl l in
               tac p
         with
            Not_found ->
               raise (RefineError (StringTermError ("EQCD tactic doesn't know about ", l)))
   in
      eqcd

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
let eqcd_resource =
   { resource_data = new_stable ();
     resource_join = join_resource;
     resource_extract = extract_resource;
     resource_improve = improve_resource
   }

(*
 * Resource argument.
 *)
let eqcd_of_proof { tac_arg = { ref_rsrc = { ref_eqcd = eqcd } } } = eqcd

(************************************************************************
 * D TACTIC                                                             *
 ************************************************************************)

(*
 * D tactic.
 *)
let d_equalT i p =
   if i = 0 then
      (eqcd_of_proof p) p
   else
      let t = goal p in
      let count = num_hyps t in
         equalityElimination (i - 1) (count - i - 1) p

let d_resource = d_resource.resource_improve d_resource (equal_term, d_equalT)

(************************************************************************
 * EQCD                                                                 *
 ************************************************************************)

(*
 * EQCD tactic.
 *)
let eqcd_univT p =
   universeEquality (hyp_count p) p

let eqcd_itT p =
   axiomEquality (hyp_count p) p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (univ_term, eqcd_univT)
let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (it_term, eqcd_itT)

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of a universe is incremented by one.
 *)
let inf_univ _ decl t =
   let le = dest_univ t in
      decl, mk_univ_term (incr_level_exp le)

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (univ_term, inf_univ)

(*
 * Type of an equality is the type of the equality type.
 *)
let inf_equal inf decl t =
   let ty, _, _ = dest_equal t in
      inf decl ty

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (equal_term, inf_equal)

(************************************************************************
 * SQUASH STABILITY                                                     *
 ************************************************************************)

(*
 * Equality is squash stable.
 *)
let squash_equalT p =
   equality_squashElimination (hyp_count p) p

let squash_resource = squash_resource.resource_improve squash_resource (equal_term, squash_equalT)

(*
 * $Log$
 * Revision 1.5  1998/04/22 22:44:43  jyh
 * *** empty log message ***
 *
 * Revision 1.4  1998/04/21 19:54:47  jyh
 * Upgraded refiner for program extraction.
 *
 * Revision 1.3  1998/04/09 18:26:03  jyh
 * Working compiler once again.
 *
 * Revision 1.2  1997/08/06 16:18:26  jyh
 * This is an ocaml version with subtyping, type inference,
 * d and eqcd tactics.  It is a basic system, but not debugged.
 *
 * Revision 1.1  1997/04/28 15:52:10  jyh
 * This is the initial checkin of Nuprl-Light.
 * I am porting the editor, so it is not included
 * in this checkin.
 *
 * Directories:
 *     refiner: logic engine
 *     filter: front end to the Ocaml compiler
 *     editor: Emacs proof editor
 *     util: utilities
 *     mk: Makefile templates
 *
 * Revision 1.7  1996/10/23 15:18:06  jyh
 * First working version of dT tactic.
 *
 * Revision 1.6  1996/09/25 22:52:11  jyh
 * Initial "tactical" commit.
 *
 * Revision 1.5  1996/09/02 19:37:21  jyh
 * Semi working package management.
 * All _univ version removed.
 *
 * Revision 1.4  1996/05/21 02:16:43  jyh
 * This is a semi-working version before Wisconsin vacation.
 *
 * Revision 1.3  1996/04/11 13:33:57  jyh
 * This is the final version with the old syntax for terms.
 *
 * Revision 1.2  1996/03/28 02:51:29  jyh
 * This is an initial version of the type theory.
 *
 * Revision 1.1  1996/03/05 19:59:42  jyh
 * Version just before LogicalFramework.
 *
 * Revision 1.1  1996/02/13 21:35:58  jyh
 * Intermediate checkin while matching is bing added to the refiner.
 *
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
