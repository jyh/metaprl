(*
 * Equality type.
 *
 *)

include Tacticals
include Base_theory
include Itt_squash

open Printf
open Debug
open Opname
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermType
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan
open Refiner.Refiner.RefineError
open Rformat
open Simple_print
open Term_stable
open Resource

open Tacticals
open Sequent

(*
 * Show that the file is loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Itt_equal%t" eflush

let debug_eqcd =
   create_debug (**)
      { debug_name = "eqcd";
        debug_description = "display eqcd operations";
        debug_value = false
      }

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

prec prec_type
prec prec_equal

dform equal_df1 : parens :: "prec"[prec_equal] :: equal{'T; 'a; 'b} =
   szone pushm slot{'a} space `"= " slot{'b} space `"in " slot{'T} popm ezone
dform it_df1 : mode[prl] :: it = cdot

dform type_prl_df1 : parens :: "prec"[prec_type] :: mode[prl] :: "type"{'a} =
   slot{'a} " " `"Type"

mldform term_df2 : mode[prl] :: univ[@i:l] term_print buf =
   format_char buf '\134';
   format_simple_level_exp buf i

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Typehood is equality.
 *)
prim equalityAxiom 'H 'J : :
   sequent ['ext] { 'H; x: 'T; 'J['x] >- 'x = 'x in 'T } =
   it

(*
 * Reflexivity.
 *)
prim equalityRef 'H 'y :
   sequent ['ext] { 'H >- 'x = 'y in 'T } -->
   sequent ['ext] { 'H >- 'x = 'x in 'T } =
   it

(*
 * Symettry.
 *)
prim equalitySym 'H :
   sequent ['ext] { 'H >- 'y = 'x in 'T } -->
   sequent ['ext] { 'H >- 'x = 'y in 'T } =
   it

(*
 * Transitivity.
 *)
prim equalityTrans 'H 'z :
   sequent ['ext] { 'H >- 'x = 'z in 'T } -->
   sequent ['ext] { 'H >- 'z = 'y in 'T } -->
   sequent ['ext] { 'H >- 'x = 'y in 'T } =
   it

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
 * Typehood.
 *)
prim equalityType 'H :
   sequent [squash] { 'H >- 'a = 'a in 'T } -->
   sequent [squash] { 'H >- 'b = 'b in 'T } -->
   sequent ['ext] { 'H >- "type"{. 'a = 'b in 'T } } =
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
                | _ ->
                     raise (RefineError ("dest_level_param", TermMatchError (t, "param type")))
            end
       | { op_params = [] } ->
            raise (RefineError ("dest_level_param", TermMatchError (t, "no params")))
       | _ ->
            raise (RefineError ("dest_level_param", TermMatchError (t, "too many params")))

(* Cumulativity over universes *)
mlterm cumulativity{univ[@j:l]; univ[@i:l]} =
   let i = dest_level_param <:con< univ[@i:l] >> in
   let j = dest_level_param <:con< univ[@j:l] >> in
      if level_cumulativity j i then
         []
      else
         raise (RefineError ("cumulativity", StringError "failed"))

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

(*
 * Squash from any.
 *)
prim squashFromAny 'H 'ext :
   sequent ['ext] { 'H >- 'T } -->
   sequent [squash] { 'H >- 'T } =
   it

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

let type_term = << "type"{'t} >>
let type_opname = opname_of_term type_term
let is_type_term = is_dep0_term type_opname
let mk_type_term = mk_dep0_term type_opname
let dest_type_term = dest_dep0_term type_opname

let univ_term = << univ[@i:l] >>
let univ1_term = << univ[1:l] >>
let univ_opname = opname_of_term univ_term
let is_univ_term = TermOp.is_univ_term univ_opname
let dest_univ = TermOp.dest_univ_term univ_opname
let mk_univ_term = TermOp.mk_univ_term univ_opname

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
            if !debug_eqcd then
               eprintf "Itt_equal.eqcd: looking up %s%t" (Simple_print.string_of_opname (opname_of_term l)) eflush;
            let tac = slookup tbl l in
               if !debug_eqcd then
                  eprintf "Itt_equal.eqcd: found a tactic for %s%t" (Simple_print.string_of_opname (opname_of_term l)) eflush;
               tac p
         with
            Not_found ->
               raise (RefineError ("eqcd", StringTermError ("EQCD tactic doesn't know about ", l)))
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
let eqcdT p =
   Sequent.get_tactic_arg p "eqcd" p

(************************************************************************
 * D TACTIC                                                             *
 ************************************************************************)

(*
 * D tactic.
 *)
let d_equalT i p =
   if i = 0 then
      eqcdT p
   else
      let t = goal p in
      let count = num_hyps t in
         equalityElimination (i - 1) (count - i - 1) p

let d_resource = d_resource.resource_improve d_resource (equal_term, d_equalT)

(*
 * Typehood.
 *)
let d_equal_typeT i p =
   if i = 0 then
      equalityType (hyp_count p) p
   else
      raise (RefineError ("d_equal_typeT", StringError "no elimination form"))

let equal_type_term = << "type"{. 'a = 'b in 'T } >>

let d_resource = d_resource.resource_improve d_resource (equal_type_term, d_equal_typeT)

(*
 * Turn a eqcd tactic into a d tactic.
 *)
let d_wrap_eqcd eqcdT i p =
   if i = 0 then
      eqcdT p
   else
      d_equalT i p

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

let unsquashT v p =
   squashFromAny (Sequent.hyp_count p) v p

(************************************************************************
 * OTHER TACTICS                                                        *
 ************************************************************************)

(*
 * H, x:T, J >- x = x in T
 *)
let equalAssumT i p =
   let i, j = hyp_indices p i in
      equalityAxiom i j p

(*
 * Reflexivity.
 *)
let equalRefT t p =
   equalityRef (hyp_count p) t p

(*
 * Symettry.
 *)
let equalSymT p =
   equalitySym (hyp_count p) p

(*
 * Transitivity.
 *)
let equalTransT t p =
   equalityTrans (hyp_count p) t p

(*
 * $Log$
 * Revision 1.15  1998/07/02 18:37:30  jyh
 * Refiner modules now raise RefineError exceptions directly.
 * Modules in this revision have two versions: one that raises
 * verbose exceptions, and another that uses a generic exception.
 *
 * Revision 1.14  1998/07/01 04:37:37  nogin
 * Moved Refiner exceptions into a separate module RefineErrors
 *
 * Revision 1.13  1998/06/22 19:46:15  jyh
 * Rewriting in contexts.  This required a change in addressing,
 * and the body of the context is the _last_ subterm, not the first.
 *
 * Revision 1.12  1998/06/15 22:33:17  jyh
 * Added CZF.
 *
 * Revision 1.11  1998/06/12 13:47:26  jyh
 * D tactic works, added itt_bool.
 *
 * Revision 1.10  1998/06/09 20:52:33  jyh
 * Propagated refinement changes.
 * New tacticals module.
 *
 * Revision 1.9  1998/06/03 22:19:44  jyh
 * Nonpolymorphic refiner.
 *
 * Revision 1.8  1998/06/01 13:55:50  jyh
 * Proving twice one is two.
 *
 * Revision 1.7  1998/05/28 13:47:31  jyh
 * Updated the editor to use new Refiner structure.
 * ITT needs dform names.
 *
 * Revision 1.6  1998/04/24 02:43:26  jyh
 * Added more extensive debugging capabilities.
 *
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
