(*
 * Subtype type.
 *
 *)

open Debug
open Options
open Term
open Resource
open Term_dtable
open Refine_sig

open Var
     
include Itt_equal

(* debug_string DebugLoad "Loading itt_subtype..." *)

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare subtype{'A; 'B}

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform mode[prl] :: subtype{'A; 'B} = slot{'A} subseteq slot{'B}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext subtype(A; B)
 * by subtypeFormation
 * H >- Ui ext A
 * H >- Ui ext B
 *)
prim subtypeFormation 'H :
   ('A : sequent ['ext] { 'H >- univ[@i:l] }) -->
   ('B : sequent ['ext] { 'H >- univ[@i:l] }) -->
   sequent ['ext] { 'H >- univ[@i:l] } =
   subtype{'A; 'B}

(*
 * H >- subtype(A1; B1) = subtype(A2; B2) in Ui
 * by subtypeEquality
 *
 * H >- A1 = A2 in Ui
 * H >- B1 = B2 in Ui
 *)
prim subtypeEquality 'H :
   sequent [squash] { 'H >- 'A1 = 'A2 in univ[@i:l] } -->
   sequent [squash] { 'H >- 'B1 = 'B2 in univ[@i:l] } -->
   sequent ['ext] { 'H >- subtype{'A1; 'B1} = subtype{'A2; 'B2} in univ[@i:l] } =
   it

(*
 * H >- subtype(A; B) ext it
 * by subtype_axiomFormation
 *
 * H >- A = A in Ui
 * H; x: A; y: A; x = y in A >- x = y in B
 *)
prim subtype_axiomFormation 'H 'x :
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent [squash] { 'H; x: 'A >- 'x = 'x in 'B } -->
   sequent ['ext] { 'H >- subtype{'A; 'B} } =
   it

(*
 * H >- it = it in subtype(A; B)
 * by subtype_axiomEquality
 *
 * H >- subtype(A; B)
 *)
prim subtype_axiomEquality 'H :
   sequent [squash] { 'H >- subtype{'A; 'B} } -->
   sequent ['ext] { 'H >- it = it in subtype{'A; 'B} } =
   it

(*
 * H, x: subtype(A; B); J[x] >- C[x]
 * by subtypeElimination
 *
 * H, x: subtype(A; B); J[it] >- C[it]
 *)
prim subtypeElimination 'H 'J :
   ('t : sequent ['ext] { 'H; x: subtype{'A; 'B}; 'J[it] >- 'C[it] }) -->
   sequent ['ext] { 'H; x: subtype{'A; 'B}; 'J['x] >- 'C['x] } =
   't

(*
 * H >- x = y in B
 * by subtypeElimination2 A
 *
 * H >- x = y in A
 * H >- subtype(A; B)
 *)
prim subtypeElimination2 'H 'A :
   sequent [squash] { 'H >- 'x = 'y in 'A } -->
   sequent [squash] { 'H >- subtype{'A; 'B} } -->
   sequent ['ext] { 'H >- 'x = 'y in 'B } =
   it

(*
 * Squash elimination.
 *)
prim subtype_squashElimination 'H :
   sequent [squash] { 'H >- subtype{'A; 'B} } -->
   sequent ['ext] { 'H >- subtype{'A; 'B} } =
   it

(************************************************************************
 * PRIMITIVES                                                           *
 ************************************************************************)

let subtype_term = << subtype{'A; 'B} >>
let subtype_opname = opname_of_term subtype_term
let is_subtype_term = is_dep0_dep0_term subtype_opname
let dest_subtype = dest_dep0_dep0_term subtype_opname
let mk_subtype_term = mk_dep0_dep0_term subtype_opname

(************************************************************************
 * SUBTYPE RESOURCE                                                     *
 ************************************************************************)

(*
 * This is what is supplied to the resource.
 *)
type sub_info_type = (term * term) list * tactic

type sub_resource_info =
   LRSubtype of sub_info_type
 | RLSubtype of sub_info_type
 | DSubtype of sub_info_type

(*
 * Subtype resource is a DAG.
 *)
type sub_data = tactic term_dtable
     
(*
 * The resource itself.
 *)
resource (sub_resource_info, tactic, sub_data) sub_resource

(*
 * Improve the subtyping information.
 * We are provided with a (term * term) list
 * and a tactic, where the first term pair is the goal, the rest are
 * subgoals, and the supplied tactic should generate the subgoals
 * in order.
 *)
let subtype_f tac subgoals _ =
   let rec aux sg = function
      p::t ->
         let goal = concl p in
            if opname_of_term goal == subtype_opname then
               match sg with
                  (_, _, tac)::sg' -> (tac p)::(aux sg' t)
                | [] -> raise (RefineError (StringError "subtypeT: subtype mismatch"))
            else
               (idT p)::(aux sg t)
    | [] -> []
   in
      tac thenFLT aux subgoals

let improve_data base = function
   LRSubtype (goal, tac) ->
      insert_left base goal (subtype_f tac)
 | RLSubtype (goal, tac) ->
      insert_right base goal (subtype_f tac)
 | DSubtype (goal, tac) ->
      insert base goal (subtype_f tac)

(*
 * Extract a subtype tactic from the data.
 * Chain the tactics together.
 *)
let extract_data base =
   let tbl = extract base in
   let subtyper p =
      let t = concl p in
      let t1, t2 =
         try dest_subtype t with
            Term.TermMatch _ ->
               raise (RefineError (StringTermError ("subtype: should be subtype: ", t)))
      in
      let tac =
         try lookup tbl t1 t2 with
            Not_found ->
               raise (RefineError (StringTermError ("Can't infer subtype ", t)))
      in
         tac p
   in
      subtyper

(*
 * Wrap up the joiner.
 *)
let rec join_resource { resource_data = data1 } { resource_data = data2 } =
   { resource_data = join_tables data1 data2;
     resource_join = join_resource;
     resource_extract = extract_resource;
     resource_improve = improve_resource
   }
      
and extract_resource { resource_data = data } =
   extract_data data
   
and improve_resource { resource_data = data } arg =
   { resource_data = improve_data data arg;
     resource_join = join_resource;
     resource_extract = extract_resource;
     resource_improve = improve_resource
   }

(*
 * Resource.
 *)
let sub_resource =
   { resource_data = new_dtable ();
     resource_join = join_resource;
     resource_extract = extract_resource;
     resource_improve = improve_resource
   }

(*
 * Resource argument.
 *)
let subtyper_of_proof { tac_arg = { ref_rsrc = { ref_subtype = f } } } = f

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * D the conclusion.
 *)
let d_concl_subtype p =
   let count = hyp_count p in
   let x = maybe_new_var "x" (declared_vars p) in
      (subtype_axiomFormation count x
       thenLT [addHiddenLabelT "wf";
               addHiddenLabelT "aux"]) p

(*
 * D a hyp.
 * We take the argument.
 *)
let d_hyp_subtype i p =
   let count = hyp_count p in
   let i' = get_pos_hyp_index i count in
      subtypeElimination i' (count - i' - 1) p

(*
 * Join them.
 *)
let d_subtype i =
   if i = 0 then
      d_concl_subtype
   else
      d_hyp_subtype i

let d_resource = d_resource.resource_improve d_resource (subtype_term, d_subtype)

(*
 * EQCD.
 *)
let eqcd_subtype p =
   let count = hyp_count p in
      (subtypeEquality count
       thenT addHiddenLabelT "wf") p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (subtype_term, eqcd_subtype)

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of subtype.
 *)
let inf_subtype f decl t =
   let a, b = dest_subtype t in
   let decl', a' = f decl a in
   let decl'', b' = f decl' b in
   let le1, le2 =
      try dest_univ a', dest_univ b' with
         Term.TermMatch _ -> raise (RefineError (StringTermError ("typeinf: can't infer type for", t)))
   in
      decl'', Itt_equal.mk_univ_term (max_level_exp le1 le2)

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (subtype_term, inf_subtype)

(*
 * $Log$
 * Revision 1.3  1998/04/21 19:55:07  jyh
 * Upgraded refiner for program extraction.
 *
 * Revision 1.2  1997/08/06 16:18:45  jyh
 * This is an ocaml version with subtyping, type inference,
 * d and eqcd tactics.  It is a basic system, but not debugged.
 *
 * Revision 1.1  1997/04/28 15:52:29  jyh
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
 * Revision 1.4  1996/10/23 15:18:12  jyh
 * First working version of dT tactic.
 *
 * Revision 1.3  1996/05/21 02:17:18  jyh
 * This is a semi-working version before Wisconsin vacation.
 *
 * Revision 1.2  1996/04/11 13:34:21  jyh
 * This is the final version with the old syntax for terms.
 *
 * Revision 1.1  1996/03/30 01:37:21  jyh
 * Initial version of ITT.
 *
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
