(*
 * Strutural rules.
 *
 *)

include Options

include Itt_equal

open Printf
open Debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineErrors

open Tactic_type
open Sequent
open Options
open Tacticals
open Itt_equal

(*
 * Show that the file is loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Itt_struct%t" eflush

(* debug_string DebugLoad "Loading itt_struct..." *)

(*
 * This is just syntax for a binding term.
 * It has no semantic meaning in the type theory.
 *)
declare bind{x. 'T['x]}

(*
 * H; x: A; J >- A ext x
 * by hypothesis
 *)
prim hypothesis 'H 'J 'x : :
   sequent ['ext] { 'H; x: 'A; 'J['x] >- 'A } = 'x

(*
 * H, x: A, J >- A ext t
 * by thin
 * H, J >- A ext t
 *)
prim thin 'H 'J :
   ('t : sequent ['ext] { 'H; 'J >- 'C }) -->
   sequent ['ext] { 'H; x: 'A; 'J >- 'C } =
   't

(*
 * H, J >- T ext t[s]
 * by cut S
 * H, J >- S ext s
 * H, x: S, J >- T ext t[x]
 *)
prim cut 'H 'J 'S 'x :
   ('s : sequent ['ext] { 'H; 'J >- 'S }) -->
   ('t['x] : sequent ['ext] { 'H; x: 'S; 'J >- 'T }) -->
   sequent ['ext] { 'H; 'J >- 'T } =
   't['s]

(*
 * H >- T
 * by introduction t
 * H >- t = t in T
 *)
prim introduction 'H 't :
   sequent [squash] { 'H >- 't = 't in 'T } -->
   sequent ['ext] { 'H >- 'T } =
   't

(*
 * H >- T1[t1] ext t
 * by substitution (t1 = t2 in T2) lambda(x. T1[x])
 * H >- t1 = t2 in T2
 * H >- T1[t2] ext t
 * H, x: T2 >- T1[x] = T1[x] in type
 *)
prim substitution 'H ('t1 = 't2 in 'T2) bind{x. 'T1['x]} :
   sequent [squash] { 'H >- 't1 = 't2 in 'T2 } -->
   ('t : sequent ['ext] { 'H >- 'T1['t2] }) -->
   sequent [squash] { 'H; x: 'T2 >- "type"{'T1['x]} } -->
   sequent ['ext] { 'H >- 'T1['t1] } =
   't

(*
 * H, x: A, J >- T ext t
 * by hypothesesReplacement B
 * H, x:B, J >- T ext t
 * H, x: A, J >- A = B in type
 *)
prim hypReplacement 'H 'J 'B univ[@i:l] :
   ('t : sequent ['ext] { 'H; x: 'B; 'J['x] >- 'T['x] }) -->
   sequent [squash] { 'H; x: 'A; 'J['x] >- 'A = 'B in univ[@i:l] } -->
   sequent ['ext] { 'H; x: 'A; 'J['x] >- 'T['x] } =
   't

(*
 * H; x: A[t1]; J[x] >> T1[x] ext t
 * by hypSubstitution (t1 = t2 in T2) bind(x. A[x])
 * H; x: A[t1]; J[x] >> t1 = t2 in T2
 * H; x: A[t2]; J[x] >> T1[x]
 * H, x: A[t1]; J[x]; z: T2 >> A[z] in type
 *)
prim hypSubstitution 'H 'J ('t1 = 't2 in 'T2) bind{y. 'A['y]} 'z :
   sequent [squash] { 'H; x: 'A['t1]; 'J['x] >- 't1 = 't2 in 'T2 } -->
   sequent ['prop] { 'H; x: 'A['t2]; 'J['x] >- 'T1['x] } -->
   sequent [squash] { 'H; x: 'A['t1]; 'J['x]; z: 'T2 >- 'A['z] } -->
   sequent ['prop] { 'H; x: 'A['t1]; 'J['x] >- 'T1['x] } =
   it

(*
 * We don't really need this a s a rule, but it
 * is used often.
 *
 * H >> a = b in T
 * by swapEquands
 * H >> b = a in T
 *)
prim swapEquands 'H :
   sequent [squash] { 'H >- 'b = 'a in 'T } -->
   sequent ['ext] { 'H >- 'a = 'b in 'T } =
   it

(************************************************************************
 * PRIMITIVES                                                           *
 ************************************************************************)

let bind_term = << bind{x. 'T['x]} >>
let bind_opname = opname_of_term bind_term
let is_bind_term = is_dep1_term bind_opname
let dest_bind = dest_dep1_term bind_opname
let mk_bind_term = mk_dep1_term bind_opname

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Prove by hypothesis.
 *)
let nthHypT i p =
   let x, _ = nth_hyp p i in
   let i, j = hyp_indices p i in
      hypothesis i j x p

(*
 * Thin a hyp.
 * Check that this doesn't introduce a free variable
 * (although the rule is still valid otherwise).
 *)
let thinT i p =
   let x, _ = nth_hyp p i in
   let i, j = hyp_indices p i in
      if is_free_seq_var (i + 1) x p then
         raise (RefineError ("thinT", StringStringError ("free variable: ", x)))
      else
         thin i j p

(*
 * Cut rule.
 *)
let assertT s p =
   let count = hyp_count p in
   let v = get_opt_var_arg "x" p in
      (cut count 0 s v
       thenLT [addHiddenLabelT "assertion"; idT]) p

(*
 * Cut in at a certain point.
 *)
let assertAtT i s p =
   let i, j = hyp_indices p i in
   let v = get_opt_var_arg "x" p in
      (cut i j s v
       thenLT [addHiddenLabelT "assertion"; idT]) p

(*
 * Explicit extract.
 *)
let useWitnessT t p =
   let count = hyp_count p in
      introduction count t p

(*
 * Swap the equands.
 *)
let swapEquandsT p =
   swapEquands (hyp_count p) p

(*
 * Substitution.
 * The binding term may be optionally supplied.
 *)
let substConclT t p =
   let _, a, _ =
      try dest_equal t with
         Term.TermMatch _ -> raise (RefineError ("substT", StringTermError ("arg should be an equality: ", t)))
   in
   let bind =
      try
         let t1 = get_with_arg p in
            if is_bind_term t1 then
               t1
            else
               raise (RefineError ("substT", StringTermError ("need a \"bind\" term: ", t)))
      with
         Not_found ->
            let x = get_opt_var_arg "z" p in
               mk_bind_term x (var_subst (concl p) a x)
   in
      (substitution (hyp_count p) t bind
       thenLT [addHiddenLabelT "equality";
               addHiddenLabelT "main";
               addHiddenLabelT "aux"]) p

(*
 * Hyp substitution requires a replacement.
 *)
let substHypT i t p =
   let _, a, _ =
      try dest_equal t with
         Term.TermMatch _ ->
            raise (RefineError ("substT", StringTermError ("arg should be an equality: ", t)))
   in
   let _, t1 = Sequent.nth_hyp p i in
   let z = get_opt_var_arg "z" p in
   let bind =
      try
         let b = get_with_arg p in
            if is_bind_term b then
               b
            else
               raise (RefineError ("substT", StringTermError ("need a \"bind\" term: ", b)))
      with
         Not_found ->
            mk_bind_term z (var_subst t1 a z)
   in
   let i, j = hyp_indices p i in
      (hypSubstitution i j t bind z
       thenLT [addHiddenLabelT "equality";
               addHiddenLabelT "main";
               addHiddenLabelT "aux"]) p

(*
 * General substition.
 *)
let substT i =
   if i = 0 then
      substConclT
   else
      substHypT i

(*
 * Derived versions.
 *)
let hypSubstT i p =
   let _, h = Sequent.nth_hyp p i in
      (substT i h thenET nthHypT i) p

let revHypSubstT i p =
   let t, a, b = dest_equal (snd (Sequent.nth_hyp p i)) in
   let h' = mk_equal_term t b a in
      (substT i h' thenET (swapEquandsT thenT nthHypT i)) p

(*
 * $Log$
 * Revision 1.12  1998/07/01 04:37:50  nogin
 * Moved Refiner exceptions into a separate module RefineErrors
 *
 * Revision 1.11  1998/06/23 22:12:37  jyh
 * Improved rewriter speed with conversion tree and flist.
 *
 * Revision 1.10  1998/06/22 19:46:24  jyh
 * Rewriting in contexts.  This required a change in addressing,
 * and the body of the context is the _last_ subterm, not the first.
 *
 * Revision 1.9  1998/06/12 13:47:40  jyh
 * D tactic works, added itt_bool.
 *
 * Revision 1.8  1998/06/09 20:52:46  jyh
 * Propagated refinement changes.
 * New tacticals module.
 *
 * Revision 1.7  1998/06/01 13:56:24  jyh
 * Proving twice one is two.
 *
 * Revision 1.6  1998/05/28 13:48:11  jyh
 * Updated the editor to use new Refiner structure.
 * ITT needs dform names.
 *
 * Revision 1.5  1998/04/24 02:43:50  jyh
 * Added more extensive debugging capabilities.
 *
 * Revision 1.4  1998/04/22 22:45:17  jyh
 * *** empty log message ***
 *
 * Revision 1.3  1997/08/06 16:33:11  jyh
 * Minor changes.
 *
 * Revision 1.2  1997/08/06 16:18:44  jyh
 * This is an ocaml version with subtyping, type inference,
 * d and eqcd tactics.  It is a basic system, but not debugged.
 *
 * Revision 1.1  1997/04/28 15:52:28  jyh
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
 * Revision 1.3  1996/05/21 02:17:14  jyh
 * This is a semi-working version before Wisconsin vacation.
 *
 * Revision 1.2  1996/04/11 13:34:18  jyh
 * This is the final version with the old syntax for terms.
 *
 * Revision 1.1  1996/03/30 01:37:20  jyh
 * Initial version of ITT.
 *
 * Revision 1.1  1996/03/28 02:51:33  jyh
 * This is an initial version of the type theory.
 *
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
