(*
 * This is the basic rewrite data type.
 * A file with this name is required for every theory.
 *)

include Perv

open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermAddr
open Refiner.Refiner.Refine

open Tactic_type
open Tacticals
open Var

(************************************************************************
 * TYPES                                                                *
 ************************************************************************)

(*
 * A conversion is wither a regular rewrite,
 * or a conditional rewrite, or a composition.
 *)
type t =
   Rewrite of rw
 | CondRewrite of cond_rewrite
 | Compose of conv * conv
 | Choice of conv * conv
 | Address of address * conv
 | Fold of term * conv
 | Cut of term
 | Identity

and env = tactic_arg * address

and conv = env -> t

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Justification for rewrites.
 *)
declare rewrite_just

(*
 * The basic rewrite axiom.
 * BUG: jyh: I don't know why we need the extra param here.
 *)
prim rewriteAxiom 'a : : "rewrite"{'x; 'x} = rewrite_just

(*
 * Sequent version of rewrite proposition.
 *)
prim rewriteSequentAxiom 'H : :
   sequent ['ext] { 'H >- "rewrite"{'x; 'x} } =
   rewrite_just

(*
 * Sequent replacement.
 *)
prim rewriteHypCut 'H 'J 'T1 :
   ('t : sequent ['ext] { 'H; x: 'T1; 'J['x] >- 'C['x] }) -->
   sequent ['ext] { 'H >- "rewrite"{'T1; 'T2} } -->
   sequent ['ext] { 'H; x: 'T2; 'J['x] >- 'C['x] } =
   't

prim rewriteConclCut 'H 'T1 :
   ('t : sequent ['ext] { 'H >- 'T1 }) -->
   sequent ['ext] { 'H >- "rewrite"{'T1; 'T2} } -->
   sequent ['ext] { 'H >- 'T2 } =
   't

prim rewriteContextCut 'H 'J (lambda{v. 'T['v]}) :
   ('t : "sequent"{'ext; ."context"[H:v]{'T["concl"{'C; ."concl"}]}}) -->
   "sequent"{'ext; ."context"[H:v]{."concl"{."rewrite"{.'T[rewrite_just]; ."context"[J:v]{rewrite_just}}; concl}}} -->
   "sequent"{'ext; ."context"[H:v]{."context"[J:v]{."concl"{'C; ."concl"}}}} =
   't

(************************************************************************
 * IMPLEMENTATION                                                       *
 ************************************************************************)

(*
 * Get the term of the environment.
 *)
let env_term (arg, addr) =
   term_subterm (Sequent.goal arg) addr

(*
 * Get the sequent that we are matching against.
 *)
let env_goal (arg, _) =
   Sequent.goal arg

(*
 * Create a conversion from a basic rewrite.
 * This function is required by filter_prog.
 *)
let rewrite_of_rewrite rw (_, addr) =
   Rewrite (rwaddr addr rw)

(*
 * Create a conversion from a conditional rewrite.
 * This function is required by filter_prog.
 *)
let rewrite_of_cond_rewrite crw args (_, addr) =
   CondRewrite (crwaddr addr (crw args))

(*
 * Composition.
 *)
let prefix_andthenC conv1 conv2 =
   let conv = Compose (conv1, conv2) in
      (fun _ -> conv)

let prefix_orelseC conv1 conv2 =
   let conv = Choice (conv1, conv2) in
      (fun _ -> conv)

(*
 * No action.
 *)
let idC _ =
   Identity

(*
 * Apply the conversion at the specified address.
 *)
let addrC addr conv =
   let conv = Address (make_address addr, conv) in
      (fun _ -> conv)

(*
 * Reverse the conversion at the specified address.
 *)
let foldC t conv =
   let conv = Fold (t, conv) in
      (fun _ -> conv)

(*
 * Cut just replaces the term an generates a rewrite
 * subgoal.
 *)
let cutC t =
   let conv = Cut t in
      (fun _ -> conv)

(*
 * Apply cut sequent rule.
 * We have three cases:
 *    1. The replacement is in a hyp
 *    2. The replacement is in a hyp context
 *    3. The replacement is in the concl
 *)
let rewrite_just_term = << rewrite_just >>

let cutT i addr t p =
   if i = 0 then
      let t2 = Sequent.concl p in
      let j = Sequent.hyp_count p in
      let t1 = replace_subterm t2 addr t in
      let i = Sequent.hyp_count p in
         rewriteConclCut i t1 p
   else
      let goal = Sequent.goal p in
      let caddr = Sequent.clause_addr p i in
      let clause = term_subterm goal caddr in
         if is_context_term clause then
            let v = maybe_new_vars1 p "v" in
            let vt = mk_var_term v in
            let name, arg, args = dest_context clause in
            let t1 = mk_context_term name vt args in
            let t1 = replace_subterm t1 addr t in
            let t1 = mk_xlambda_term v t1 in
            let count = Sequent.hyp_count p in
            let i, j =
               if i < 0 then
                  count + i, -i
               else
                  i - 1, count - i + 1
            in
               rewriteContextCut i j t1 p
         else
            let _, t1 = Sequent.nth_hyp p i in
            let i, j = Sequent.hyp_indices p i in
            let t1 = replace_subterm t1 addr t in
               rewriteHypCut i j t1 p

(*
 * Apply axiom rule.
 *)
let rwAxiomT =
   rewriteAxiom << "string"["bogus argument"] >>

(*
 * Apply sequent axiom rule.
 *)
let rwSeqAxiomT p =
   rewriteSequentAxiom (Sequent.hyp_count p) p

(*
 * Apply the rewrite.
 *)
let rw conv i p =
   (*
    * root: address of the clause
    * rel: offset into the term
    * addr: compose_addrress root rel
    *)
   let rec apply i rel addr conv p =
      match conv (p, addr) with
         Rewrite rw ->
            tactic_of_rewrite rw p
       | CondRewrite crw ->
            tactic_of_cond_rewrite crw p
       | Compose (conv1, conv2) ->
            let tac1 p = apply i rel addr conv1 p in
            let tac2 p = apply i rel addr conv2 p in
               (tac1 then_OnFirstT tac2) p
       | Choice (conv1, conv2) ->
            let tac1 p = apply i rel addr conv1 p in
            let tac2 p = apply i rel addr conv2 p in
               (tac1 orelseT tac2) p
       | Address (addr', conv) ->
            let rel = compose_address rel addr' in
            let addr = compose_address addr addr' in
               apply i rel addr conv p
       | Identity ->
            idT p
       | Fold (t, conv) ->
            (cutT i rel t thenLT [idT; solveCutT i rel conv]) p
       | Cut t ->
            cutT i rel t p

   and solveCutT i rel conv p =
      let rel = compose_address (make_address [1]) rel in
      let root = Sequent.clause_addr p 0 in
      let addr = compose_address root rel in
         (apply i rel addr conv thenT rwSeqAxiomT) p
   in
   let addr = Sequent.clause_addr p i in
      apply i (make_address []) addr conv p

(*
 * $Log$
 * Revision 1.3  1998/06/22 20:01:43  jyh
 * Fixed syntax error in term_addr_gen.ml
 *
 * Revision 1.2  1998/06/22 19:46:43  jyh
 * Rewriting in contexts.  This required a change in addressing,
 * and the body of the context is the _last_ subterm, not the first.
 *
 * Revision 1.1  1998/06/03 22:19:55  jyh
 * Nonpolymorphic refiner.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
