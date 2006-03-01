doc <:doc<
   @module[Itt_dfun]

   The @tt[Itt_dfun] module defines the type <<x:'A -> 'B['x]>> of
   dependent functions.

   @docoff
   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 1998-2005 MetaPRL Group, Cornell University and Caltech

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License
   as published by the Free Software Foundation; either version 2
   of the License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

   Author: Jason Hickey @email{jyh@cs.cornell.edu}
   Modified By: Alexei Kopylov @email{kopylov@cs.caltech.edu}
                Aleksey Nogin @email{nogin@cs.caltech.edu}
   @end[license]
>>

doc <:doc<
   @parents
>>
extends Itt_equal
extends Itt_struct
extends Itt_set
extends Itt_void
extends Itt_unit
doc docoff

open Lm_debug
open Lm_printf

open Basic_tactics
open Unify_mm

open Itt_equal
open Itt_subtype

declare "fun"{'A; x. 'B['x]}

declare lambda{x. 'b['x]}
declare apply{'f; 'a}

define unfold_ycomb: ycomb <--> lambda{h. lambda{x. 'h ('x 'x)} lambda{x. 'h ('x 'x)}}

define unfold_fix: fix{f. 'b['f]} <--> ycomb (lambda{f. 'b['f]})

define unfold_let : "let"{'a;x.'b['x]} <--> (lambda{x.'b['x]} 'a)

doc docoff

let fold_ycomb = makeFoldC << ycomb >> unfold_ycomb
let fold_fix = makeFoldC << fix{f. 'b['f]} >> unfold_fix

(*
 * Primitives.
 *)
let lambda_term = << lambda{x. 'b['x]} >>
let lambda_opname = opname_of_term lambda_term
let is_lambda_term = is_dep1_term lambda_opname
let dest_lambda = dest_dep1_term lambda_opname
let mk_lambda_term = mk_dep1_term lambda_opname

let fix_term = << fix{x. 'b['x]} >>
let fix_opname = opname_of_term fix_term
let is_fix_term = is_dep1_term fix_opname
let dest_fix = dest_dep1_term fix_opname
let mk_fix_term = mk_dep1_term fix_opname

let apply_term = << apply{'f; 'a} >>
let apply_opname = opname_of_term apply_term
let is_apply_term = is_dep0_dep0_term apply_opname
let dest_apply = dest_dep0_dep0_term apply_opname
let mk_apply_term = mk_dep0_dep0_term apply_opname

let dfun_term = << x: 'A -> 'B['x] >>
let dfun_opname = opname_of_term dfun_term
let is_dfun_term = is_dep0_dep1_term dfun_opname
let dest_dfun = dest_dep0_dep1_term dfun_opname
let mk_dfun_term = mk_dep0_dep1_term dfun_opname

let empty_var = Lm_symbol.add ""
let mk_fun_term t1 t2 =
   let v = maybe_new_var_set empty_var (free_vars_set t2) in
      mk_dfun_term v t1 t2

let is_fun_term t =
   is_dfun_term t &&
      let v, t1, t2 = dest_dfun t in
         not (SymbolSet.mem (free_vars_set t2) v)

let dest_fun t =
      let v, t1, t2 = dest_dfun t in
         if SymbolSet.mem (free_vars_set t2) v then
            raise (RefineError("Itt_dfun.dest_fun",StringTermError("The function term is a dependent function", t)))
         else
            t1, t2

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

prec prec_fun
prec prec_apply
prec prec_lambda
prec prec_lambda < prec_apply
prec prec_fun < prec_apply
prec prec_fun < prec_lambda

declare declaration{'decl : Dform ;'term : Dform } : Dform

dform decl_df : declaration{'decl;'a}
   = 'decl `" = " slot{'a}

dform decl_df : except_mode [src] :: declaration{'decl;lambda{x.'a}}
   = declaration{math_apply{'decl; 'x};'a}

dform decl_df : except_mode [src] :: declaration{'decl;fix{f.'a['f :> Dform]}}
   = declaration{'decl; 'a['decl]}

dform fun_df : "fun"{'A; x. 'B} = math_fun[x]{'A; 'B}

dform apply_df : parens :: "prec"[prec_apply] :: apply{'f; 'a} =
   slot["lt"]{'f} " " slot["le"]{'a}

dform lambda_df : parens :: except_mode [src] :: "prec"[prec_lambda] :: lambda{x. 'b} =
   Mpsymbols!lambda slot{'x} `"." slot{'b}

dform ycomb_df : except_mode[src] :: ycomb = Mpsymbols!mathbbY

dform fix_df : except_mode[src] :: fix{f. 'b} =
   `"fix" `"(" slot{'f} `"." slot{'b} `")"

dform let_df : "let"{'a;x.'b} =
     szone pushm[3]  `"let " szone{declaration{'x;'a}} `" in" hspace
     szone{'b} popm ezone

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

doc <:doc<
   @rewrites

   The @tt{reduce_beta} rewrite defines normal beta-reduction.
   The @tt{reduce_fix} rewrite defines reduction on the fixpoint
   combinator.  The @tt{reduce_fix} rewrite can be derived by defining
   the $Y$-combinator $Y @equiv @lambda f. @lambda x. (f@space (x@space x))@space (f@space (x@space x))$
   and defining $@fix{x; b[x]} @equiv Y@space (<<lambda{x.'b['x]}>>)$.
>>

prim_rw reduce_beta {| reduce |} : (lambda{v. 'b['v]} 'a) <--> 'b['a]
interactive_rw reduce_let {| reduce |} : ("let"{'a;x.'b['x]}) <--> 'b['a]

interactive_rw reduce_ycomb : (ycomb 'x) <--> ('x (ycomb 'x))

interactive_rw reduce_fix : fix{f. 'b['f]} <--> 'b[fix{f. 'b['f]}]

doc docoff

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

doc rules

(*
 * @modsubsection{Typehood and equality}
 *
 * The dependent-function space retains the intensional type
 * equality of the very-dependent type.
 *)
prim functionEquality {| intro [] |} :
   [wf] sequent { <H> >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent { <H>; a1: 'A1 >- 'B1['a1] = 'B2['a1] in univ[i:l] } -->
   sequent { <H> >- (a1:'A1 -> 'B1['a1]) = (a2:'A2 -> 'B2['a2]) in univ[i:l] }
   = it

(*
 * Typehood.
 *)
prim functionType {| intro [] |} :
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H>; a: 'A >- "type"{'B['a]} } -->
   sequent { <H> >- "type"{ a:'A -> 'B['a] } }
   = it

doc <:doc<
   @modsubsection{Introduction}

   The propositional interpretation of the dependent-function
   is the universal quantification @hrefterm[all], $@all{a; A; B[a]}$.  The
   universal quantification is true, if it is a type,
   and $B[a]$ is true for any $a @in A$.
>>
prim lambdaFormation {| intro [] |} :
   [wf] sequent { <H> >- "type"{'A} } -->
   [main] ('b['a] : sequent { <H>; a: 'A >- 'B['a] }) -->
   sequent { <H> >- a:'A -> 'B['a] }
   = lambda{a.'b['a]}

doc <:doc<
   @modsubsection{Membership}

   The dependent function space contains the @hrefterm[lambda] functions.
>>
prim lambdaEquality {| intro [] |} :
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H>; a1: 'A >- 'b1['a1] = 'b2['a1] in 'B['a1] } -->
   sequent { <H> >- lambda{a1. 'b1['a1]} = lambda{a2. 'b2['a2]} in a:'A -> 'B['a] }
   = it

doc <:doc<
   @modsubsection{Extensionality}

   The function space is one of the few types in the @Nuprl type
   theory with an @emph{extensional} equality.  Normally, equality is
   intensional --- it depends on the syntactic structure of the
   terms in the type.  The function space allows equality of functions
   $f_1$ and $f_2$ if their @emph{application} provides equal values on
   equal arguments.  The functions and the function type must all be
   well-formed (and in fact, this implicitly requires that $f_1$ and
   $f_2$ both be @tt{lambda} terms).
>>
prim functionExtensionality (y:'C -> 'D['y]) (z:'E -> 'F['z]) :
   [main] sequent { <H>; x: 'A >- ('f 'x) = ('g 'x) in 'B['x] } -->
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H> >- 'f in y:'C -> 'D['y] } -->
   [wf] sequent { <H> >- 'g in z:'E -> 'F['z] } -->
   sequent { <H> >- 'f = 'g in x:'A -> 'B['x] }
   = it

doc <:doc<
   @modsubsection{Elimination}

   The elimination rule @emph{instantiates} the function
   $f@colon <<x:'A -> 'B['x]>>$ with an argument $a @in A$, to
   obtain a proof of $B[a]$. The second form, @tt[independentFunctionElimination],
   is more appropriate for the propositional interpretation of the function
   space <<'A -> 'B>>: if there is a proof of $A$, then there is also a proof
   of $B$.
>>
prim functionElimination {| elim [] |} 'H 'a :
   [wf] sequent { <H>; f: x:'A -> 'B['x]; <J['f]> >- 'a in 'A } -->
   ('t['f; 'y; 'it] : sequent { <H>; f: x:'A -> 'B['x]; <J['f]>; y: 'B['a]; it: 'y = ('f 'a) in 'B['a] >- 'T['f] }) -->
   sequent { <H>; f: x:'A -> 'B['x]; <J['f]> >- 'T['f] }
   = 't['f; 'f 'a; it]

interactive independentFunctionElimination 'H :
   [assertion] sequent { <H>; f: 'A -> 'B; <J['f]> >- 'A } -->
   [main] sequent { <H>; f: 'A -> 'B; <J['f]>; y: 'B >- 'T['f] } -->
   sequent { <H>; f: 'A -> 'B; <J['f]> >- 'T['f] }

doc docoff
let d_hyp_fun = argfunT (fun i p ->
   try
      let a = get_with_arg p in
         functionElimination i a
   with
      RefineError _ ->
         independentFunctionElimination i)

let resource elim += (dfun_term, wrap_elim d_hyp_fun)

doc <:doc<
   @modsubsection{Combinator equality}

   Applications have (at least) an @emph{intensional} equality; they are
   equal if their functions and arguments are equal.
>>

prim applyEquality {| intro[intro_typeinf <<'f1>>; complete_unless_member] |} (x:'A -> 'B['x]) :
   sequent { <H> >- 'f1 = 'f2 in x:'A -> 'B['x] } -->
   sequent { <H> >- 'a1 = 'a2 in 'A } -->
   sequent { <H> >- ('f1 'a1) = ('f2 'a2) in 'B['a1] }
   = it

doc docoff

(*
 * Typehood of application depends on the ability to infer a type.
 *)
let d_apply_typeT = funT (fun p ->
   let app = dest_type_term (Sequent.concl p) in
   let f, _ = dest_apply app in
   let f_type =
      try get_with_arg p with
         RefineError _ ->
            infer_type p f
   in
   let tac, univ =
     let _, _, univ = dest_dfun f_type in
         applyEquality, univ
   in
      if is_univ_term univ then
         univTypeT univ thenT tac f_type
      else
         raise (RefineError ("d_apply_typeT", StringTermError ("inferred type is not a univ", univ))))

let resource intro += << "type"{'f 'a} >>, wrap_intro d_apply_typeT

doc <:doc<
   @modsubsection{Subtyping}

   Function spaces are @emph{contravariant} in the domains, and
   @emph{covariant} in their ranges.  More specifically, the
   ranges must be pointwise covariant.

>>
interactive functionSubtype {| intro [] |} :
   ["subtype"] sequent { <H> >- 'A2 subtype 'A1 } -->
   ["subtype"] sequent { <H>; a1: 'A1 >- 'B1['a1] subtype 'B2['a1] } -->
   sequent { <H> >- a1:'A1 -> 'B1['a1]  subtype  a2:'A2 -> 'B2['a2] }
doc docoff

(*
(*
 * H; x: a1:A1 -> B1 <= a2:A2 -> B2; J[x] >- T[x]
 * by function_subtypeElimination i
 *
 * H; x: a1:A1 -> B1 <= a2:A2 -> B2; y: A2 <= A1; z: a:A2 -> B2[a] <= B1[a]; J[x] >- T[x]
 *)
interactive function_subtypeElimination {| elim [] |} 'H 'x 'y 'z 'a :
   ('t['x; 'y; 'z] : sequent { <H>;
             x: \subtype{(a1:'A1 -> 'B1['a1]); (a2:'A2 -> 'B2['a2])};
             <J['x]>;
             y: \subtype{'A2; 'A1};
             z: a:'A2 -> \subtype{'B1['a]; 'B2['a]}
             >- 'T['x]
           }) -->
   sequent { <H>; x: \subtype{(a1:'A1 -> 'B1['a1]); (a2:'A2 -> 'B2['a2])}; <J['x]> >- 'T['x] }
*)

(*
 * H; x: a1:A1 -> B1 = a2:A2 -> B2 in Ui; J[x] >- T[x]
 * by function_equalityElimination
 *
 * H; x: a1:A1 -> B1 = a2:A2 -> B2 in Ui; y: A1 = A2 in Ui; z: a:A1 -> B1[a] = B2[a] in Ui; J[x] >- T[x]
interactive function_equalityElimination {| elim [ThinOption thinT] |} 'H 'x 'y 'z 'a :
   ('t['x; 'y; 'z] : sequent { <H>;
             x: (a1:'A1 -> 'B1['a1]) = (a2:'A2 -> 'B2['a2]) in univ[i:l];
             <J['x]>;
             y: 'A1 = 'A2 in univ[i:l];
             z: a:'A1 -> ('B1['a] = 'B2['a] in univ[i:l])
             >- 'T['x]
           }) -->
   sequent { <H>; x: (a1:'A1 -> 'B1['a1]) = (a2:'A2 -> 'B2['a2]) in univ[i:l]; <J['x]> >- 'T['x] }
 *)

(*
 * H >- Ui ext a:A -> B
 * by functionFormation a A
 *
 * H >- A = A in Ui
 * H, a: A >- Ui ext B
 *)
interactive functionFormation 'A :
   [wf] sequent { <H> >- 'A in univ[i:l] } -->
   ('B['a] : sequent { <H>; a: 'A >- univ[i:l] }) -->
   sequent { <H> >- univ[i:l] }

(************************************************************************
 * EXTENSIOANLITY                                                       *
 ************************************************************************)

(*
 * Takes two arguments.
 *)
let fnExtensionalityT t1 t2 = funT (fun p ->
   let t, _, _ = dest_equal (concl p) in
      if is_fun_term t then
         functionExtensionality t1 t2 thenMT nameHypT (-1) "x"
      else
         functionExtensionality t1 t2)

let fnExtenT t = fnExtensionalityT t t
let fnExtenVoidT = fnExtenT << void -> void >>

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of lambda.
 *)
let inf_lambda inf consts decls eqs opt_eqs defs t =
   let v, b = dest_lambda t in
   let consts = SymbolSet.add consts v in
   let a = Typeinf.vnewname consts defs (Lm_symbol.add "T") in
   let a' = mk_var_term a in
   let eqs', opt_eqs', defs', b' =
      inf consts ((v, a')::decls) eqs opt_eqs ((a,Itt_void.top_term)::defs) b
   in
      eqs', opt_eqs', defs', mk_dfun_term v a' b'

(*
 * Type of apply.
 *)
let inf_apply inf consts decls eqs opt_eqs defs t =
   let f, a = dest_apply t in
   let eqs', opt_eqs', defs', f' = inf consts decls eqs opt_eqs defs f in
   let eqs'', opt_eqs'', defs'', a' = inf consts decls eqs' opt_eqs' defs' a in
   let eqs''', opt_eqs''', _ , f'' =
      Typeinf.typeinf_final consts eqs'' opt_eqs'' defs'' f' in
   if is_dfun_term f'' then
      let v, d, r = dest_dfun f'' in
         eqs''', opt_eqs''', defs'', subst1 r v a
   else
      let av = Typeinf.vnewname consts defs'' (Lm_symbol.add "A") in
      let bv = Typeinf.vnewname consts defs'' (Lm_symbol.add "B") in
      let at = mk_var_term av in
      let bt = mk_var_term bv in
         (eqnlist_append_eqn eqs'' f' (mk_fun_term at bt)),((a',at)::opt_eqs'''),
         ((av, Itt_void.top_term)::(bv,Itt_void.top_term)::defs''), bt

let resource typeinf += [
   dfun_term, infer_univ_dep0_dep1 dest_dfun;
   lambda_term, inf_lambda;
   apply_term, inf_apply
]

(************************************************************************
 * SUBTYPING                                                            *
 ************************************************************************)

(*
 * Subtyping of two function types.
 *)
let resource sub +=
   (DSubtype ([<< a1:'A1 -> 'B1['a1] >>, << a2:'A2 -> 'B2['a2] >>;
               << 'A2 >>, << 'A1 >>;
               << 'B1['a1] >>, << 'B2['a1] >>],
              functionSubtype))

(*
 * -*-
 * Local Variables:
 * End:
 * -*-
 *)
