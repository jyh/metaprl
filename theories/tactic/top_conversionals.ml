(*!
 * @begin[spelling]
 * Conversionals addr addrC allSubC andthenC conv
 * cutC dprod failC firstC foldC higherC idC inl
 * inr lowerC orelseC reduceC reduceDecideInl reduceSpread repeatC
 * rw rwh someSubC sweepDnC sweepUpC tryC
 * @end[spelling]
 *
 * @begin[doc]
 * @theory[Top_conversionals]
 *
 * Conversionals are analog of tactics  (Section~@reftheory[Top_tacticals])
 * for rewriting.  Conversionals are used extensively in the @Nuprl
 * type theory (Section @reftheory[Itt_theory]) to express and
 * apply computational equivalences.  The @tt{Top_conversionals}
 * module defines the basic conversionals provided by the @MetaPRL
 * prover.
 *
 * Each @bf{rewrite} definition in a module defines a conversion.
 * For example, the definition of beta reduction in the @Nuprl type
 * theory (Section @reftheory[Itt_rfun]), is defined as follows:
 *
 * @begin[center]
 * @bf{rewrite} unfold_beta : $(@lambda x. b[x])@space a @longleftrightarrow b[a]$
 * @end[center]
 *
 * This declaration defines a conversion called @tt{unfold_beta} that can
 * be applied with the function @tt{rwh}, which searches for the outermost
 * valid applications of the rewrite.  Here is an example proof step:
 *
 * $$
 * @rulebox{rwh; @tt{unfold_beta 0};
 *   @sequent{ext; H; ((@lambda v. v + 1)@space 2) = 3 @in @int};
 *   @sequent{ext; H; 2 + 1 = 3 @in @int}}
 * $$
 *
 * @end[doc]
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 *
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/index.html for information on Nuprl,
 * OCaml, and more information about this system.
 *
 * Copyright (C) 1998 Jason Hickey, Cornell University
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
 *
 * Author: Jason Hickey
 * @email{jyh@cs.caltech.edu}
 *
 * @end[license]
 *)

(*!
 * @begin[doc]
 * @parents
 * @end[doc]
 *)
include Mptop
(*! @docoff *)

open Mp_debug
open Printf

open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError

open Mp_resource
open Simple_print
open Term_match_table

open Tactic_type.Conversionals

(*
 * Debug statement.
 *)
let _ =
   show_loading "Loading Tacticals%t"

let debug_conv =
   create_debug (**)
      { debug_name = "conv";
        debug_description = "display conversion operation";
        debug_value = false
      }

let debug_reduce =
   create_debug (**)
      { debug_name = "reduce";
        debug_description = "display reductions";
        debug_value = false
      }

(*!
 * @begin[doc]
 * @thysection{Conversion application}
 *
 * @begin[description]
 * @item{@conv[rw];
 * Conversions are not tactics: they have a different type @tt{conv}
 * and they are applied differently.  The basic method for applying
 * a conversion is to use @tt{rw}, which converts a conversion to
 * a tactic applied to a specific clause in a sequent (these functions
 * are defined only for a sequent calculus).  The (@tt{rw} @it{conv} $i$)
 * @emph{tactic} applies the conversion @it{conv} to clause $i$ in
 * the current goal sequent.}
 * @end[description]
 *
 * @docoff
 * @end[doc]
 *)
let rw = Tactic_type.Conversionals.rw
let rwh = Tactic_type.Conversionals.rwh
let rwc = Tactic_type.Conversionals.rwc
let rwch = Tactic_type.Conversionals.rwch

(*!
 * @begin[doc]
 * @thysection{Primitive conversions}
 *
 * @begin[description]
 * @item{@conv[idC], @conv[failC];
 * The @tt{idC} conversion is the identity conversion: no rewriting
 * is performed.  The @tt{failC} conversion always fails.}
 * @end[description]
 *
 * @docoff
 * @end[doc]
 *)
let idC = Tactic_type.Conversionals.idC
let failC = Tactic_type.Conversionals.failC

(*!
 * @begin[doc]
 * @thysection{Conversionals}
 *
 * @begin[description]
 * @item{@conv[andthenC], @conv[orelseC];
 * Conversionals can be combined in the same manner as tactics.
 * The (@tt{$c_1$ andthenC $c_2$}) conversion first applies conversion
 * $c_1$, and then applies $c_2$ to the result term.  The (@tt{$c_1$ orelseC $c_2$})
 * conversion first applies $c_1$@; if $c_1$ fails (because the conversion does not
 * match the term being rewritten, or because of a call to @tt{failC}), $c_2$ is
 * applied instead.}
 *
 * @item{@conv[tryC], @conv[firstC];
 * There are several variations on @tt{orelseC}.  The (@tt{tryC} $c$) conversion
 * is equivalent to ($c$ orelseC idC).  The @tt{firstC} conversion takes a list of
 * conversions to try in order until the first one succeeds.  The conversion (@tt{firstC}
 * $[c_1; @cdots; c_n]$) is equivalent to @tt{$c_1$ orelseC $@cdots$ orelseC $c_n$}.}
 *
 * @item{@conv[repeatC];
 * The (@tt{repeatC} $c$) conversion applies conversion $c$ repeatedly
 * until it fails, or until it fails to make progress.}
 * @end[description]
 *
 * @docoff
 * @end[doc]
 *)
let prefix_andthenC = Tactic_type.Conversionals.prefix_andthenC
let prefix_orelseC = Tactic_type.Conversionals.prefix_orelseC
let tryC = Tactic_type.Conversionals.tryC
let firstC = Tactic_type.Conversionals.firstC
let repeatC = Tactic_type.Conversionals.repeatC
let repeatForC = Tactic_type.Conversionals.repeatForC

(*!
 * @begin[doc]
 * @thysection{Addressing and search}
 *
 * Generally, the terms to be rewritten to not occur at the outermost
 * level of a clause.  The following conversionals recursively search
 * through the subterms of a clause for applicable rewrites.
 *
 * @begin[description]
 * @item{@conv[someSubC];
 * The most general of these is the (@tt{someSubC}  $c$) conversion,
 * which tries applying conversion $c$ to all of the immediate subterms of
 * the clause.  It succeeds if $c$ succeeds on any of the subterms@; it
 * fails otherwise.  The conversion @tt{allSubC} requires success on
 * @emph{all} of the immediate subterms.}
 *
 * @item{@conv[addrC];
 * Subterms can also be addressed explicitly with the (@tt{addrC @it{addr} $c$})
 * conversion, although the use is discouraged.  The address is an integer list
 * that describes the @emph{path} leading to the term to be rewritten.  For
 * example, the address $[ ]$ is the identity address, $[0]$ is its leftmost
 * subterm, $[0; 1]$ is the second subterm of the first subterm, etc.  Addresses
 * are fragile, and correct addresses are difficult to discover.  For this
 * reason, the @tt{addrC} conversion is almost never used.}
 *
 * @item{@conv[higherC];
 * The (@tt{higherC} $c$) conversion searches for the outermost
 * occurrences of subterms in the clause where conversion $c$
 * applies.  It's definition uses @tt{someSubC}.
 *
 * @begin[center]
 * @code{let rec higherC c = c orelseC (someSubC (higherC c))}
 * @end[center]}
 *
 * @item{@conv[lowerC], @conv[sweepDnC];
 * The @tt{lowerC} conversional searches for the @emph{innermost}
 * rewrite occurrences.  The (@tt{sweepDnC} $c$) conversion applies
 * $c$ from the outermost to the innermost subterms.
 *
 * @begin[center]
 * @code{let rec sweepDnC c = (tryC c) andalsoC (someSubC (sweepDnC c))}
 * @end[center]}
 *
 * @item{@conv[sweepUpC];
 * The @tt{sweepUpC} conversion works from the innermost to outermost subterms.
 * Note that these conversions never fail@; however they may fail to
 * make progress if the conversion $c$ never succeeds.}
 *
 * @item{@conv[rwh];
 * For convenience, the @tt{rwh} function automatically
 * applies the @tt{higherC} conversion, the tactic (@tt{rwh $c$ $i$})
 * is equivalent to (@tt{rw (higherC $c$) $i$}).}
 * @end[description]
 *
 * @docoff
 * @end[doc]
 *)
let someSubC = Tactic_type.Conversionals.someSubC
let allSubC = Tactic_type.Conversionals.allSubC
let higherC = Tactic_type.Conversionals.higherC
let lowerC = Tactic_type.Conversionals.lowerC
let sweepUpC = Tactic_type.Conversionals.sweepUpC
let sweepDnC = Tactic_type.Conversionals.sweepDnC

(*!
 * @begin[doc]
 * @thysection{Conversion reversal}
 *
 * Computational rewrites define a congruence, and all of the
 * equivalence relations hold, including reversing the application
 * of the rewrite.  However, reversed rewrites are usually incompletely
 * specified.
 *
 * @begin[description]
 * @item{@conv[foldC], @conv[cutC];
 * The (@tt{foldC} $t$ $c$) takes a term $t$ and a conversion that
 * rewrites the term in the @emph{forward} direction, and generates
 * reversed conversion.  For example, here is a reverse application of
 * the beta rewrite.
 *
 * $$
 * @rulebox{rwh; (@tt{foldC} (@lambda v. v + 1)@space 2 @tt{unfold_beta}) 0;
 *   @sequent{ext; H; 2 + 1 = 3 @in @int};
 *   @sequent{ext; H; ((@lambda v. v + 1)@space 2) = 3 @in @int}}
 * $$
 *
 * @noindent
 * The @tt{cutC} conversion is used to replace a term and generate a
 * rewrite obligation.
 *
 * $$
 * @rulebox{rw; (@tt{addrC} [1] (@tt{cutC} 3)) 0;
 *   @sequent{ext; H; 3 = 3 @in @int}@cr
 *   @sequent{ext; H; ((@lambda v. v + 1)@space 2) @longleftrightarrow 3};
 *   @sequent{ext; H; ((@lambda v. v + 1)@space 2) = 3 @in @int}}
 * $$}
 * @end[description]
 *
 * @docoff
 * @end[doc]
 *)
let addrC = Tactic_type.Conversionals.addrC
let clauseC = Tactic_type.Conversionals.clauseC
let foldC = Tactic_type.Conversionals.foldC
let makeFoldC = Tactic_type.Conversionals.makeFoldC
let cutC = Tactic_type.Conversionals.cutC

(************************************************************************
 * REDUCTION RESOURCE                                                   *
 ************************************************************************)

(*!
 * @begin[doc]
 * @resources
 *
 * @bf{The @Comment!resource[reduce] resource}
 *
 * The @tt{reduce} resource provides a generic method for
 * defining @emph{evaluation}.  The @tt{reduceC} conversion
 * can be used to apply this evaluator.
 *
 * For example, the @Nuprl type theory describes several
 * generic reductions:
 * @begin[description]
 * @item{beta; $(@lambda v. b[v])@space a @longleftrightarrow b[a]$}
 * @item{pair; $(@bf{match}@space (a, b)@space @bf{with}@space u, v @rightarrow c[u, v]) @longleftrightarrow c[a, b]$}
 * @item{union; $(@bf{match}@space @i{inl}(a)@space @bf{with}
 *                @i{inl}(u) @rightarrow b[u]
 *                @mathrel{|} @i{inr}(v) @rightarrow c[v]) @longleftrightarrow b[a]$}
 * @end[description]
 *
 * Each of the modules for functions (Section @reftheory[Itt_rfun]),
 * tuples (Section @reftheory[Itt_dprod]), and union (Section @reftheory[Itt_union]),
 * defines an addition to the @hrefresource[reduce_resource]: the @hreftheory[Itt_rfun] adds
 * the @hrefresource[reduce_beta] rewrite with redex $(@lambda v. b[v])@space a$@; the
 * @tt{Itt_dprod} adds the @tt{reduceSpread} rewrite with redex
 * $(@bf{match}@space (a, b)@space @bf{with}@space u, v @rightarrow c[u, v])$@; and the
 * @tt{Itt_union} adds the @tt{reduceDecideInl} rewrite with
 * redex $(@bf{match}@space @i{inl}(a)@space @bf{with}
 *                @i{inl}(u) @rightarrow b[u]
 *                @mathrel{|} @i{inr}(v) @rightarrow c[v])$
 *
 * In modules that @tt{include} these three theories, the @tt{reduceC}
 * conversion will recursively search for applications of these three
 * rewrites in an attempt to fully reduce the term.
 *
 * The implementation of the the @tt{reduce_resource} and the @tt{reduceC}
 * conversion rely on tables to store the shape of redices, together with the
 * conversions for the reduction.
 *
 * @docoff
 * @end[doc]
 *)
type reduce_data = (conv, conv) term_table

resource (term * conv, conv, reduce_data, conv) reduce_resource

(*
 * Extract a D tactic from the data.
 * The tactic checks for an optable.
 *)
let identity x = x

let extract_data tbl =
   let rw e =
      let t = env_term e in
      let conv =
         try
            (* Find and apply the right tactic *)
            if !debug_reduce then
               eprintf "Conversionals: lookup %a%t" debug_print t eflush;
            snd (Term_match_table.lookup "Conversionals.extract_data" tbl identity t)
         with
            Not_found ->
               raise (RefineError ("Conversionals.extract_data", StringTermError ("no reduction for", t)))
      in
         if !debug_reduce then
            eprintf "Conversionals: applying %a%t" debug_print t eflush;
         conv
   in
      funC rw

(*
 * Add a new tactic.
 *)
let improve_data (t, conv) tbl =
   Refine_exn.print Dform.null_base (insert tbl t) conv

(*
 * Wrap up the joiner.
 *)
let join_resource base1 base2 =
   join_tables base1 base2

let extract_resource = extract_data

let improve_resource data x =
   if !debug_reduce then
      begin
         let t, _ = x in
         let opname = opname_of_term t in
            eprintf "Conversionals.improve_resource: %a%t" debug_print t eflush
      end;
   improve_data x data

let improve_resource_arg data name cvars vars args params mterm conv =
   match mterm with
      MetaIff (MetaTheorem t, _) ->
         improve_resource data (t, conv)
    | _ ->
         raise (RefineError ("Conversionals.improve_resource_arg", StringError "not a simple rewrite"))

let close_resource rsrc modname =
   rsrc

(*
 * Resource.
 *)
let reduce_resource =
   Mp_resource.create (**)
      { resource_join = join_resource;
        resource_extract = extract_resource;
        resource_improve = improve_resource;
        resource_improve_arg = improve_resource_arg;
        resource_close = close_resource
      }
      (new_table ())

let get_resource modname =
   Mp_resource.find reduce_resource modname

let rec add_reduce_info rr = function
   (t, conv) :: tl ->
      add_reduce_info (Mp_resource.improve rr (t, conv)) tl
 | [] ->
      rr

let reduceTopC_env e =
   get_conv (env_arg e) "reduce"

let reduceTopC = funC reduceTopC_env

let reduceC =
   repeatC (higherC reduceTopC)

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
