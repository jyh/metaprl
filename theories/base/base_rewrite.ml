doc <:doc<
   @spelling{rewriter rw}

   @begin[doc]
   @module[Base_rewrite]

   The rewrite judgment $t_1 @longleftrightarrow t_2$ is used in rewrite
   derivations.  Derived rewrites are declared with the @bf{interactive_rw}
   form, as follows:

   @bf{interactive_rw} @it{name} : $t_1 @longleftrightarrow t_2$

   When a rewrite is declared, the @MetaPRL refiner
   requires a proof of the judgment $t_1 @longleftrightarrow t_2$.
   The judgment is not conditional, and it is not stated in a sequent
   calculus.

   The @hrefmodule[Base_rewrite] module lifts the rewrite judgment to the sequent
   level.  It also defines rules for reflexivity and symmetry.
   @end[doc]

   ----------------------------------------------------------------

   @begin[license]

   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/index.html for information on Nuprl,
   OCaml, and more information about this system.

   Copyright (C) 1998 Jason Hickey, Cornell University

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

   Author: Jason Hickey @email{jyh@cs.caltech.edu}
   Modified By: Aleksey Nogin @email{nogin@cs.caltech.edu}

   @end[license]
>>

doc <:doc<
   @begin[doc]
   @parents
   @end[doc]
>>
extends Auto_tactic
extends Base_trivial
doc docoff

extends Perv
extends Ocaml_df

open Refiner.Refiner.TermMan

open Tactic_type.Conversionals

open Auto_tactic

(*
 * XXX HACK: Currently Base_rewrite covers both conditional and unconditional rewrites.
 * Ideally, it should have empty hypothesis lists and only cover the unconditional rewrites.
 * while the conditional rewrites would be internal to specific theories.
 *)

doc <:doc<
   @begin[doc]
   @terms

   This theory uses its own semantics of sequents: a @tt[Base_rewrite] sequent
   of a form <<sequent { <H> >- Perv!"rewrite"{'a; 'b} }>> means that <<'a>> and <<'b>>
   are interchangeable in context <<df_context_var[H:v]>>.
   @end[doc]
>>
declare sequent_arg

doc <:doc<
   @begin[doc]
   @rules

   The following rule defines the rewrite reflexivity.  A term
   @it{a} always rewrites to itself.
   @end[doc]
>>
prim rewriteAxiom1 :
   sequent { <H> >- Perv!"rewrite"{'a; 'a} } = it

doc <:doc<
   @begin[doc]
   The @tt[rewriteAxiom2] conditional rewrite provides a link to the primitive
   rewriter: a proof of <<Perv!"rewrite"{'a; 'b}>> shows that the terms
   $a$ and $b$ are computationally equivalent.
   @end[doc]
>>
prim_rw rewriteAxiom2 'a 'b : (Perv!"rewrite"{'a; 'b}) --> 'a <--> 'b

doc <:doc<
   @begin[doc]
   A rule for symmetry is also defined.  The rules for symmetry and
   transitivity can be derived from reflexivity @hrefrule[rewriteAxiom1] and
   substitution @hrefrewrite[rewriteAxiom2].
   @end[doc]
>>
interactive rewriteSym :
   sequent { <H> >- Perv!"rewrite"{'a; 'b} } -->
   sequent { <H> >- Perv!"rewrite"{'b; 'a} }
doc <:doc< @docoff >>

(*
 * Substitution.
 * The binding term may be optionally supplied.
 *)
let rewriteC t =
   let a, b = dest_xrewrite t in
      rewriteAxiom2 a b

let rewriteT t =
   rwh (rewriteC t) 0

let rewriteSymT = rewriteSym

doc <:doc<
   @begin[doc]
   The reflexive rule @hrefrule[rewriteAxiom1] is also added to the
   @hreftactic[trivialT] resource.
   @docoff
   @end[doc]
>>

let resource auto += {
   auto_name = "Base_rewrite.triv_equalT";
   auto_prec = trivial_prec;
   auto_tac = rewriteAxiom1;
   auto_type = AutoTrivial;
}

dform sequent_arg_df : sequent_arg = `"" (* sub["BR"] *)

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
