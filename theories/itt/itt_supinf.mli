doc <:doc<
   @begin[doc]
   @module[Itt_supinf]

   SupInf decision procedure (eventually it'll become a true tactic).

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

   Author: Yegor Bryukhov
   @email{ybryukhov@gc.cuny.edu}
   @end[license]
>>

doc <:doc<
   @begin[doc]
   @parents
   @end[doc]
>>
(*extends Itt_equal
extends Itt_squash
extends Itt_rfun
extends Itt_bool
extends Itt_logic
extends Itt_struct
extends Itt_decidable
extends Itt_quotient
extends Itt_int_arith*)
doc <:doc< @docoff >>

open Refiner.Refiner.TermOp

open Tactic_type.Sequent

module type BoundFieldSig =
sig
	type bfield

	val fieldUnit : bfield
	val fieldZero : bfield
	val plusInfinity : bfield
	val minusInfinity : bfield
	val mul : bfield -> bfield -> bfield
	val add : bfield -> bfield -> bfield
	val neg : bfield -> bfield
	val sub : bfield -> bfield -> bfield
	val inv : bfield -> bfield
	val div : bfield -> bfield -> bfield
	val compare : bfield -> bfield -> int
	val print : bfield -> unit
end

module type AF_Sig =
sig
	type vars
	type af
	type bfield

	val constvar : vars

   val mk_number: bfield -> af
   val mk_var: vars -> af
   val scale: bfield -> af -> af
   val add: af -> af -> af

   val coef: af -> vars -> bfield
   val remove: af -> vars -> af
   val split: af -> (bfield * vars * af)
   val isNumber: af -> bool

	val minusInfinity : af
	val plusInfinity : af

	val print : af -> unit
	val print_var : vars -> unit
end
(*
Axioms:
    Coef(Number(q),x) = If(x==Const, q, 0)
    Coef(Var(y),x) = If(y==x, 1, 0)
    Coef(Scale(q,F),x) = q * Coef(F,x)
    Coef(Add(F,G),x) = Coef(F,x) + Coef(G,x)

    Remove(Number(q),x) = Number(q)
    Remove(Var(y),x) = If(y==x, 0, Var(y))
    Remove(Scale(q,F),x) = q * Remove(F,x)
    Remove(Add(F,G),x) = Remove(F,x) + Remove(G,x)

    Split(Number(q)) = <q,Const,Number(0)>
    Split(Var(x)) = <1,x,Number(0)>
    F = Add(Scale(Split(F).1,Var(Split(F).2)), Split(F).3)
    Coef(Split(F).3, Split(F).2) = 0
    Split(F).2 = Const  implies  Split(F).3 = Number(0)

    IsNumber(F) = ( (exists q) F = Number(q) )

    Coef(F,x) = Coef(G,x) for all x:V  implies  F = G

Comments:
  - Const  is a reserved element of  V  used to represent the
    "variable" associated to the constant term in an affine form.
  - The constructors include injections from  Q  and  V , as well as
    the operations  q,F |-> q*F  and  F,G |-> F+G.
  - Coef(F,x)  is the coefficient of  x  in the form  F .
  - Remove(F,x) = F - Coef(F,x)*x.  Equivalently, it is the result of
    setting  x  to  0  in  F .
  - Split(a1*x1+...+an*xn) = <ai, xi, Remove(a1*x1+...+an*xn, xi)>
    for some  i  between  1  and  n , where the  xi  are distinct
    elements of  V  (including possibly  Const ).  The last "Split"
    axiom guarantees that the constant term is not split off until
    there is nothing else left.
*)
module type SAF_Sig =
sig
	type bfield
	type vars
	type af
	type saf

	val affine: af -> saf
   val min: saf -> saf -> saf
   val max: saf -> saf -> saf

   val scale: bfield -> saf -> saf
   val add: saf -> saf -> saf

   val decompose: saf -> af list
   val occurs: vars -> saf -> bool

	val print : saf -> unit
end
(*
Axioms:
    (For each equation below, the equation resulting from exchanging
    Min  with  Max  and  oo  with  -oo  is also to be an axiom.  The
    notation  L1 =~= L2  means that list  L1  is a permutation of the
    list  L2 .)

    Scale(q, Affine(F)) = Affine(Scale(q,F))
    Add(Affine(F), Affine(G)) = Affine(Add(F,G))

    Scale(q, Min(S,T)) = Min(Scale(q,S), Scale(q,T)),  if q>0;
                       = Affine(Number(0)),            if q=0;
                       = Max(Scale(q,S), Scale(q,T)),  if q<0
    Add(S, Min(T,U)) = Min(Add(S,T), Add(S,U))
    Add(Min(T,U), S) = Min(Add(T,S), Add(U,S))
    Min(Affine(Number(oo), S) = S
    Min(S, Affine(Number(oo)) = S
    Min(Affine(Number(-oo), S) = Affine(Number(-oo))
    Min(S, Affine(Number(-oo)) = Affine(Number(-oo))

    Decompose(Affine(F)) = [F]
    Decompose(Min(S,T)) =~= Append(Decompose(S), Decompose(T))

    Occurs(x, Affine(F)) = (Coef(x,F)!=0)
    Occurs(x, Min(F,G)) = Or(Occurs(x,F), Occurs(x,G))

    Decompose(S) =~= Decompose(T)  implies  S = T

Comments:
  - The first two axioms say that Affine is a homomorphism; the first
    axiom for  Decompose  implies that it's 1-1.
  - Only one  Decompose  operation is provided since, in the Sup-Inf
    algorithm, only top-level Min's occur as arguments of Sup, and
    only top-level Max's occur as arguments of Inf.
  - The last axiom only implies that  Decompose  return the Min'ed or
    Max'ed terms in some order, not necessarily in the order they were
    given.

Implementation notes:
  - Both Shostak's and Bledsoe's version of Sup-Inf use affine and
    semi-affine *expressions* and include a Simp routine for putting
    them in canonical form.  Shostak assumes (and arranges in the
    recursion) that all arguments to Sup or Inf are canonical; thus it
    is consistent with his approach to always maintain affine and
    semi-affine forms in canonical form and not perform any explicit
    simplifications.
  - On the other hand, the data structures above leave simplification
    to the implementor, who may choose to keep affine expressions
    unsimplified until a call to  Decompose  or  Split , where some
    simplification is neccesary, since (1) the two equations for Split
    imply that the variable split out doesn't occur in the remainder,
    and (2) the typing of Decompose implies that no Min's or Max's
    occur in the returned list.
*)
module type SACS_Sig =
sig
	type vars
	type af
	type saf
	type sacs

   val empty: sacs
   val addConstr: sacs -> af -> sacs

   val upper: sacs -> vars -> saf
   val lower: sacs -> vars -> saf

	val print : sacs -> unit
end
(*
Axioms:
    Upper(Empty, x) = Affine(Number(oo))
    Lower(Empty, x) = Affine(Number(-oo))

    Upper(AddConstr(F,C), x) =
        Min( Upper(C,x),
             If(Coef(F,x) >= 0, Affine(Number(oo)),
                                Scale(-1/Coef(F,x), Remove(F,x))) )
    Lower(AddConstr(F,C), x) =
        Max( Lower(C,x),
             If(Coef(F,x) <= 0, Affine(Number(-oo)),
                                Scale(-1/Coef(F,x), Remove(F,x))) )

Comments:
  - Empty produces the constraint set containing no constraints.
  - AddConstr(F,C)  produces the constraint set resulting from adding
    the constraint  F >= 0  to  C .
  - Upper(S,x)  computes the semi-affine form representing all of the
    upper bounds on  x  that can be deduced from  S .
  - Lower(S,x)  computes the semi-affine form representing all of the
    lower bounds on  x  that can be deduced from  S .
*)
module type CS_Sig =
sig
	type t
	type elt

   val empty: t
   val add: t -> elt -> t

   val mem: t -> elt -> bool
end

(*
Axioms:
    Member(x,Empty) = False
    Member(x,Add(S,y)) = Or(x==y, Member(x,S))
*)

module AF : AF_Sig
module SAF : SAF_Sig
module SACS : SACS_Sig
module CS : CS_Sig

topval testT : tactic

doc <:doc< @docoff >>
