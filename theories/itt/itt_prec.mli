(*
 * PArameterized recursive type.
 *
 *)

include Itt_equal
include Itt_subtype
include Itt_fun
include Itt_prod

open Refiner.Refiner.Term

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*
 * Parameterized recursive type has an additional
 * argument x, with initial value a.
 *)
declare "prec"{T, x. 'B['T; 'x]; 'a}
declare precind{'a; p, h. 'g['p; 'h]}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

rewrite reducePrecind : precind{'a; p, h. 'g['p; 'h]} <-->
   'g[lambda{a. precind{'a; p, h. 'g['p; 'h]}}; 'a]

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- prec(A1, x1. B1[A1; x1]; a1) = prec(A2, x2. B2[A2; x2]; a2) in Ui
 * by precEquality A x y z T P1 P2
 *
 * H >- a1 = a2 in A
 * H; x: A; T: A -> Ui >- B1[T; x] = B2[T; x] in Ui
 * H; P1: A -> Ui; P2: A -> Ui; z: x:A -> y: P1 x -> (y in P2 x); x:A; y: B1[P1; x]
 *   >- y = y in B2[P2; x]
 *)
axiom precEquality 'H 'A 'x 'y 'z 'T 'P1 'P2 :
   sequent [squash] { 'H >- 'a1 = 'a2 in 'A } -->
   sequent [squash] { 'H; x: 'A; T: 'A -> univ[@i:l] >- 'B1['T; 'x] = 'B2['T; 'x] in univ[@i:l] } -->
   sequent [squash] { 'H;
             P1: 'A -> univ[@i:l];
             P2: 'A -> univ[@i:l];
             z: x:'A -> subtype{('P1 'x); ('P2 'x)};
             x: 'A;
             y: 'B1['P1; 'x]
           >- 'y = 'y in 'B1['P2; 'x]
           } -->
   sequent ['ext] { 'H >- "prec"{A1, x1. 'B1['A1; 'x1]; 'a1}
                   = "prec"{A2, x2. 'B2['A2; 'x2]; 'a2}
                   in univ[@i:l]
           }

(*
 * H >- prec(T, x. B[T; x]; a) ext t
 * by precMemberFormation
 *
 * H >- B[lambda(a. prec(T, x. B[T; x])); a]
 * H >- prec(T, x. B[T; x]; a) = prec(T, x. B[T; x]; a) in type
 *)
axiom precMemberFormation 'H :
   sequent ['ext] { 'H >- 'B[lambda{z. "prec"{T, x. 'B['T; 'x]; 'z}}; 'a] } -->
   sequent [squash] { 'H >- "type"{("prec"{T, x. 'B['T; 'x]; 'a})} } -->
   sequent ['ext] { 'H >- "prec"{T, x. 'B['T; 'x]; 'a} }

(*
 * H >- a1 = a2 in prec(T, x. B[T; x]. a)
 * by precMemberEquality
 *
 * H >- prec(T, x. B[T; x]. a) = prec(T, x. B[T; x]. a) in type
 * H >- a1 = a2 in B[lambda(a. prec(T, x. B[T; x]); a); a]
 *)
axiom precMemberEquality 'H 'z :
   sequent [squash] { 'H >- "type"{("prec"{T, x. 'B['T; 'x]; 'a})} } -->
   sequent [squash] { 'H >- 'a1 = 'a2 in 'B[lambda{z. "prec"{T, x. 'B['T; 'x]; 'z}}; 'a] } -->
   sequent ['ext] { 'H >- 'a1 = 'a2 in "prec"{T, x. 'B['T; 'x]; 'a} }

(*
 * H; r: prec(T, x. B[T; x]; a); J[r] >- T[a]
 * by precElimination lambda(z. T[z]) A Z u h y
 *
 * H; r: prec(T, x. B[T; x]; a); J[r] >- a = a in A
 * H; r: prec(T, x. B[T; x]; a); J[r]; Z: A -> Ui
 *   u: p: (a: A * Z a) -> (p = p in a: A * prec(T, x. B[T; x]; a);
 *   h: p: (a: A * Z a) -> G[p];
 *   p: a: A * B[Z, a]
 * >- T[p]
 *)
axiom precElimination 'H 'J lambda{z. 'G['z]} 'a 'A 'Z 'r 'p 'u 'h univ[@i:l] :
   sequent [squash] { 'H; r: "prec"{T, x. 'B['T; 'x]; 'a}; 'J['r] >- 'a = 'a in 'A } -->
   sequent ['ext] { 'H; r: "prec"{T, x. 'B['T; 'x]; 'a}; 'J['r];
      Z: 'A -> univ[@i:l] ;
      u: subtype{(a: 'A * 'Z 'a); (a: 'A * "prec"{T, x. 'B['T; 'x]; 'a})};
      h: p: (a: 'A * 'Z 'a) -> 'G['p];
      p: a: 'A * 'B['Z; 'a]
   >- 'G['p]
   } -->
   sequent ['ext] { 'H; r: "prec"{T, x. 'B['T; 'x]; 'a}; 'J['r] >- 'G['a] }

(*
 * H; r: prec(T, x. B[T; x]; a); J[r] >- T[r]
 * by precUnrollElimination y u
 *
 * H; r: prec(T, x. B[T; x]; a); J[r];
 *   y: B[lambda(a. prec(T, x. B[T; x]); a); a];
 *   u: r = y in B[lambda(a. prec(T, x. B[T; x]); a); a]
 *   >- T[y]
 *)
axiom precUnrollElimination 'H 'J 'z 'y 'u :
   sequent ['ext] { 'H; r: "prec"{T, x. 'B['T; 'x]; 'a}; 'J['r];
             y: 'B[lambda{z. "prec"{T, x. 'B['T; 'x]; 'z}}; 'a];
             u: 'r = 'y in 'B[lambda{z. "prec"{T, x. 'B['T; 'x]; 'z}}; 'a]
             >- 'G['y]
           } -->
   sequent ['ext] { 'H; r: "prec"{T, x. 'B['T; 'x]; 'a}; 'J['r] >- 'G['r] }

(*
 * H >- precind(r1; h1, z1. t1[r1, z1]) = precind(r2; h2, z2. t2[r2; z2]) in S[r1]
 * by precindEquality lambda(x. S[x]) (a:A * prec(T, y. B[T; y]; a)) Z u h z
 *
 * H >- r1 = r2 in a:A * prec(T, y. B[T, y]; a)
 * H; Z: A -> Ui;
 *   u: z: (a:A * Z a) -> (z = z in a:A * prec(T, x. B[t, x]; a));
 *   h: z: (a:A * Z a) -> S[z];
 *   z: a: A * B[Z; a]
 *   >- t1[h; z] = t2[h; z] in S[z]
 *)
axiom precindEquality 'H lambda{x. 'S['x]} (a:'A * "prec"{T, y. 'B['T; 'y]; 'a}) 'Z 'u 'h 'z univ[@i:l] :
   sequent [squash] { 'H >- 'r1 = 'r2 in a: 'A * "prec"{T, y. 'B['T; 'y]; 'a} } -->
   sequent [squash] { 'H; Z: 'A -> univ[@i:l];
             u: subtype{(a: 'A * 'Z 'a); (a: 'A * "prec"{T, x. 'B['T; 'x]; 'a})};
             h: z: (a: 'A * 'Z 'a) -> 'S['z];
             z: a: 'A * 'B['Z; 'a]
             >- 't1['h; 'z] = 't2['h; 'z] in 'S['z]
           } -->
   sequent ['ext] { 'H >- precind{'r1; h1, z1. 't1['h1; 'z1]}
                   = precind{'r2; h2, z2. 't2['h2; 'z2]}
                   in 'S['r1]
           }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

val is_prec_term : term -> bool
val dest_prec : term -> string * string * term * term
val mk_prec_term : string -> string -> term -> term -> term

val is_precind_term : term -> bool
val dest_precind : term -> string * string * term * term
val mk_precind_term : string -> string -> term -> term -> term

(*
 * $Log$
 * Revision 1.6  1998/06/15 22:33:29  jyh
 * Added CZF.
 *
 * Revision 1.5  1998/06/01 13:56:04  jyh
 * Proving twice one is two.
 *
 * Revision 1.4  1998/05/28 13:47:51  jyh
 * Updated the editor to use new Refiner structure.
 * ITT needs dform names.
 *
 * Revision 1.3  1998/04/22 22:44:59  jyh
 * *** empty log message ***
 *
 * Revision 1.2  1997/08/06 16:18:36  jyh
 * This is an ocaml version with subtyping, type inference,
 * d and eqcd tactics.  It is a basic system, but not debugged.
 *
 * Revision 1.1  1997/04/28 15:52:20  jyh
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
 * Revision 1.3  1996/09/02 19:37:33  jyh
 * Semi working package management.
 * All _univ version removed.
 *
 * Revision 1.2  1996/05/21 02:16:58  jyh
 * This is a semi-working version before Wisconsin vacation.
 *
 * Revision 1.1  1996/03/30 01:37:16  jyh
 * Initial version of ITT.
 *
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
