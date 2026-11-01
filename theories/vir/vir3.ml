(*
 * O95 PROGRAM 3, the MetaPRL arm (mojave). The A.2 safety theorem over program 2's
 * F2, unchanged (vir 98d9329, inputs/program3-inputs.md K1-K4; E10: the principal
 * is frame_sender(b)). Model (B) of programs 1-2, unchanged.
 *
 * K2 as A.2 writes it: ValidFrame is a SET TYPE over the wire buffer (a CTT
 * ValidFrame is a WireBuf; its predicate is squashed when the set is eliminated).
 * The wire buffer is list{top}, the type program 2 gave the buffer of a slice; the
 * frame is the whole-buffer slice pair{b; 0}, as Lean's wholeSlice. The accessors
 * are A.2's read_u32 at 0, 4, 8 of that slice.
 * K3: IsRouted(o) is "o is a return": assert of decide{o; btrue; bfalse}, the CTT
 * form of Lean's match to True/False. CanAccess is assert of can_access.
 * take (J1) stays declared and undefined, so the statement's well-formedness needs
 * its typing as a hypothesis, beside the I1 typings (C4 does not count hypotheses).
 *)
extends Vir2

open Basic_tactics

define unfold_wirebuf : wirebuf <--> list{top}
define unfold_whole_slice : whole_slice{'b} <--> pair{'b; 0}
define unfold_validframe :
   validframe <-->
   { b: wirebuf | ge{vlen{whole_slice{'b}}; 24} and (read_u32{whole_slice{'b}; 0; v. 'v} = vir_magic in int) }
define unfold_frame_sender : frame_sender{'b} <--> read_u32{whole_slice{'b}; 4; v. 'v}
define unfold_frame_topic : frame_topic{'b} <--> read_u32{whole_slice{'b}; 8; v. 'v}

define unfold_isrouted : isrouted{'o} <--> "assert"{decide{'o; x. btrue; y. bfalse}}

(*
 * K3: the scored theorem. Statement as A.2: for all b in ValidFrame and every state,
 * IsRouted(F2(b, st)) implies CanAccess(frame_sender(b), frame_topic(b)).
 *)
interactive route_acl_safe :
   sequent { <H> >- all x: top. all k: int. wire_u32{'x; 'k} in int } -->
   sequent { <H> >- all x: int. all y: int. can_access{'x; 'y} in bool } -->
   sequent { <H> >- all s: top. all x: int. has_tokens{'s; 'x} in bool } -->
   sequent { <H> >- all p: top. all n: int. all s: top. take{'p; 'n; q. vreturn{pair{'s; 'q}}} in top + top } -->
   sequent { <H> >- all b: validframe. all st: top.
      (isrouted{vir_F2{whole_slice{'b}; 'st}} => "assert"{can_access{frame_sender{'b}; frame_topic{'b}}}) }
