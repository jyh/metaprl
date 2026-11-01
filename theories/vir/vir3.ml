(*
 * O95 PROGRAM 3, the MetaPRL arm (mojave). The A.2 safety theorem over program 2's
 * F2, unchanged (vir 98d9329, inputs/program3-inputs.md K1-K4; E10: the principal
 * is frame_sender(b)). Model (B) of programs 1-2, unchanged.
 *
 * K2 as A.2 writes it: ValidFrame is a SET TYPE over the wire buffer (a CTT
 * ValidFrame is a WireBuf; its predicate is squashed when the set is eliminated).
 * The wire buffer (B: list{top}, the type program 2 gave a slice's buffer; B': below); the
 * frame is the whole-buffer slice pair{b; 0}, as Lean's wholeSlice. The accessors
 * are A.2's read_u32 at 0, 4, 8 of that slice.
 * K3: IsRouted(o) is "o is a return": assert of decide{o; btrue; bfalse}, the CTT
 * form of Lean's match to True/False. CanAccess is assert of can_access.
 * B' (council 2026-11-01 sA): the wire buffer is list{int} (vir.ml's wirebuf, was
 * list{top} here); every K2/K3 term has a wf rule in intro; K3 is a rule with
 * second-order premises -- [wf] the frame, [wf] the state (passed: it is not in
 * the goal), the routed premise -- and no typing premises, which the prims carry.
 *)
extends Vir2

open Basic_tactics

define unfold_whole_slice : whole_slice{'b} <--> pair{'b; 0}
define unfold_validframe :
   validframe <-->
   { b: wirebuf | ge{vlen{whole_slice{'b}}; 24} and (read_u32{whole_slice{'b}; 0; v. 'v} = vir_magic in int) }
define unfold_frame_sender : frame_sender{'b} <--> read_u32{whole_slice{'b}; 4; v. 'v}
define unfold_frame_topic : frame_topic{'b} <--> read_u32{whole_slice{'b}; 8; v. 'v}

define unfold_isrouted : isrouted{'o} <--> "assert"{decide{'o; x. btrue; y. bfalse}}

interactive whole_slice_wf {| intro [] |} :
   [wf] sequent { <H> >- 'b in wirebuf } -->
   sequent { <H> >- whole_slice{'b} in vslice }

interactive validframe_type {| intro [] |} :
   sequent { <H> >- "type"{validframe} }

interactive validframe_wirebuf {| intro [] |} :
   [wf] sequent { <H> >- 'b in validframe } -->
   sequent { <H> >- 'b in wirebuf }

interactive frame_sender_wf {| intro [] |} :
   [wf] sequent { <H> >- 'b in wirebuf } -->
   sequent { <H> >- frame_sender{'b} in int }

interactive frame_topic_wf {| intro [] |} :
   [wf] sequent { <H> >- 'b in wirebuf } -->
   sequent { <H> >- frame_topic{'b} in int }

interactive isrouted_type {| intro [] |} :
   [wf] sequent { <H> >- 'o in vresult } -->
   sequent { <H> >- "type"{isrouted{'o}} }

(*
 * K3: the scored theorem. A.2's statement as a rule: for b in ValidFrame and a
 * state st, IsRouted(F2(b, st)) implies CanAccess(frame_sender(b), frame_topic(b)).
 *)
interactive route_acl_safe {| intro [] |} 'st :
   [wf] sequent { <H> >- 'b in validframe } -->
   [wf] sequent { <H> >- 'st in state } -->
   sequent { <H> >- isrouted{vir_F2{whole_slice{'b}; 'st}} } -->
   sequent { <H> >- "assert"{can_access{frame_sender{'b}; frame_topic{'b}}} }

(* Display forms (B') *)
dform whole_slice_df : except_mode[src] :: whole_slice{'b} = `"wholeSlice(" slot{'b} `")"
dform validframe_df : except_mode[src] :: validframe = `"ValidFrame"
dform frame_sender_df : except_mode[src] :: frame_sender{'b} = `"frame_sender(" slot{'b} `")"
dform frame_topic_df : except_mode[src] :: frame_topic{'b} = `"frame_topic(" slot{'b} `")"
dform isrouted_df : except_mode[src] :: isrouted{'o} = `"IsRouted(" slot{'o} `")"
