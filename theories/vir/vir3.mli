(*
 * O95 PROGRAM 3, the MetaPRL arm: the A.2 safety theorem over program 2's F2
 * (vir 98d9329, inputs/program3-inputs.md K1-K4).
 *)
extends Vir2

open Tactic_type.Tactic

(* K2 *)
declare whole_slice{'b}
declare validframe
declare frame_sender{'b}
declare frame_topic{'b}

(* K3 *)
declare isrouted{'o}

topval unfold_whole_slice : conv
topval unfold_validframe : conv
topval unfold_frame_sender : conv
topval unfold_frame_topic : conv
topval unfold_isrouted : conv
