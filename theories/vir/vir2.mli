(*
 * O95 PROGRAM 2, the MetaPRL arm: the B.1-faithful router with a dynamic payload
 * (vir 5d6f739a, inputs/program2-inputs.md J1-J5).
 *)
extends Vir

open Tactic_type.Tactic

(* J1 *)
declare take{'s; 'n; p. 'k['p]}
declare err_bad_payload

(* J2-J4 *)
declare parse_header2{'b0; s, sender, topic, off, n. 'k['s; 'sender; 'topic; 'off; 'n]}
declare emit_payload2{'s; 'off; 'n; 'st}
declare vir_U2{'b0; 'st}
declare vir_F2{'b0; 'st}

topval unfold_parse_header2 : conv
topval unfold_emit_payload2 : conv
topval unfold_vir_U2 : conv
topval unfold_vir_F2 : conv
