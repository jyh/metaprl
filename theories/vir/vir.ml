(*
 * O95, the MetaPRL arm (mojave). The VIR of the frozen object (vir cd64c9fd,
 * appendix A.2-A.3) with the shared inputs (vir 8a73bc8c, I1-I5).
 *
 * Representation: a slice is a pair (buffer, offset), read by fst/snd (lazy).
 * (First form used spread{b; buf, off. ...}, which is strict in b: every advance
 * then needed product eta, b ~ (fst b, snd b), which ITT has only for a hypothesis
 * variable. Changed 2026-11-01 00:2x before any proof on the I4 path; said on the bus.)
 * advance adds to the offset
 * (zero copy); vlen is length(buffer) - offset (I1 slice law); read_u32 reads the
 * buffer at offset + j (I1 read law). guard is ifthenelse on bool; return/drop
 * are inl/inr; let_atom and let_lin are substitution (linearity is NOT modelled).
 * The I1 operators are declared and never defined.
 *)
extends Itt_theory

open Basic_tactics

define unfold_vir_magic : vir_magic <--> 1297303345
define unfold_vlen : vlen{'s} <--> (length{fst{'s}} -@ snd{'s})
define unfold_let_atom : let_atom{'a; v. 'e['v]} <--> 'e['a]
define unfold_let_lin : let_lin{'op; v. 'e['v]} <--> 'e['op]
define unfold_advance :
   advance{'b; 'i; s. 'e['s]} <--> 'e[pair{fst{'b}; snd{'b} +@ 'i}]
define unfold_read_u32 :
   read_u32{'b; 'j; v. 'e['v]} <--> 'e[wire_u32{fst{'b}; snd{'b} +@ 'j}]
define unfold_vguard : vguard{'c; 'e1; 'e2} <--> ifthenelse{'c; 'e1; 'e2}
define unfold_vreturn : vreturn{'a} <--> inl{'a}
define unfold_vdrop : vdrop{'c} <--> inr{'c}

(* I2 *)
define unfold_parse_header :
   parse_header{'b0; s, sender, topic. 'k['s; 'sender; 'topic]} <-->
   vguard{ge_bool{vlen{'b0}; 24};
     read_u32{'b0; 0; magic.
     vguard{beq_int{'magic; vir_magic};
       read_u32{'b0; 4; sender.
       read_u32{'b0; 8; topic.
       advance{'b0; 12; s. 'k['s; 'sender; 'topic]}}};
       vdrop{err_unauthorized_or_rate_limited}}};
     vdrop{err_truncated_frame}}

define unfold_check_rate_limit :
   check_rate_limit{'st; 'p; st2. 'k['st2]} <-->
   vguard{has_tokens{'st; 'p};
     let_lin{dec_tokens{'st; 'p}; st2. 'k['st2]};
     vdrop{err_unauthorized_or_rate_limited}}

define unfold_verify_acl :
   verify_acl{'p; 't; 'k} <-->
   vguard{can_access{'p; 't}; 'k; vdrop{err_unauthorized_or_rate_limited}}

define unfold_emit_payload :
   emit_payload{'s; 'st} <--> advance{'s; 12; payload. vreturn{pair{'st; 'payload}}}

(* I3 *)
define unfold_vir_U :
   vir_U{'b0; 'st} <-->
   parse_header{'b0; s1, sender, topic.
     check_rate_limit{'st; 'sender; st2.
       verify_acl{'sender; 'topic;
         emit_payload{'s1; 'st2}}}}

(* I4: F of A.3, as written, bucket_st' for st' *)
define unfold_vir_F :
   vir_F{'b0; 'st} <-->
   vguard{ge_bool{vlen{'b0}; 24};
     read_u32{'b0; 0; magic.
     read_u32{'b0; 4; sender.
     read_u32{'b0; 8; topic.
     vguard{band{beq_int{'magic; vir_magic}; band{can_access{'sender; 'topic}; has_tokens{'st; 'sender}}};
       let_lin{dec_tokens{'st; 'sender}; st2.
       advance{'b0; 24; payload_slice.
         vreturn{pair{'st2; 'payload_slice}}}};
       vdrop{err_unauthorized_or_rate_limited}}}}};
     vdrop{err_truncated_frame}}

(* The 7 GIVEN rules (I5), stated as written. *)
interactive_rw beta_lin : let_lin{'v1; v2. 'e['v2]} <--> 'e['v1]
interactive_rw dce_atom : let_atom{'a; v. 'e} <--> 'e
interactive_rw guard_true : vguard{btrue; 'e1; 'e2} <--> 'e1
interactive_rw guard_merge :
   vguard{'c1; vguard{'c2; 'eok; 'eerr}; 'eerr} <--> vguard{band{'c1; 'c2}; 'eok; 'eerr}
interactive_rw slice_fuse :
   advance{'b; 'i; s1. advance{'s1; 'j; s2. 'e['s2]}} <--> advance{'b; 'i +@ 'j; s2. 'e['s2]}
interactive_rw read_comm :
   read_u32{'b; 'i; v1. let_lin{'upd['v1]; st2. read_u32{'b; 'j; v2. 'e['v1; 'st2; 'v2]}}} <-->
   read_u32{'b; 'i; v1. read_u32{'b; 'j; v2. let_lin{'upd['v1]; st2. 'e['v1; 'st2; 'v2]}}}

(*
 * CONDITIONAL forms of the GIVEN rules. In this model guard_merge and slice_fuse
 * as written are not derivable from ITT's definitions (ITT has no commuting
 * conversion for decide; pair arithmetic needs int). The condition is the GIVEN
 * rule's own typing side condition, not a new rule; it is counted in C2 at each use.
 *)
interactive_rw guard_merge_c :
   ('c1 in bool) -->
   vguard{'c1; vguard{'c2; 'eok; 'eerr}; 'eerr} <--> vguard{band{'c1; 'c2}; 'eok; 'eerr}

interactive_rw slice_fuse_c :
   ('b in top * int) --> ('i in int) --> ('j in int) -->
   advance{'b; 'i; s1. advance{'s1; 'j; s2. 'e['s2]}} <--> advance{'b; 'i +@ 'j; s2. 'e['s2]}

(*
 * AUX RULES (I5, E8): not among the 7 GIVEN rules; each is counted by C3.
 *)
interactive_rw aux_advance_sink_guard :
   advance{'b; 'i; s. vguard{'c; 'e['s]; 'd}} <--> vguard{'c; advance{'b; 'i; s. 'e['s]}; 'd}

interactive_rw aux_read_hoist :
   vguard{'c; read_u32{'b; 'j; v. 'e['v]}; 'd} <--> read_u32{'b; 'j; v. vguard{'c; 'e['v]; 'd}}

interactive_rw aux_guard_swap :
   ('c1 in bool) --> ('c2 in bool) -->
   vguard{'c1; vguard{'c2; 'e; 'd}; 'd} <--> vguard{'c2; vguard{'c1; 'e; 'd}; 'd}
