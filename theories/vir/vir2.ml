(*
 * O95 PROGRAM 2, the MetaPRL arm (mojave). The B.1-faithful router with a dynamic
 * payload (vir 5d6f739a, inputs/program2-inputs.md J1-J5). Model (B) of program 1,
 * unchanged. take (J1) is declared and never defined: no rule looks inside it.
 * Atoms: 24 <= off is le_bool{24; off}; off + n <= len(s) is le_bool{off +@ n; vlen{s}}.
 *)
extends Vir

open Basic_tactics

(* J2 *)
define unfold_parse_header2 :
   parse_header2{'b0; s, sender, topic, off, n. 'k['s; 'sender; 'topic; 'off; 'n]} <-->
   vguard{ge_bool{vlen{'b0}; 24};
     read_u32{'b0; 0; magic.
     vguard{beq_int{'magic; vir_magic};
       read_u32{'b0; 4; sender. read_u32{'b0; 8; topic.
       read_u32{'b0; 12; off. read_u32{'b0; 16; n.
       advance{'b0; 12; s. 'k['s; 'sender; 'topic; 'off; 'n]}}}}};
       vdrop{err_unauthorized_or_rate_limited}}};
     vdrop{err_truncated_frame}}

define unfold_emit_payload2 :
   emit_payload2{'s; 'off; 'n; 'st} <-->
   vguard{band{le_bool{24; 'off}; le_bool{'off +@ 'n; vlen{'s} +@ 12}};
     advance{'s; 'off -@ 12; p. take{'p; 'n; q. vreturn{pair{'st; 'q}}}};
     vdrop{err_bad_payload}}

(* J3 *)
define unfold_vir_U2 :
   vir_U2{'b0; 'st} <-->
   parse_header2{'b0; s1, sender, topic, off, n.
     check_rate_limit{'st; 'sender; st2.
       verify_acl{'sender; 'topic;
         emit_payload2{'s1; 'off; 'n; 'st2}}}}

(* J4: F2 as vir wrote it, bucket_st' for st' *)
define unfold_vir_F2 :
   vir_F2{'b0; 'st} <-->
   vguard{ge_bool{vlen{'b0}; 24};
     read_u32{'b0; 0; magic. read_u32{'b0; 4; sender. read_u32{'b0; 8; topic.
     read_u32{'b0; 12; off. read_u32{'b0; 16; n.
     vguard{band{beq_int{'magic; vir_magic}; band{can_access{'sender; 'topic}; has_tokens{'st; 'sender}}};
       let_lin{dec_tokens{'st; 'sender}; st2.
       vguard{band{le_bool{24; 'off}; le_bool{'off +@ 'n; vlen{'b0}}};
         advance{'b0; 'off; p. take{'p; 'n; q. vreturn{pair{'st2; 'q}}}};
         vdrop{err_bad_payload}}};
       vdrop{err_unauthorized_or_rate_limited}}}}}}};
     vdrop{err_truncated_frame}}

(*
 * J5: U2 == F2. Conditions as program 1, with the buffer's length now typed:
 * vlen needs length{fst b0} in int, so b0 is in list{top} * int (program 1: top * int).
 *)
interactive_rw router2_fuse :
   ('b0 in list{top} * int) -->
   (all x: top. all k: int. wire_u32{'x; 'k} in int) -->
   (all x: int. all y: int. can_access{'x; 'y} in bool) -->
   (all x: int. has_tokens{'st; 'x} in bool) -->
   vir_U2{'b0; 'st} <--> vir_F2{'b0; 'st}
