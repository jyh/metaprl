(*
 * O95 PROGRAM 2, the MetaPRL arm (mojave). The B.1-faithful router with a dynamic
 * payload (vir 5d6f739a, inputs/program2-inputs.md J1-J5). Model (B) of program 1,
 * unchanged. take (J1) is declared and never defined: no rule looks inside it.
 * B' (council 2026-11-01 sA): take and ERR_BAD_PAYLOAD are axiomatized by prim wf
 * rules (J1 gives them no other law); every defined term has a wf rule in intro.
 * Atoms: 24 <= off is le_bool{24; off}; off + n <= len(s) is le_bool{off +@ n; vlen{s}}.
 *)
extends Vir

open Basic_tactics

(* J1: uninterpreted, axiomatized by their typing *)
prim take_wf {| intro [] |} :
   [wf] sequent { <H> >- 's in vslice } -->
   [wf] sequent { <H> >- 'n in int } -->
   [wf] sequent { <H>; p: vslice >- 'k['p] in 'T } -->
   sequent { <H> >- take{'s; 'n; p. 'k['p]} in 'T } = it

prim err_bad_payload_wf {| intro [] |} :
   sequent { <H> >- err_bad_payload in verr } = it

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

interactive parse_header2_wf {| intro [] |} :
   [wf] sequent { <H> >- 'b0 in vslice } -->
   [wf] sequent { <H>; s: vslice; sender: int; topic: int; off: int; n: int >- 'k['s; 'sender; 'topic; 'off; 'n] in vresult } -->
   sequent { <H> >- parse_header2{'b0; s, sender, topic, off, n. 'k['s; 'sender; 'topic; 'off; 'n]} in vresult }

interactive emit_payload2_wf {| intro [] |} :
   [wf] sequent { <H> >- 's in vslice } -->
   [wf] sequent { <H> >- 'off in int } -->
   [wf] sequent { <H> >- 'n in int } -->
   [wf] sequent { <H> >- 'st in state } -->
   sequent { <H> >- emit_payload2{'s; 'off; 'n; 'st} in vresult }

interactive vir_U2_wf {| intro [] |} :
   [wf] sequent { <H> >- 'b0 in vslice } -->
   [wf] sequent { <H> >- 'st in state } -->
   sequent { <H> >- vir_U2{'b0; 'st} in vresult }

interactive vir_F2_wf {| intro [] |} :
   [wf] sequent { <H> >- 'b0 in vslice } -->
   [wf] sequent { <H> >- 'st in state } -->
   sequent { <H> >- vir_F2{'b0; 'st} in vresult }

(*
 * J5: U2 == F2. B': the conditions are the two carriers.
 *)
interactive_rw router2_fuse :
   ('b0 in vslice) -->
   ('st in state) -->
   vir_U2{'b0; 'st} <--> vir_F2{'b0; 'st}

(* Display forms (B') *)
dform take_df : except_mode[src] :: take{'s; 'n; p. 'k} =
   szone pushm[0] `"take{" slot{'s} `"; " slot{'n} `"; " slot{'p} `"." hspace slot{'k} `"}" popm ezone
dform err_bad_payload_df : except_mode[src] :: err_bad_payload = `"ERR_BAD_PAYLOAD"
dform parse_header2_df : except_mode[src] :: parse_header2{'b0; s, sender, topic, off, n. 'k} =
   szone pushm[0] `"parse_header2{" slot{'b0} `"; " slot{'s} `", " slot{'sender} `", " slot{'topic} `", "
   slot{'off} `", " slot{'n} `"." hspace slot{'k} `"}" popm ezone
dform emit_payload2_df : except_mode[src] :: emit_payload2{'s; 'off; 'n; 'st} =
   `"emit_payload2{" slot{'s} `"; " slot{'off} `"; " slot{'n} `"; " slot{'st} `"}"
dform vir_U2_df : except_mode[src] :: vir_U2{'b0; 'st} = `"U2(" slot{'b0} `", " slot{'st} `")"
dform vir_F2_df : except_mode[src] :: vir_F2{'b0; 'st} = `"F2(" slot{'b0} `", " slot{'st} `")"
