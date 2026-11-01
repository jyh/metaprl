(*
 * O95, the MetaPRL arm (mojave). The VIR of the frozen object (vir cd64c9fd,
 * appendix A.2-A.3) with the shared inputs (vir 8a73bc8c, I1-I5).
 *
 * AMENDMENT B' (council 2026-11-01 sA, the Captain's style rulings; a declared
 * amendment under the preregistration, predictions untouched):
 *  1. second-order implication, never `all`: a theorem is a rule whose wf
 *     subgoals are [wf] premises; a conditional rewrite's conditions are carriers.
 *  2. never `top`: typed carriers. The wire is list{int}; a slice is wire * int;
 *     the bucket state is a declared type `state`; drop codes are a declared type
 *     `verr`; a router's result is (state * slice) + verr.
 *  3. the I1 operators stay UNINTERPRETED (router-inputs.md:8) and are axiomatized
 *     by `prim` wf rules, each in intro; every DEFINED term gets an `interactive`
 *     wf rule in intro, so typing subgoals are closed by autoT.
 *     The I1 slice and read laws hold BY DEFINITION here (vlen, advance and
 *     read_u32 are defined, as in B), so they are not added as prim_rw.
 *  4. a display form for every VIR term.
 *
 * Representation (unchanged from B): a slice is a pair (buffer, offset), read by
 * fst/snd (lazy). advance adds to the offset (zero copy); vlen is
 * length(buffer) - offset; read_u32 reads the buffer at offset + j. guard is
 * ifthenelse on bool; return/drop are inl/inr; let_atom and let_lin are
 * substitution (linearity is NOT modelled).
 *)
extends Itt_theory

open Basic_tactics
open Itt_struct2

(************************************************************************
 * Carriers.
 *)
define unfold_wirebuf : wirebuf <--> list{int}
define unfold_vslice : vslice <--> wirebuf * int
define unfold_vresult : vresult <--> ((state * vslice) + verr)

(* The two declared carriers (I1 gives them no structure). *)
prim state_univ {| intro [] |} :
   sequent { <H> >- state in univ[i:l] } = it

prim verr_univ {| intro [] |} :
   sequent { <H> >- verr in univ[i:l] } = it

interactive state_type {| intro [] |} :
   sequent { <H> >- "type"{state} }

interactive verr_type {| intro [] |} :
   sequent { <H> >- "type"{verr} }

interactive wirebuf_univ {| intro [] |} :
   sequent { <H> >- wirebuf in univ[i:l] }

interactive wirebuf_type {| intro [] |} :
   sequent { <H> >- "type"{wirebuf} }

interactive vslice_univ {| intro [] |} :
   sequent { <H> >- vslice in univ[i:l] }

interactive vslice_type {| intro [] |} :
   sequent { <H> >- "type"{vslice} }

interactive vresult_univ {| intro [] |} :
   sequent { <H> >- vresult in univ[i:l] }

interactive vresult_type {| intro [] |} :
   sequent { <H> >- "type"{vresult} }

(* A slice's two projections (the buffer and the offset). *)
interactive vslice_fst_wf {| intro [] |} :
   [wf] sequent { <H> >- 's in vslice } -->
   sequent { <H> >- fst{'s} in wirebuf }

interactive vslice_snd_wf {| intro [] |} :
   [wf] sequent { <H> >- 's in vslice } -->
   sequent { <H> >- snd{'s} in int }

(* The wire's length (vlen reads it). *)
interactive wirebuf_length_wf {| intro [] |} :
   [wf] sequent { <H> >- 'b in wirebuf } -->
   sequent { <H> >- length{'b} in int }

(************************************************************************
 * I1: the uninterpreted operators, axiomatized by their typing alone.
 *)
prim wire_u32_wf {| intro [] |} :
   [wf] sequent { <H> >- 'buf in wirebuf } -->
   [wf] sequent { <H> >- 'k in int } -->
   sequent { <H> >- wire_u32{'buf; 'k} in int } = it

prim can_access_wf {| intro [] |} :
   [wf] sequent { <H> >- 'p in int } -->
   [wf] sequent { <H> >- 't in int } -->
   sequent { <H> >- can_access{'p; 't} in bool } = it

prim has_tokens_wf {| intro [] |} :
   [wf] sequent { <H> >- 'st in state } -->
   [wf] sequent { <H> >- 'p in int } -->
   sequent { <H> >- has_tokens{'st; 'p} in bool } = it

prim dec_tokens_wf {| intro [] |} :
   [wf] sequent { <H> >- 'st in state } -->
   [wf] sequent { <H> >- 'p in int } -->
   sequent { <H> >- dec_tokens{'st; 'p} in state } = it

prim err_truncated_frame_wf {| intro [] |} :
   sequent { <H> >- err_truncated_frame in verr } = it

prim err_unauthorized_or_rate_limited_wf {| intro [] |} :
   sequent { <H> >- err_unauthorized_or_rate_limited in verr } = it

(************************************************************************
 * A.2 terms.
 *)
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

interactive vir_magic_wf {| intro [] |} :
   sequent { <H> >- vir_magic in int }

interactive vlen_wf {| intro [] |} :
   [wf] sequent { <H> >- 's in vslice } -->
   sequent { <H> >- vlen{'s} in int }

interactive let_atom_wf {| intro [intro_typeinf <<'a>>] |} 'A :
   [wf] sequent { <H> >- 'a in 'A } -->
   [wf] sequent { <H>; v: 'A >- 'e['v] in 'T } -->
   sequent { <H> >- let_atom{'a; v. 'e['v]} in 'T }

interactive let_lin_wf {| intro [] |} :
   [wf] sequent { <H> >- 'op in state } -->
   [wf] sequent { <H>; v: state >- 'e['v] in 'T } -->
   sequent { <H> >- let_lin{'op; v. 'e['v]} in 'T }

interactive advance_wf {| intro [] |} :
   [wf] sequent { <H> >- 'b in vslice } -->
   [wf] sequent { <H> >- 'i in int } -->
   [wf] sequent { <H>; s: vslice >- 'e['s] in 'T } -->
   sequent { <H> >- advance{'b; 'i; s. 'e['s]} in 'T }

interactive read_u32_wf {| intro [] |} :
   [wf] sequent { <H> >- 'b in vslice } -->
   [wf] sequent { <H> >- 'j in int } -->
   [wf] sequent { <H>; v: int >- 'e['v] in 'T } -->
   sequent { <H> >- read_u32{'b; 'j; v. 'e['v]} in 'T }

interactive vguard_wf {| intro [] |} :
   [wf] sequent { <H> >- 'c in bool } -->
   [wf] sequent { <H> >- 'e1 in 'T } -->
   [wf] sequent { <H> >- 'e2 in 'T } -->
   sequent { <H> >- vguard{'c; 'e1; 'e2} in 'T }

interactive vreturn_wf {| intro [] |} :
   [wf] sequent { <H> >- 'a in state * vslice } -->
   sequent { <H> >- vreturn{'a} in vresult }

interactive vdrop_wf {| intro [] |} :
   [wf] sequent { <H> >- 'c in verr } -->
   sequent { <H> >- vdrop{'c} in vresult }

(************************************************************************
 * I2.
 *)
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

interactive parse_header_wf {| intro [] |} :
   [wf] sequent { <H> >- 'b0 in vslice } -->
   [wf] sequent { <H>; s: vslice; sender: int; topic: int >- 'k['s; 'sender; 'topic] in vresult } -->
   sequent { <H> >- parse_header{'b0; s, sender, topic. 'k['s; 'sender; 'topic]} in vresult }

interactive check_rate_limit_wf {| intro [] |} :
   [wf] sequent { <H> >- 'st in state } -->
   [wf] sequent { <H> >- 'p in int } -->
   [wf] sequent { <H>; st2: state >- 'k['st2] in vresult } -->
   sequent { <H> >- check_rate_limit{'st; 'p; st2. 'k['st2]} in vresult }

interactive verify_acl_wf {| intro [] |} :
   [wf] sequent { <H> >- 'p in int } -->
   [wf] sequent { <H> >- 't in int } -->
   [wf] sequent { <H> >- 'k in vresult } -->
   sequent { <H> >- verify_acl{'p; 't; 'k} in vresult }

interactive emit_payload_wf {| intro [] |} :
   [wf] sequent { <H> >- 's in vslice } -->
   [wf] sequent { <H> >- 'st in state } -->
   sequent { <H> >- emit_payload{'s; 'st} in vresult }

(************************************************************************
 * I3, I4.
 *)
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

interactive vir_U_wf {| intro [] |} :
   [wf] sequent { <H> >- 'b0 in vslice } -->
   [wf] sequent { <H> >- 'st in state } -->
   sequent { <H> >- vir_U{'b0; 'st} in vresult }

interactive vir_F_wf {| intro [] |} :
   [wf] sequent { <H> >- 'b0 in vslice } -->
   [wf] sequent { <H> >- 'st in state } -->
   sequent { <H> >- vir_F{'b0; 'st} in vresult }

(************************************************************************
 * The 7 GIVEN rules (I5), stated as written. (const_fold is ITT's own
 * arithmetic reduction.)
 *)
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
 * CONDITIONAL forms of the GIVEN rules (as in B; the conditions are the GIVEN
 * rule's own typing side conditions, now over the typed carriers).
 *)
interactive_rw guard_merge_c :
   ('c1 in bool) -->
   vguard{'c1; vguard{'c2; 'eok; 'eerr}; 'eerr} <--> vguard{band{'c1; 'c2}; 'eok; 'eerr}

interactive_rw slice_fuse_c :
   ('b in vslice) --> ('i in int) --> ('j in int) -->
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

(*
 * I4: U == F. B': the conditions are the two carriers; the operator typings are
 * the prims above, used through intro.
 *)
interactive_rw router_fuse :
   ('b0 in vslice) -->
   ('st in state) -->
   vir_U{'b0; 'st} <--> vir_F{'b0; 'st}

(************************************************************************
 * Display forms (B' ruling 4).
 *)
dform wirebuf_df : except_mode[src] :: wirebuf = `"WireBuf"
dform vslice_df : except_mode[src] :: vslice = `"Slice"
dform state_df : except_mode[src] :: state = `"State"
dform verr_df : except_mode[src] :: verr = `"Err"
dform vresult_df : except_mode[src] :: vresult = `"Result"

dform has_tokens_df : except_mode[src] :: has_tokens{'st; 'p} =
   `"has_tokens(" slot{'st} `", " slot{'p} `")"
dform can_access_df : except_mode[src] :: can_access{'p; 't} =
   `"can_access(" slot{'p} `", " slot{'t} `")"
dform dec_tokens_df : except_mode[src] :: dec_tokens{'st; 'p} =
   `"dec_tokens(" slot{'st} `", " slot{'p} `")"
dform err_truncated_frame_df : except_mode[src] :: err_truncated_frame = `"ERR_TRUNCATED_FRAME"
dform err_unauthorized_or_rate_limited_df : except_mode[src] :: err_unauthorized_or_rate_limited =
   `"ERR_UNAUTHORIZED_OR_RATE_LIMITED"
dform wire_u32_df : except_mode[src] :: wire_u32{'buf; 'k} =
   `"wire_u32(" slot{'buf} `", " slot{'k} `")"

dform vir_magic_df : except_mode[src] :: vir_magic = `"MAGIC"
dform vlen_df : except_mode[src] :: vlen{'s} = `"len(" slot{'s} `")"
dform let_atom_df : except_mode[src] :: let_atom{'a; v. 'e} =
   szone pushm[0] `"let_atom{" slot{'a} `"; " slot{'v} `"." hspace slot{'e} `"}" popm ezone
dform let_lin_df : except_mode[src] :: let_lin{'op; v. 'e} =
   szone pushm[0] `"let_lin{" slot{'op} `"; " slot{'v} `"." hspace slot{'e} `"}" popm ezone
dform advance_df : except_mode[src] :: advance{'b; 'i; s. 'e} =
   szone pushm[0] `"advance{" slot{'b} `"; " slot{'i} `"; " slot{'s} `"." hspace slot{'e} `"}" popm ezone
dform read_u32_df : except_mode[src] :: read_u32{'b; 'j; v. 'e} =
   szone pushm[0] `"read_u32{" slot{'b} `"; " slot{'j} `"; " slot{'v} `"." hspace slot{'e} `"}" popm ezone
dform vguard_df : except_mode[src] :: vguard{'c; 'e1; 'e2} =
   szone pushm[2] `"guard{" slot{'c} `";" hspace slot{'e1} `";" hspace slot{'e2} `"}" popm ezone
dform vreturn_df : except_mode[src] :: vreturn{'a} = `"return{" slot{'a} `"}"
dform vdrop_df : except_mode[src] :: vdrop{'c} = `"drop{" slot{'c} `"}"

dform parse_header_df : except_mode[src] :: parse_header{'b0; s, sender, topic. 'k} =
   szone pushm[0] `"parse_header{" slot{'b0} `"; " slot{'s} `", " slot{'sender} `", " slot{'topic} `"."
   hspace slot{'k} `"}" popm ezone
dform check_rate_limit_df : except_mode[src] :: check_rate_limit{'st; 'p; st2. 'k} =
   szone pushm[0] `"check_rate_limit{" slot{'st} `"; " slot{'p} `"; " slot{'st2} `"." hspace slot{'k} `"}" popm ezone
dform verify_acl_df : except_mode[src] :: verify_acl{'p; 't; 'k} =
   szone pushm[0] `"verify_acl{" slot{'p} `"; " slot{'t} `";" hspace slot{'k} `"}" popm ezone
dform emit_payload_df : except_mode[src] :: emit_payload{'s; 'st} =
   `"emit_payload{" slot{'s} `"; " slot{'st} `"}"
dform vir_U_df : except_mode[src] :: vir_U{'b0; 'st} = `"U(" slot{'b0} `", " slot{'st} `")"
dform vir_F_df : except_mode[src] :: vir_F{'b0; 'st} = `"F(" slot{'b0} `", " slot{'st} `")"
