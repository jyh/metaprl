(*
 * O95, the MetaPRL arm: the VIR of the frozen object (vir cd64c9fd, appendix A.2-A.3)
 * with the shared inputs (vir 8a73bc8c, inputs/router-inputs.md I1-I5).
 *)
extends Itt_theory

open Tactic_type.Tactic

(* I1: uninterpreted operators of the VIR *)
declare has_tokens{'st; 'p}
declare can_access{'p; 't}
declare dec_tokens{'st; 'p}
declare err_truncated_frame
declare err_unauthorized_or_rate_limited
declare wire_u32{'buf; 'k}

(* A.2 terms, given meaning in CTT *)
declare vir_magic
declare vlen{'s}
declare let_atom{'a; v. 'e['v]}
declare let_lin{'op; v. 'e['v]}
declare advance{'b; 'i; s. 'e['s]}
declare read_u32{'b; 'j; v. 'e['v]}
declare vguard{'c; 'e1; 'e2}
declare vreturn{'a}
declare vdrop{'c}

(* I2: the spec bodies *)
declare parse_header{'b0; s, sender, topic. 'k['s; 'sender; 'topic]}
declare check_rate_limit{'st; 'p; st2. 'k['st2]}
declare verify_acl{'p; 't; 'k}
declare emit_payload{'s; 'st}

(* I3, I4 *)
declare vir_U{'b0; 'st}
declare vir_F{'b0; 'st}

topval unfold_vir_magic : conv
topval unfold_vlen : conv
topval unfold_let_atom : conv
topval unfold_let_lin : conv
topval unfold_advance : conv
topval unfold_read_u32 : conv
topval unfold_vguard : conv
topval unfold_vreturn : conv
topval unfold_vdrop : conv
topval unfold_parse_header : conv
topval unfold_check_rate_limit : conv
topval unfold_verify_acl : conv
topval unfold_emit_payload : conv
topval unfold_vir_U : conv
topval unfold_vir_F : conv
