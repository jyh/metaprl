cd "/vir/vir/router_fuse";;
refine (rw (sweepDnC (unfold_vir_U orelseC unfold_vir_F)) 0 thenT rw (sweepDnC (unfold_parse_header orelseC unfold_check_rate_limit orelseC unfold_verify_acl orelseC unfold_emit_payload)) 0 thenT rw (addrC [1;2;3;2;3;3] aux_advance_sink_guard) 0 thenT rw (addrC [1;2;3;2;3;3;2;3] beta_lin) 0 thenT rw (addrC [1;2;3;2;3;3;2] aux_advance_sink_guard) 0);;
