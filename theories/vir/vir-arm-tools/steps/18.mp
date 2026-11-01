cd "/vir/vir/router_fuse";;
refine (rw (sweepDnC (unfold_vir_U orelseC unfold_vir_F)) 0 thenT rw (sweepDnC (unfold_parse_header orelseC unfold_check_rate_limit orelseC unfold_verify_acl orelseC unfold_emit_payload)) 0 thenT rw (addrC [1;2;3;2;3;3] aux_advance_sink_guard) 0 thenT rw (addrC [1;2;3;2;3;3;2;3] beta_lin) 0 thenT rw (addrC [1;2;3;2;3;3;2] aux_advance_sink_guard) 0 thenT rw (addrC [1;2;3;2;3;3;2;2] slice_fuse_c) 0 thenMT rw (addrC [1;2;3;2;3;3;2;2;2] reduceC) 0 thenMT rw (repeatC (higherC unfold_read_u32)) 0 thenMT rw (addrC [1;2;2] aux_guard_swap) 0 thenMT rw (addrC [1;2;2] guard_merge_c) 0 thenMT rw (addrC [1;2] guard_merge_c) 0 thenMT rw (higherC beta_lin) 0 thenT assumT 1 thenT assumT 2 thenT assumT 3 thenT assumT 4 thenT autoT);;
cd "..";;
export ();;
status_all ();;
