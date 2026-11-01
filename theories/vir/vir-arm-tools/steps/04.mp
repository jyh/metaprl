cd "/vir/vir/guard_merge_c";;
refine (rw (sweepDnC (unfold_vguard orelseC unfold_band)) 0 thenT splitBoolT <<'c1>> 0 thenMT rw reduceC 0 ttca);;
cd "../aux_guard_swap";;
refine (rw (sweepDnC unfold_vguard) 0 thenT splitBoolT <<'c1>> 0 thenMT splitBoolT <<'c2>> 0 thenMT rw reduceC 0 ttca);;
cd "../slice_fuse_c";;
refine (sqSubstT << 'b ~ pair{fst{'b}; snd{'b}} >> 0);;
ls "";;
