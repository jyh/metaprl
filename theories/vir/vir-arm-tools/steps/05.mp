cd "/vir/vir/slice_fuse_c";;
refine (sqSubstT << 'b ~ pair{fst{'b}; snd{'b}} >> 0 thenLT [autoT; rw (sweepDnC unfold_advance) 0 thenT rw reduceC 0 thenT sqSubstT << (snd{'b} +@ 'i) +@ 'j ~ snd{'b} +@ ('i +@ 'j) >> 0 thenT autoT]);;
ls "";;
