cd "/vir/vir/slice_fuse_c";;
refine (rw (sweepDnC unfold_advance) 0 thenT rw reduceC 0 thenT rw (sweepDnC unfold_advance) 0 thenT rw reduceC 0 thenT rw (higherC add_Assoc2C) 0 thenLT [logicAutoT; assumT 1 thenT rwh unfoldSnd 0 thenT spreadEquality <<bind{q. int}>> <<top * int>> thenT autoT; assumT 2 thenT autoT; assumT 3 thenT autoT]);;
ls "";;
cd "..";;
export ();;
status_all ();;
