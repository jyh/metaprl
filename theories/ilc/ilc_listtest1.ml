extends Ilc_extend

interactive t1:
  ilc{| >- linear {| tensor{Lin{'x1;'x2}; Lin{'y1;'y2}} >- tensor{top;circ{"not"{beq_int{'x1;'y1}}}} |} |}

interactive t2:
  ilc{| >- linear {| Lin{'y1;'y2}; Array{'x1;'x2;'x3}  >- circ{"not"{beq_int{'y1;'x1}}}|}|}

interactive t3:
  ilc{| >- linear {| Array{'y1;'y2;'y3}; Array{'x1;'x2;'x3}  >- circ{"not"{beq_int{'y1;'x1}}}|}|}

interactive t4:
  ilc{| circ{"not"{beq_int{'x1;'x2}}} >-
  linear {| Lin{'y1;'y2}; List{'x1;'x2;'x3}  >- circ{"not"{beq_int{'y1;'x1}}}|}|}

interactive t5:
  ilc{| circ{"not"{beq_int{'x1;'x2}}} >-
  linear {| Array{'y1;'y2;'y3}; List{'x1;'x2;'x3}  >- circ{"not"{beq_int{'y1;'x1}}}|}|}

interactive t6:
  ilc{| circ{"not"{beq_int{'y1;'x2}}} >-
  linear {| Lin{'y1;'y2}; List{'x1;'x2;'x3}  >- circ{"not"{beq_int{'y1;'x1}}}|}|}

interactive t7:
  ilc{| circ{"not"{beq_int{'y1;'x2}}} >-
  linear {| Array{'y1;'y2;'y3}; List{'x1;'x2;'x3}  >- circ{"not"{beq_int{'y1;'x1}}}|}|}

interactive t8:
  ilc{| circ{"not"{beq_int{'y1;'y2}}} >-
  linear {| List{'y1;'y2;'y3}; List{'x1;'x2;'x3}  >- circ{"not"{beq_int{'y1;'x1}}}|}|}

interactive t9:
  ilc{| circ{"not"{beq_int{'x1;'x2}}} >-
  linear {| List{'y1;'y2;'y3}; List{'x1;'x2;'x3}  >- circ{"not"{beq_int{'y1;'x1}}}|}|}

interactive t10:
  ilc{| circ{"not"{beq_int{'x2;'y2}}} >-
  linear {| List{'y1;'y2;'y3}; List{'x1;'x2;'x3}  >- circ{"not"{beq_int{'y1;'x1}}}|}|}
