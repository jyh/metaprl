extends Ilc_core
extends Ilc_term

prim add_neq 'a 'b:
  ilc{| <H>; circ{"not"{beq_int{'a;'b}}} >- linear{| <L> >- 'C|} |} -->
    ilc{| <H> >- linear{| <L> >- 'C|} |}

prim sep_ll 'L 'J:
   ilc{| <H>; circ{"not"{beq_int{'a;'x}}} >-
	 linear{| <L>; Lin{'a;'b}; <J>; Lin{'x;'y}; <M> >- 'C |} |} -->
	   ilc{| <H> >- linear{| <L>; Lin{'a;'b}; <J> ;Lin{'x;'y};<M> >- 'C |} |}

 prim sep_aa 'L 'J:
    ilc{| <H>; circ{"not"{beq_int{'a;'x}}} >-
 	 linear{| <L>; Array{'a;'b;'c}; <J>; Array{'x;'y;'z}; <M> >- 'C |} |} -->
 	   ilc{| <H> >- linear{| <L>; Array{'a;'b;'c}; <J>; Array{'x;'y;'z};<M> >- 'C |} |}

 prim sep_la 'L 'J:
    ilc{| <H>; circ{"not"{beq_int{'a;'x}}} >-
 	 linear{| <L>; Lin{'a;'b}; <J>; Array{'x;'y;'z}; <M> >- 'C |} |} -->
 	   ilc{| <H> >- linear{| <L>; Lin{'a;'b}; <J>; Array{'x;'y;'z};<M> >- 'C |} |}

 prim sep_llst1 'H 'L 'J :
    ilc{| <H>; circ{"not"{beq_int{'x;'y}}}; <M1>;circ{"not"{beq_int{'a;'x}}} >-
 	 linear{| <L>; Lin{'a;'b}; <J>;List{'x;'y;'z}; <M2> >- 'C |} |} -->
 	   ilc{| <H> ;circ{"not"{beq_int{'x;'y}}};<M1> >-
 		      linear{| <L>; Lin{'a;'b};<J>; List{'x;'y;'z};<M2> >- 'C |} |}


prim sep_llst2 'H 'L 'J :
    ilc{| <H>; circ{"not"{beq_int{'a;'y}}}; <M1>;circ{"not"{beq_int{'a;'x}}} >-
 	 linear{| <L>; Lin{'a;'b}; <J>;List{'x;'y;'z}; <M2> >- 'C |} |} -->
 	   ilc{| <H> ; circ{"not"{beq_int{'a;'y}}}; <M1> >-
 		      linear{| <L>; Lin{'a;'b};<J>; List{'x;'y;'z};<M2> >- 'C |} |}

prim sep_alst1 'H 'L 'J :
    ilc{| <H>; circ{"not"{beq_int{'x;'y}}}; <M1>;circ{"not"{beq_int{'a;'x}}} >-
 	 linear{| <L>; Array{'a;'b;'c}; <J>;List{'x;'y;'z}; <M2> >- 'C |} |} -->
 	   ilc{| <H> ;circ{"not"{beq_int{'x;'y}}};<M1> >-
 		      linear{| <L>; Array{'a;'b;'c};<J>; List{'x;'y;'z};<M2> >- 'C |} |}


prim sep_alst2 'H 'L 'J :
    ilc{| <H>; circ{"not"{beq_int{'a;'y}}}; <M1>;circ{"not"{beq_int{'a;'x}}} >-
 	 linear{| <L>; Array{'a;'b;'c}; <J>;List{'x;'y;'z}; <M2> >- 'C |} |} -->
 	   ilc{| <H> ; circ{"not"{beq_int{'a;'y}}}; <M1> >-
 		      linear{| <L>; Array{'a;'b;'c};<J>; List{'x;'y;'z};<M2> >- 'C |} |}


prim sep_lstlst1 'H 'L 'J :
    ilc{| <H>; circ{"not"{beq_int{'x;'y}}}; <M1>;circ{"not"{beq_int{'a;'x}}} >-
 	 linear{| <L>; List{'a;'b;'c}; <J>;List{'x;'y;'z}; <M2> >- 'C |} |} -->
 	   ilc{| <H> ;circ{"not"{beq_int{'x;'y}}};<M1> >-
 		      linear{| <L>; List{'a;'b;'c};<J>; List{'x;'y;'z};<M2> >- 'C |} |}

prim sep_lstlst2 'H 'L 'J :
    ilc{| <H>; circ{"not"{beq_int{'a;'b}}}; <M1>;circ{"not"{beq_int{'a;'x}}} >-
 	 linear{| <L>; List{'a;'b;'c}; <J>;List{'x;'y;'z}; <M2> >- 'C |} |} -->
 	   ilc{| <H> ;circ{"not"{beq_int{'a;'b}}};<M1> >-
 		      linear{| <L>; List{'a;'b;'c};<J>; List{'x;'y;'z};<M2> >- 'C |} |}


prim sep_lstlst3 'H 'L 'J :
    ilc{| <H>; circ{"not"{beq_int{'b;'y}}}; <M1>;circ{"not"{beq_int{'a;'x}}} >-
 	 linear{| <L>; List{'a;'b;'c}; <J>;List{'x;'y;'z}; <M2> >- 'C |} |} -->
 	   ilc{| <H> ; circ{"not"{beq_int{'b;'y}}}; <M1> >-
 		      linear{| <L>; List{'a;'b;'c};<J>; List{'x;'y;'z};<M2> >- 'C |} |}

