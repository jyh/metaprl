doc <:doc<
   @module[Itt_bintree]

   This is a theory of binary trees.
>>

extends Itt_record
extends Itt_algebra_df
extends Itt_srec
extends Itt_bisect
extends Itt_struct
extends Itt_labels

doc docoff

open Lm_debug
open Lm_printf

open Basic_tactics

open Itt_struct

doc <:doc<
   @modsection{Simple Trees}
   @modsection{Basic Definitions}
>>

define nodetype: Node{'T} <--> {left:'T; right:'T}

define bintree: BinTree <--> srec{T.Node{'T} + unit}

interactive_rw unfold_bintree: BinTree <--> srec{T. {left:'T; right:'T} + unit}


define emptytree: emptytree <--> inr{it}


define tree: tree{'node} <--> inl{'node}


define indtree: tree_ind{'tree; 'empty; L,R,node. 'f['L;'R;'node]} <-->
    srecind{'tree;
      p,t. decide{'t;
                   node.'f['p('node^left); 'p('node^right); 'node];
                   "it". 'empty}
           }


interactive_rw reduce_indtree_empty {| reduce |} :
   tree_ind{emptytree; 'empty_case; L,R,node. 'f['L;'R;'node]} <--> 'empty_case

interactive_rw reduce_indtree_node {| reduce |} :
   tree_ind{tree{'node}; 'empty_case; L,R,node. 'f['L;'R;'node]} <-->
   'f[ tree_ind{('node^left); 'empty_case; L,R,node. 'f['L;'R;'node]};
       tree_ind{('node^right); 'empty_case; L,R,node. 'f['L;'R;'node]};
       'node
     ]

doc docoff

dform nodetype_df : except_mode[src] :: Node{'T} = `"Node(" 'T ")"

dform bintree_df : except_mode[src] :: BinTree = `"BinTree"

dform emptytree_df : except_mode[src] :: emptytree = `"NIL"

dform tree_df : except_mode[src] :: tree{'T} = `"tree(" 'T ")"

dform indtree_df : except_mode[src] :: tree_ind{'tree; 'empty; L,R,node. 'f} =
   szone pushm[0] pushm[3] `"match" " " slot{'tree} " " `"with" hspace
   emptytree `" -> " slot{'empty} popm hspace
   pushm[3] `" | " 'L `"." 'R `"." tree{'node} `" -> " slot{'f} popm popm ezone

doc <:doc<
   @modsubsection{Basic Rules}
>>

interactive node_wf {| intro[] |}:
 sequent{ <H> >-"type"{ 'T}} -->
 sequent{ <H> >-"type"{ Node{'T}}}

interactive node_monotone {| intro[] |} :
 sequent{ <H> >-'S subtype 'T} -->
 sequent{ <H> >- Node{'S} subtype Node{'T}}

interactive bintree_wf {| intro[] |} :
 sequent{ <H> >-"type"{ BinTree}}

doc <:doc<
   @modsubsection{Functions on trees}
>>

define match_tree: match_tree{'t; 'empty_case; self.'nonempty_case['self]} <--> tree_ind{'t; 'empty_case; L,R,self.'nonempty_case['self]}

interactive_rw reduce_matchtree_empty : match_tree{emptytree; 'empty; node. 'f['node]} <--> 'empty

interactive_rw reduce_matchtree_node : match_tree{tree{'node}; 'empty; node. 'f['node]} <--> 'f['node]

define leftSubtree: leftSubtree{'t} <-->  match_tree{'t; emptytree; self. ^left}

define rightSubtree: rightSubtree{'t} <-->  match_tree{'t; emptytree; self. ^right}

interactive_rw reduce_leftSubtree_empty : leftSubtree{emptytree} <--> emptytree

interactive_rw reduce_rightSubtree_empty : rightSubtree{emptytree} <--> emptytree

define weight : weight{'t} <--> tree_ind{'t; 0; L,R,node. 'L +@ 'R +@ 1}

interactive weight_wf {| intro[] |} :
 sequent{ <H> >-'t in BinTree} -->
 sequent{ <H> >-weight{'t} in int}

doc docoff

dform match_tree_df : except_mode[src] :: match_tree{'t; 'empty_case; node.'nonempty_case} =
   szone pushm[0] pushm[3] `"match" " " slot{'t} " " `"with" hspace
   emptytree `" -> " slot{'empty_case} popm hspace
   pushm[3] `" | " tree{'node} `" -> " slot{'nonempty_case} popm popm ezone

dform weight_df : except_mode[src] :: weight{'T} = `"weight(" 'T ")"
dform ltree_df : except_mode[src] :: leftSubtree{'T} = `"leftSubtree(" 'T ")"
dform rtree_df : except_mode[src] :: rightSubtree{'T} = `"rightSubtree(" 'T ")"

(*
define height : height{'t} <--> tree_ind{'t; 0; L,R,node. max{'L;'R} +@ 1}

interactive height_wf {| intro[] |} :
 sequent{ <H> >-'t in BinTree} -->
 sequent{ <H> >-height{'t} in int}

interactive height_weight  {| intro[] |} : (* make two theorems *)
 sequent{ <H> >-'t in BinTree} -->
 sequent{ <H> >-height{'t} <= weight{'t} & weight{'t}< power{2;height{'t}}}
*)



(* ==================== *)

doc <:doc<
   @modsubsection{Example}
>>

(*     17     *)
(*      \     *)
(*       19   *)

define example: simpletree <--> tree{ {data=17; left=emptytree; right=tree{ {data=19; left=emptytree; right=emptytree} }} }

interactive_rw example_weight : weight{simpletree} <--> 2

interactive example_wf  {| intro[] |} :
 sequent{ <H> >- simpletree in BinTree }

doc docoff

dform simpletree_df : except_mode[src] :: simpletree = `"simpletree"

(* ==================== *)
doc <:doc<
   @modsection{Parametrized trees}
   @modsubsection{Definitions}
>>

define node: node{'l;'r;'nd} <--> ( ('nd^left:='l)^right:='r )

define nodetype2: Node{'T;l,r.'R['l;'r]} <--> record["left":t]{'T; l.record["right":t]{'T;r.'R['l;'r]}}

define nodetype3: Node{'T;'A} <--> Node{'T; l,r.'A}

define bintree2: BinTree{l,r.'R['l;'r]} <--> srec{T.Node{'T;l,r.'R['l;'r]} + unit}

define bintree3: BinTree{'R} <-->  BinTree{l,r.'R}

define bintree4 : BinTree{'A; t.'P['t]} <--> BinTree{l,r. {a:'A |  'P[node{'l;'r;'a}] } }

doc docoff

dform node_df : except_mode[src] :: node{'l;'r;'nd} = `"node(" 'l `"," 'r `"," 'nd ")"

let resource reduce +=
   <<  field[label:t]{node{'l;'r;'nd}}  >>, wrap_reduce (addrC [Subterm 1] node thenC reduceTopC);

dform node_df : except_mode[src] :: Node{'T;l,r.'R} = `"Node(" 'T `"; " 'l `"," 'r `"." 'R ")"

dform node_df : except_mode[src] :: Node{'T;'A} = `"Node(" 'T `"; " 'A ")"

dform bt2_df : except_mode[src] :: BinTree{l,r.'R} = `"BinTree(" 'l `"," 'r `"." 'R ")"
dform bt3_df : except_mode[src] :: BinTree{'R} = `"BinTree(" 'R ")"
dform bt4_df : except_mode[src] :: BinTree{'S;t.'P} = `"BinTree(" 'S `" | " 't `"." 'P ")"

let resource intro +=
   [<< 'a='b in Node{'T;l,r.'R['l;'r]} >>, wrap_intro (rwh nodetype2 0 thenT dT 0)]

let resource elim +=
   << Node{'T;l,r.'R['l;'r]} >>, wrap_elim (fun n -> rw nodetype2 n thenT dT n)

doc rules

interactive tree_monotone2 {| intro[] |} :
 sequent{ <H> >-"type"{ BinTree{l,r.'S['l;'r]}} }  -->
 sequent{ <H>; l:BinTree{l,r.'S['l;'r]}; r:BinTree{l,r.'S['l;'r]} >-  'R['l;'r] subtype 'S['l;'r] }  -->
 sequent{ <H> >- BinTree{l,r.'R['l;'r]}  subtype BinTree{l,r.'S['l;'r]}}

interactive tree_monotone3 {| intro[] |} :
 sequent{ <H> >-'R subtype 'S} -->
 sequent{ <H> >-BinTree{'R}  subtype BinTree{'S}}

interactive tree_wf2 {| intro[] |}  BinTree{l,r.'S['l;'r]} :
 sequent{ <H> >-"type"{ BinTree{l,r.'S['l;'r]}} }  -->
 sequent{ <H>; l:BinTree{l,r.'S['l;'r]}; r:BinTree{l,r.'S['l;'r]} >- "subtype"{ 'R['l;'r]; 'S['l;'r]} }  -->
 sequent{ <H> >-"type"{ BinTree{l,r.'R['l;'r]}}}

interactive tree_wf3 {| intro[] |} :
 sequent{ <H> >-"type"{ 'R}} -->
 sequent{ <H> >-"type"{ BinTree{'R}}}

interactive tree_subtype {| intro[] |} :
 sequent{ <H> >- "type"{ BinTree{l,r.'R['l;'r]}}} -->
 sequent{ <H> >- "subtype"{ BinTree{l,r.'R['l;'r]};BinTree}}

interactive emptytree_wf  {| intro[] |} :
 sequent{ <H> >-"type"{ BinTree{l,r.'R['l;'r]}} }  -->
 sequent{ <H> >-emptytree in BinTree{l,r.'R['l;'r]} }

interactive tree_wf  {| intro[] |} :
 [wf] sequent{ <H> >-"type"{ BinTree{l,r.'R['l;'r]}} }  -->
 sequent{ <H> >-'node in Node{BinTree{l,r.'R['l;'r]}; l,r.'R['l;'r]} }  -->
 sequent{ <H> >-tree{'node} in BinTree{l,r.'R['l;'r]} }

interactive tree4_wf  {| intro[] |} :
 [wf] sequent{ <H> >-"type"{ BinTree{'A;t.'P['t]}} }   -->
 sequent{ <H> >-'node in Node{ BinTree{'A;t.'P['t]}; l,r. {a:'A |  'P[node{'l;'r;'a}] } } }  -->
 sequent{ <H> >-tree{'node} in  BinTree{'A;t.'P['t]} }

interactive node_wf2  {| intro[] |} :
 sequent{ <H> >- 'l in 'T }  -->
 sequent{ <H> >- 'r in 'T }  -->
 sequent{ <H> >- 'nd in 'R['l;'r] }  -->
 sequent{ <H> >-node{'l;'r;'nd} in Node{'T;ll,rr.'R['ll;'rr]} }

doc <:doc<
   Induction rule
>>

interactive treeInduction {| elim [ThinOption thinT] |} 'H :
    sequent{ <H>; t: BinTree{l,r.'R['l;'r]};  <J['t]> >-  'C[emptytree]} -->
    sequent{ <H>; t: BinTree{l,r.'R['l;'r]};  <J['t]>; l:BinTree{l,r.'R['l;'r]}; r:BinTree{l,r.'R['l;'r]}; node:'R['l;'r]; L: 'C['l]; R: 'C['r]
                       >-  'C[tree{node{'l;'r;'node}}] } -->
    sequent{ <H>; t: BinTree{l,r.'R['l;'r]};  <J['t]> >-  'C['t]}

interactive treeInduction2 {| elim [ThinOption thinT] |} 'H :
    sequent{ <H>; t: BinTree{'A; t.'P['t]};  <J['t]> >-  'C[emptytree]} -->
    sequent{ <H>; t: BinTree{'A; t.'P['t]};  <J['t]>;
                    l:BinTree{'A; t.'P['t]}; r:BinTree{'A; t.'P['t]}; node: 'A; u: squash{'P[node{'l;'r;'node}]}; L: 'C['l]; R: 'C['r]
                       >-  'C[tree{node{'l;'r;'node}}] } -->
    sequent{ <H>; t: BinTree{'A; t.'P['t]};  <J['t]> >-  'C['t]}

interactive treeInduction1 {| elim [ThinOption thinT] |} 'H :
    sequent{ <H>; t: BinTree;  <J['t]> >-  'C[emptytree]} -->
    sequent{ <H>; t: BinTree;  <J['t]>; l:BinTree; r:BinTree; L: 'C['l]; R: 'C['r]
                       >-  'C[tree{{left = 'l; right = 'r }}] } -->
    sequent{ <H>; t: BinTree;  <J['t]> >-  'C['t]}

doc docoff

(* ==================== *)
