doc <:doc< 
   @begin[doc]
   @module[Itt_bintree]
  
   This is a theory of binary trees.
   @end[doc]
>>

extends Itt_record
extends Itt_algebra_df
extends Itt_srec
extends Itt_bisect
extends Itt_struct

doc <:doc< @docoff >>

open Printf
open Mp_debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError
open Mp_resource

open Var
open Tactic_type
open Tactic_type.Tacticals
open Base_dtactic
open Tactic_type.Conversionals
open Top_conversionals

open Base_auto_tactic

open Itt_record
open Itt_bisect
open Itt_srec
open Itt_union
open Itt_struct

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_bintree%t"



doc <:doc< 
   @begin[doc]
   @modsection{Simple Trees}
   @modsection{Basic Definitions}
   @end[doc]
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


interactive_rw reduce_indtree_empty : tree_ind{emptytree; 'empty_case; L,R,node. 'f['L;'R;'node]} <--> 'empty_case

interactive_rw reduce_indtree_node : tree_ind{tree{'node}; 'empty_case; L,R,node. 'f['L;'R;'node]} <-->
   'f[ tree_ind{('node^left); 'empty_case; L,R,node. 'f['L;'R;'node]};
       tree_ind{('node^right); 'empty_case; L,R,node. 'f['L;'R;'node]};
       'node
     ]


doc <:doc< @docoff >>

dform nodetype_df : except_mode[src] :: Node{'T} = `"Node(" 'T ")"

dform bintree_df : except_mode[src] :: BinTree = `"BinTree"

dform emptytree_df : except_mode[src] :: emptytree = `"NIL"

dform tree_df : except_mode[src] :: tree{'T} = `"tree(" 'T ")"

dform indtree_df : except_mode[src] :: tree_ind{'tree; 'empty; L,R,node. 'f} =
   szone pushm[0] pushm[3] `"match" " " slot{'tree} " " `"with" hspace
   emptytree `" -> " slot{'empty} popm hspace
   pushm[3] `" | " 'L `"." 'R `"." tree{'node} `" -> " slot{'f} popm popm ezone


let resource reduce +=
   [<<  tree_ind{emptytree; 'empty; L,R,node. 'f['L;'R;'node]}  >>, reduce_indtree_empty;
    <<  tree_ind{tree{'node}; 'empty; L,R,node. 'f['L;'R;'node]}  >>, reduce_indtree_node
   ]


doc <:doc< 
   @begin[doc]
   @modsubsection{Basic Rules}
   @end[doc]
>>


interactive node_wf {| intro[] |}:
 sequent[squash]{ <H> >-"type"{ 'T}} -->
 sequent['ext]  { <H> >-"type"{ Node{'T}}}

interactive node_monotone {| intro[] |} :
 sequent[squash]{ <H> >-'S subtype 'T} -->
 sequent['ext]  { <H> >- Node{'S} subtype Node{'T}}

interactive bintree_wf {| intro[] |} :
 sequent['ext]  { <H> >-"type"{ BinTree}}


doc <:doc< 
   @begin[doc]
   @modsubsection{Functions on trees}
   @end[doc]
>>


define match_tree: match_tree{'t; 'empty_case; self.'nonempty_case['self]} <--> tree_ind{'t; 'empty_case; L,R,self.'nonempty_case['self]}

dform match_tree_df : except_mode[src] :: match_tree{'t; 'empty_case; node.'nonempty_case} =
   szone pushm[0] pushm[3] `"match" " " slot{'t} " " `"with" hspace
   emptytree `" -> " slot{'empty_case} popm hspace
   pushm[3] `" | " tree{'node} `" -> " slot{'nonempty_case} popm popm ezone


interactive_rw reduce_matchtree_empty : match_tree{emptytree; 'empty; node. 'f['node]} <--> 'empty

interactive_rw reduce_matchtree_node : match_tree{tree{'node}; 'empty; node. 'f['node]} <--> 'f['node]

define leftSubtree: leftSubtree{'t} <-->  match_tree{'t; emptytree; self. ^left}

define rightSubtree: rightSubtree{'t} <-->  match_tree{'t; emptytree; self. ^right}


dform ltree_df : except_mode[src] :: leftSubtree{'T} = `"leftSubtree(" 'T ")"
dform rtree_df : except_mode[src] :: rightSubtree{'T} = `"rightSubtree(" 'T ")"


interactive_rw reduce_leftSubtree_empty : leftSubtree{emptytree} <--> emptytree

interactive_rw reduce_rightSubtree_empty : rightSubtree{emptytree} <--> emptytree




define weight : weight{'t} <--> tree_ind{'t; 0; L,R,node. 'L +@ 'R +@ 1}

dform weight_df : except_mode[src] :: weight{'T} = `"weight(" 'T ")"


interactive weight_wf {| intro[] |} :
 sequent[squash]{ <H> >-'t in BinTree} -->
 sequent['ext]  { <H> >-weight{'t} in int}

(*
define height : height{'t} <--> tree_ind{'t; 0; L,R,node. max{'L;'R} +@ 1}

interactive height_wf {| intro[] |} :
 sequent[squash]{ <H> >-'t in BinTree} -->
 sequent['ext]  { <H> >-height{'t} in int}

interactive height_weight  {| intro[] |} : (* make two theorems *)
 sequent[squash]{ <H> >-'t in BinTree} -->
 sequent['ext]  { <H> >-height{'t} <= weight{'t} & weight{'t}< power{2;height{'t}}}
*)



(* ==================== *)

doc <:doc< 
   @begin[doc]
   @modsubsection{Example}
   @end[doc]
>>

(*     17     *)
(*      \     *)
(*       19   *)

define example: simpletree <--> tree{.{data=17; left=emptytree; right=tree{.{data=19; left=emptytree; right=emptytree}}}}

dform simpletree_df : except_mode[src] :: simpletree = `"simpletree"


interactive_rw example_weight : weight{simpletree} <--> 2

interactive example_wf  {| intro[] |} :
 sequent['ext]  { <H> >- simpletree in BinTree }



(* ==================== *)
doc <:doc< 
   @begin[doc]
   @modsection{Parametrized trees}
   @modsubsection{Definitions}
   @end[doc]
>>

define node: node{'l;'r;'nd} <--> ( ('nd^left:='l)^right:='r )

dform node_df : except_mode[src] :: node{'l;'r;'nd} = `"node(" 'l `"," 'r `"," 'nd ")"


let resource reduce +=
   [<<  field[l:t]{node{'l;'r;'nd}}  >>, (addrC [0] node thenC reduceTopC);
   ]

define nodetype2: Node{'T;l,r.'R['l;'r]} <--> record["left":t]{'T; l.record["right":t]{'T;r.'R['l;'r]}}

dform node_df : except_mode[src] :: Node{'T;l,r.'R} = `"Node(" 'T `"; " 'l `"," 'r `"." 'R ")"

define nodetype3: Node{'T;'A} <--> Node{'T; l,r.'A}

dform node_df : except_mode[src] :: Node{'T;'A} = `"Node(" 'T `"; " 'A ")"


define bintree2: BinTree{l,r.'R['l;'r]} <--> srec{T.Node{'T;l,r.'R['l;'r]} + unit}

define bintree3: BinTree{'R} <-->  BinTree{l,r.'R}

define bintree4 : BinTree{'A; t.'P['t]} <--> BinTree{l,r. {a:'A |  'P[node{'l;'r;'a}] } }

dform bt2_df : except_mode[src] :: BinTree{l,r.'R} = `"BinTree(" 'l `"," 'r `"." 'R ")"
dform bt3_df : except_mode[src] :: BinTree{'R} = `"BinTree(" 'R ")"
dform bt4_df : except_mode[src] :: BinTree{'S;t.'P} = `"BinTree(" 'S `" | " 't `"." 'P ")"

let resource intro +=
   [<< 'a='b in Node{'T;l,r.'R['l;'r]} >>, wrap_intro (rwh nodetype2 0 thenT dT 0)]

let resource elim +=
   << Node{'T;l,r.'R['l;'r]} >>, (fun n -> rw nodetype2 n thenT dT n)

doc <:doc< 
   @begin[doc]
   @modsubsection{Rules}
   @end[doc]
>>


interactive tree_monotone2 {| intro[] |} :
 sequent[squash]{ <H> >-"type"{ BinTree{l,r.'S['l;'r]}} }  -->
 sequent[squash]{ <H>; l:BinTree{l,r.'S['l;'r]}; r:BinTree{l,r.'S['l;'r]} >-  'R['l;'r] subtype 'S['l;'r] }  -->
 sequent['ext]  { <H> >- BinTree{l,r.'R['l;'r]}  subtype BinTree{l,r.'S['l;'r]}}

interactive tree_monotone3 {| intro[] |} :
 sequent[squash] { <H> >-'R subtype 'S} -->
 sequent['ext]  { <H> >-BinTree{'R}  subtype BinTree{'S}}

interactive tree_wf2 {| intro[] |}  BinTree{l,r.'S['l;'r]} :
 sequent[squash]{ <H> >-"type"{ BinTree{l,r.'S['l;'r]}} }  -->
 sequent[squash]{ <H>; l:BinTree{l,r.'S['l;'r]}; r:BinTree{l,r.'S['l;'r]} >- "subtype"{ 'R['l;'r]; 'S['l;'r]} }  -->
 sequent['ext]  { <H> >-"type"{ BinTree{l,r.'R['l;'r]}}}

interactive tree_wf3 {| intro[] |} :
 sequent[squash]{ <H> >-"type"{ 'R}} -->
 sequent['ext]  { <H> >-"type"{ BinTree{'R}}}

interactive tree_subtype {| intro[] |} :
 sequent[squash]{ <H> >- "type"{ BinTree{l,r.'R['l;'r]}}} -->
 sequent['ext]  { <H> >- "subtype"{ BinTree{l,r.'R['l;'r]};BinTree}}

interactive emptytree_wf  {| intro[] |} :
 sequent[squash]{ <H> >-"type"{ BinTree{l,r.'R['l;'r]}} }  -->
 sequent['ext]  { <H> >-emptytree in BinTree{l,r.'R['l;'r]} }

interactive tree_wf  {| intro[] |} :
 [wf] sequent[squash]{ <H> >-"type"{ BinTree{l,r.'R['l;'r]}} }  -->
 sequent[squash]{ <H> >-'node in Node{BinTree{l,r.'R['l;'r]}; l,r.'R['l;'r]} }  -->
 sequent['ext]  { <H> >-tree{'node} in BinTree{l,r.'R['l;'r]} }

interactive tree4_wf  {| intro[] |} :
 [wf] sequent[squash]{ <H> >-"type"{ BinTree{'A;t.'P['t]}} }   -->
 sequent[squash]{ <H> >-'node in Node{ BinTree{'A;t.'P['t]}; l,r. {a:'A |  'P[node{'l;'r;'a}] } } }  -->
 sequent['ext]  { <H> >-tree{'node} in  BinTree{'A;t.'P['t]} }



interactive node_wf2  {| intro[] |} :
 sequent[squash]{ <H> >- 'l in 'T }  -->
 sequent[squash]{ <H> >- 'r in 'T }  -->
 sequent[squash]{ <H> >- 'nd in 'R['l;'r] }  -->
 sequent['ext]  { <H> >-node{'l;'r;'nd} in Node{'T;l,r.'R['l;'r]} }

doc <:doc< 
   @begin[doc]
   Induction rule
   @end[doc]
>>

interactive treeInduction {| elim [ThinOption thinT] |} 'H :
    sequent['ext]  { <H>; t: BinTree{l,r.'R['l;'r]};  <J['t]> >-  'C[emptytree]} -->
    sequent['ext]  { <H>; t: BinTree{l,r.'R['l;'r]};  <J['t]>; l:BinTree{l,r.'R['l;'r]}; r:BinTree{l,r.'R['l;'r]}; node:'R['l;'r]; L: 'C['l]; R: 'C['r]
                       >-  'C[tree{node{'l;'r;'node}}] } -->
    sequent['ext]  { <H>; t: BinTree{l,r.'R['l;'r]};  <J['t]> >-  'C['t]}


interactive treeInduction2 {| elim [ThinOption thinT] |} 'H :
    sequent['ext]  { <H>; t: BinTree{'A; t.'P['t]};  <J['t]> >-  'C[emptytree]} -->
    sequent['ext]  { <H>; t: BinTree{'A; t.'P['t]};  <J['t]>;
                    l:BinTree{'A; t.'P['t]}; r:BinTree{'A; t.'P['t]}; node: 'A; u: squash{'P[node{'l;'r;'node}]}; L: 'C['l]; R: 'C['r]
                       >-  'C[tree{node{'l;'r;'node}}] } -->
    sequent['ext]  { <H>; t: BinTree{'A; t.'P['t]};  <J['t]> >-  'C['t]}


interactive treeInduction1 {| elim [ThinOption thinT] |} 'H :
    sequent['ext]  { <H>; t: BinTree;  <J['t]> >-  'C[emptytree]} -->
    sequent['ext]  { <H>; t: BinTree;  <J['t]>; l:BinTree; r:BinTree; L: 'C['l]; R: 'C['r]
                       >-  'C[tree{{left = 'l; right = 'r }}] } -->
    sequent['ext]  { <H>; t: BinTree;  <J['t]> >-  'C['t]}


(* ==================== *)




