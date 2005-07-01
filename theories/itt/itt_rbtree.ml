doc <:doc<
   @module[Itt_rbtree]

   This is a theory of red-black trees.
>>

extends Itt_sortedtree
extends Itt_bintree
extends Itt_relation_str
extends Itt_set_str
extends Itt_record
extends Itt_logic
extends Itt_bisect
extends Itt_tunion
extends Itt_nat
extends Itt_labels

doc docoff

open Lm_debug
open Lm_printf

open Tactic_type.Tacticals
open Dtactic
open Top_conversionals

open Itt_bintree

let dByDefT  unfold n = rw unfold n thenT dT n
let dByRecDefT term unfold n = dByDefT unfold n thenT rwhAll (makeFoldC term unfold)

let soft_elim term unfold = term, (dByDefT unfold)
let soft_into term unfold = term, (dByDefT unfold 0)
let softrec_elim term unfold = term, (dByRecDefT term unfold)
let softrec_into term unfold = term, (dByRecDefT term unfold 0)

let reduceByDefC unfold =   unfold thenC reduceTopC
let reduceByRecDefC term unfold = reduceByDefC unfold thenC higherC (makeFoldC term unfold)

let soft_reduce term unfold  = term, (reduceByDefC unfold)
let softrec_reduce term unfold  = term, (reduceByRecDefC term unfold)

(*
 * Show that the file is loading.
 *)
let _ =
   show_loading "Loading Itt_redblacktree%t"

doc <:doc<
   @modsection{Definitions of Red-Black Trees}
   @modsubsection{Color}
>>

define color: Color <--> unit + unit

define black: black  <--> inl{it}
define red: red  <--> inr{it}

define black_type: Black  <--> unit + void
define red_type: Red <--> void + unit

define black_or_red: black_or_red{'color; 'black_case; 'red_case} <--> decide{'color; b.'black_case; r.'red_case}

interactive_rw if_black {| reduce |} :  black_or_red{black; 'black_case; 'red_case} <--> 'black_case
interactive_rw if_red {| reduce |} :  black_or_red{red; 'black_case; 'red_case} <--> 'red_case

define sons_type: sons_type{'parent_color}  <--> black_or_red{'parent_color; Color; Black}   (* Son of a red parent is black, son of a black parent may have any color *)

define cost: cost{'color}  <-->  black_or_red{'color; 1; 0}

doc <:doc<
   @modsubsection{Red-black Tree}
   Red-black tree is a tree that satisfy the following conditions:
   @begin[enumerate]

    @item{Each node has a color: red or black;}
    @item{ Any child of a red color is black;}
    @item{ All paths from the root to any leaf have the same number of black nodes.}
   @end[enumerate]
>>

define rbtree: RBTreeOf{'A} <--> fix {rbtree. lambda {n. lambda {parent_color.
                       if beq_int{'n;.  -1}
                         then void
                         else
                           record["color":t]{ sons_type{'parent_color}; color.Node{'rbtree ('n -@ cost{'color}) 'color; 'A}}  +
                            (if beq_int{'n;  0} then unit else void)
                         }}}

define btree1: BTree{'A;'n} <--> RBTreeOf{'A} 'n red           (* Red-black tree with a black root *)

define rbtree1: RBTree{'A;'n} <--> RBTreeOf{'A} 'n black        (* Red-black tree with an arbitary root *)

define btree2: BTree{'A} <--> tunion{ nat; n.BTree{'A;'n} }

define rbtree2: RBTree{'A} <--> tunion{ nat; n.RBTree{'A;'n} }

doc <:doc<
   @modsubsection{Insert function}
>>




doc <:doc<
   << red_tree{'t}>> checks whether <<'t>> has a red root (empty trees are not red):
>>
define red_tree {| reduce |} :
   red_tree{'t} <--> match_tree{'t; bfalse; self. black_or_red{^color;bfalse;btrue} }

define recolor_root {| reduce |} :
   recolor_root{'t; 'color} <--> match_tree{'t; emptytree; self. tree{^color:='color}}

doc <:doc<
   Make red root, and black sons:
>>
define recolor_rbb {| reduce |} :
   recolor_rbb{'t} <--> recolor_root{match_tree{'t; emptytree; self. tree{(^left:=recolor_root{^left; black})^right:=recolor_root{^right; black}}  }; red}



define lRotate {| reduce |} : lRotate{'t} <--> match_tree{'t; emptytree; root.
                                 match_tree{'root^left; 't; left.
                                               'left^right:=tree{'root^left:='left^right }
                                           }}

define rRotate {| reduce |} : rRotate{'t} <--> match_tree{'t; emptytree; root.
                                 match_tree{'root^right; 't; right.
                                               'right^leftt:=tree{'root^right:='right^left }
                                           }}

define lrRotate {| reduce |} :
   lrRotate{'t} <--> lRotate{ match_tree{'t; emptytree; self. ^left:=rRotate{^left}}}

define rlRotate {| reduce |} :
   rlRotate{'t} <--> rRotate{ match_tree{'t; emptytree; self. ^right:=lRotate{^right}}}

define lbalance {| reduce |} : lbalance{'t} <-->
   if band{  red_tree{leftSubtree{'t}};  red_tree{leftSubtree{leftSubtree{'t}}}  } then recolor_rbb {lRotate{'t}} else
   if band{  red_tree{leftSubtree{'t}};  red_tree{rightSubtree{leftSubtree{'t}}}  } then recolor_rbb {lrRotate {'t}} else
   't

define rbalance {| reduce |} : rbalance{'t} <-->
   if band{  red_tree{rightSubtree{'t}};  red_tree{rightSubtree{rightSubtree{'t}}}  } then recolor_rbb {rRotate{'t}} else
   if band{  red_tree{rightSubtree{'t}};  red_tree{leftSubtree{rightSubtree{'t}}}  } then recolor_rbb {rlRotate {'t}} else
   't

define ins: ins{'a;'t;'ord} <-->
   tree_ind{'t;
     (* if t=emptree *) tree{(('a^left:=emptytree) ^right:=emptytree) ^color:=red};
     (* if t=tree(self) *) L,R,self.
        compare{'ord;. 'a^data; .^data;
          (* if a<data *)  lbalance{^left:='L};
          (* if a=data *)  tree{(('a^left:=^left) ^right:=^right) ^color:=^color};
          (* if a>data *)  rbalance{^right:='R}
               }}

define insert : insert{'a;'t;'ord} <--> recolor_root{ins{'a;'t;'ord}; black}

doc docoff

let resource reduce += [
   soft_reduce <<insert{'a;'t;'ord}>> insert;
   softrec_reduce <<ins{'a;'t;'ord}>> ins;
   soft_reduce <<match_tree{'t;'e; s.'ne['s]}>> match_tree;
   soft_reduce <<leftSubtree{'t}>> leftSubtree;
   soft_reduce <<rightSubtree{'t}>> rightSubtree;
]

doc <:doc<
   @rules
   @modsubsection{Color}
>>

interactive color_wf {| intro[] |} :
   sequent{ <H> >- "type"{Color} }

interactive redtype_wf {| intro[] |} :
   sequent{ <H> >- "type"{Red} }

interactive blacktype_wf {| intro[] |} :
   sequent{ <H> >- "type"{Black} }

interactive black_wf {| intro[] |} :
   sequent{ <H> >- black in Color }

interactive black_wf2 {| intro[] |} :
   sequent{ <H> >- black in Black }

interactive red_wf {| intro[] |} :
   sequent{ <H> >- red in Color }

interactive color_elim {| elim[] |} 'H:
   sequent{ <H>; <J[red]> >- 'C[red] } -->
   sequent{ <H>; <J[black]> >- 'C[black] } -->
   sequent{ <H>; c:Color; <J['c]> >- 'C['c] }

interactive black_elim {| elim[] |} 'H:
   sequent{ <H>; <J[black]> >- 'C[black] } -->
   sequent{ <H>; c:Black; <J['c]> >- 'C['c] }

let resource reduce += [
   soft_reduce <<sons_type{'parent_color}>> sons_type;
   soft_reduce <<cost{'color}>> cost]

interactive black_subtype {| intro[] |}:
   sequent{ <H> >- Black subtype Color }

(* == == *)

doc <:doc<
   @rules
   @modsubsection{Well-formedness}
>>

interactive rbtree_wf {| intro[] |} :
   sequent{ <H> >- "type"{'A} } -->
   sequent{ <H> >- 'color in Color } -->
   sequent{ <H> >- 'n in nat } -->
   sequent{ <H> >- "type"{RBTreeOf{'A} 'n 'color} }

interactive btree1_wf {| intro[] |} :
   sequent{ <H> >- "type"{'A} } -->
   sequent{ <H> >- 'n in nat } -->
   sequent{ <H> >- "type"{BTree{'A;'n}} }

interactive rbtree1_wf {| intro[] |} :
   sequent{ <H> >- "type"{'A} } -->
   sequent{ <H> >- 'n in nat } -->
   sequent{ <H> >- "type"{RBTree{'A;'n}} }

interactive btree2_wf {| intro[] |} :
   sequent{ <H> >- "type"{'A} } -->
   sequent{ <H> >- "type"{BTree{'A}} }

interactive rbtree2_wf {| intro[] |} :
   sequent{ <H> >- "type"{'A} } -->
   sequent{ <H> >- "type"{RBTree{'A}} }

interactive rbtree_subtype {| intro[] |} :
   sequent{ <H> >- "type"{'A} } -->
   sequent{ <H> >- RBTree{'A} subtype BinTree{'A} }

(* == induction == *)

doc <:doc<
   @rules
   @modsubsection{Induction}
>>

define black_depth: black_depth{'t} <--> tree_ind{'t; 0; L,R,self. 'L +@ cost{^color}}



(* == balance == *)
(*
interactive rbtree_wf {| intro[] |} :
   sequent{ <H> >- "type"{'A} } -->
   sequent{ <H> >- 't in RBTree{'A}} -->
   sequent{ <H> >- black_depth{'t} <= 2*@ height{'t}+@ 1 }
*)


doc <:doc<
   @modsection{Defining Set Data Structure using Red-Black Trees}
>>

define rbtree_set {| reduce |} : rbtree_set{'ord} <-->
   {car = bisect{BTree{{data:'ord^car}};. SortedTree{'ord;t.top} isect BinTree{ {color:Color} }};
    empty = emptytree;
    insert = lambda {s. lambda {a. insert{{data='a}; 's; 'ord}}};
    member = lambda {s. lambda {a. is_in_tree{'a; 's; 'ord}}}
   }

doc <:doc<
   @modsubsection{Main Theorem}
>>

interactive rbtree_correctness {| intro[] |} :
   sequent{ <H> >- 'ord in order[i:l] } -->
   sequent{ <H> >- rbtree_set{'ord} in Set[i:l]{'ord^car} }

doc <:doc<
   @rules
   @modsection{Example}
>>

define intset {| reduce |} : intset <--> rbtree_set{int_order}

interactive_rw example :
   ((intset^member) ((intset^insert) ((intset^insert) ((intset^insert) (intset^empty) 2) 3) 1) 3) <--> btrue

doc docoff
