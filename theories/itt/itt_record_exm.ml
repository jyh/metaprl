(*!
 * @begin[doc]
 * @theory[Itt_record_exm]
 *
 * This theory contains some examples of how to use records.
 * @end[doc]
 *)

extends Itt_record

(*! @docoff *)

extends Itt_int_base
extends Itt_int_ext
extends Itt_atom
extends Itt_set
extends Itt_fun
extends Itt_tsquash
extends Itt_list

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

open Itt_struct
open Itt_record
open Itt_fun
open Itt_rfun
open Itt_list

(*!
 * @begin[doc]
 * First, let us define two record types: $<<plane>>$ and $<<space>>$.
 * @end[doc]
 *)

define unfold_plane:  plane <--> record["x":t]{int;record["y":t]{int}}

define unfold_space:  space <--> record["x":t]{int;record["y":t]{int;record["z":t]{int}}}

interactive planeType {|intro[] |} 'H :
   sequent['ext] {'H >- "type"{plane} }

interactive spaceType {|intro[] |} 'H :
   sequent['ext] {'H >- "type"{space} }


(*!
 * @begin[doc]
 * The elements of these types are records. E.g., the point $<<O>>$ is an element of the type $<<space>>$:
 * @end[doc]
 *)

define unfold_O: O <--> rcrd["x":t]{0; rcrd["y":t]{0; rcrd["z":t]{0}}}

interactive oInSpace {|intro[] |} 'H :
   sequent['ext] {'H >- O IN space }

(*!
 * @begin[doc]
 * $<<O>>$ is also can be considered as an element of the type $<<plane>>$:
 * @end[doc]
 *)

interactive oInPlane {|intro[] |} 'H :
   sequent['ext] {'H >- O IN plane }

(*!
 * @begin[doc]
 * In general $<<space>>$ is a subtype of $<<plane>>$.
 * @end[doc]
 *)

interactive spacePlane {|intro[] |} 'H :
   sequent['ext] {'H >- subtype{space;plane} }

(*!
 * @begin[doc]
 * Let us consider two points $<<A>>$ and $<<B>>$:
 * @end[doc]
 *)


define unfold_A: A <--> rcrd["x":t]{1; rcrd["y":t]{2; rcrd["z":t]{3;rcrd}}}
define unfold_B: B <--> rcrd["z":t]{0; rcrd["y":t]{2; rcrd["x":t]{1}}}

(*! @docoff *)

interactive aInSpace {|intro[] |} 'H :
   sequent['ext] {'H >- A IN space }

interactive bInSpace {|intro[] |} 'H :
   sequent['ext] {'H >- B IN space }


(*!
 * @begin[doc]
 * These points are equal in $<<plane>>$, since they have
 * the same $<<label["x":t]>>$ and $<<label["y":t]>>$ coordinates,
 * But they are not equal in $<<space>>$, since they differ in $<<label["z":t]>>$ coordinate.
 * @end[doc]
 *)

interactive abInPlane {|intro[] |} 'H :
   sequent['ext] {'H >- A = B in plane }

interactive abInSpace {|intro[] |} 'H :
   sequent['ext] {'H >- not{.A = B in space} }

(*!
 * @begin[doc]
 * We can change the order of fields with different labels. E.g.,
 * @end[doc]
 *)

interactive_rw a_rw  :
   A <--> rcrd["y":t]{2; rcrd["z":t]{3; rcrd["x":t]{1}}}

(*!
 * @begin[doc]
 * However if two fields have the same label, then the leftmost field covers others. E.g.,
 * @end[doc]
 *)

interactive_rw cover_rw  :
   rcrd["x":t]{2; rcrd["x":t]{3}} <-->    rcrd["x":t]{2}


(*!
 * @begin[doc]
 * The field operator $<<field[x:t]{'r}>>$ gets the field $<<label[x:t]>>$ of the record $<<'r>>$. E.g.,
 * @end[doc]
 *)

interactive_rw a_z_rw  :
   field["z":t]{A} <--> 3

(*!
 * @begin[doc]
 * Let us define
 * @end[doc]
 *)

define plane_point: point{'a;'b;'e} <--> rcrd["x":t]{'a; rcrd["y":t]{'b;'e }}
define space_point: point{'a;'b; 'c;'e} <--> rcrd["x":t]{'a; rcrd["y":t]{'b; rcrd["z":t]{'c;'e}}}

let unfold_point = plane_point orelseC space_point

let fold_point =
   makeFoldC <<point{'a;'b;'c;'e}>> space_point orelseC
   makeFoldC <<point{'a;'b;'e}>> plane_point

interactive planeIntro {|intro[] |} 'H :
   sequent[squash] {'H >- 'a IN int} -->
   sequent[squash] {'H >- 'b IN int} -->
   sequent['ext] {'H >- point{'a;'b;rcrd} IN plane}

interactive spaceIntro {|intro[] |} 'H :
   sequent[squash] {'H >- 'a IN int} -->
   sequent[squash] {'H >- 'b IN int} -->
   sequent[squash] {'H >- 'c IN int} -->
   sequent['ext] {'H >- point{'a;'b;'c;rcrd} IN space}

(*!
 * @begin[doc]
 * Then we have the following reductions:
 * @end[doc]
 *)


interactive_rw point_beta1_rw : field["x":t]{point{'a;'b;'e}} <--> 'a

interactive_rw point_beta2_rw : field["y":t]{point{'a;'b;'e}} <--> 'b

let resource reduce +=
   [<< field["x":t]{point{'a;'b;'e}}  >>, point_beta1_rw;
    << field["y":t]{point{'a;'b;'e}}  >>, point_beta2_rw]

interactive point_eta 'H :
   sequent[squash]{'H >- 'p IN plane } -->
   sequent['ext]{'H >-   point{field["x":t]{'p};field["y":t]{'p};'p} ~ 'p }


(*!
 * @begin[doc]
 * The last reduction says that any element of $<<plane>>$ is a point of the form $<<point{'a;'b;rcrd}>>$.
 * Therefore we have the following elimination rule:
 * @end[doc]
 *)

interactive planeElim {|elim[] |} 'H 'J:
   sequent['ext]{'H; a:int; b:int; e:record; 'J[point{'a;'b;'e}] >- 'C[point{'a;'b;'e}] } -->
   sequent['ext]  {'H; p:plane; 'J['p] >- 'C['p] }


(*! @docoff *)

interactive spaceElim {|elim[] |} 'H 'J:
   sequent['ext]{'H; a:int; b:int; c:int; e:record; 'J[point{'a;'b;'c;'e}] >- 'C[point{'a;'b;'c;'e}] } -->
   sequent['ext]  {'H; p:space; 'J['p] >- 'C['p] }


(*!
 * @begin[doc]
 * Now we can define length of a point:
 * @end[doc]
 *)


define unfold_length: length{'p} <--> (field["x":t]{'p}*@field["x":t]{'p} +@ field["y":t]{'p}*@field["y":t]{'p})

(*!
 * @begin[doc]
 * That is,
 * @end[doc]
 *)

interactive_rw reduce_length: length{point{'a;'b;'e}} <--> ('a *@ 'a +@ 'b *@ 'b)

let resource reduce += << length{point{'a;'b;'e}}  >>, reduce_length

(*!
 * @begin[doc]
 * For example,
 * @end[doc]
 *)

interactive length_A {|intro[] |} 'H :
   sequent['ext]  {'H >- length{point{3;4;'e}} = 25 in int }

(*!
 * @begin[doc]
 * Now, using the @tt{reduce_length} and @tt{planeElim} rule, we can prove that
 * @end[doc]
 *)

interactive length_wf {|intro[] |} 'H :
   sequent[squash]{'H >- 'p IN plane } -->
   sequent['ext]  {'H >- length{'p} IN int }

(*!
 * @begin[doc]
 * Record can be extended. For example we can define $<<cplane>>$ and $<<cspace>>$ types.
 * @end[doc]
 *)

define unfold_colored_plane:  cplane <--> record["color":t]{atom;plane}
define unfold_colored_space:  cspace <--> record["color":t]{atom;space}

define unfold_redA: redA <--> rcrd["color":t]{token["red":t]; A}

interactive redAInCSpace {|intro[] |} 'H :
   sequent['ext] {'H >- redA IN cspace }


interactive cspaceElim {|elim[] |} 'H 'J:
   sequent['ext]{'H; a:int; b:int; c:int; color:atom; e:record; 'J[rcrd["color":t]{'color;point{'a;'b; 'c; 'e}}] >- 'C[rcrd["color":t]{'color;point{'a;'b; 'c; 'e}}] } -->
   sequent['ext]  {'H; p:cspace; 'J['p] >- 'C['p] }


(*!
 * Dependent Records
 *)

define unfold_semigroup1 : semigroup[G:t,mul:t,i:l] <-->
   record[G:t]{univ[i:l];m.record[mul:t]{.'m -> 'm -> 'm;mul.
   tsquash{.all x:'m.all y:'m.all z:'m. ('mul ('mul 'x 'y) 'z = 'mul 'x ('mul 'y 'z) in 'm)}}}

define unfold_semigroup2 : semigroup[i:l] <--> semigroup["G":t,"*":t,i:l]

let unfold_semigroup = (tryC unfold_semigroup2) thenC unfold_semigroup1

let semigroupDT n = rw unfold_semigroup n thenT dT n

let resource elim +=
   [<<semigroup[i:l]>>,semigroupDT;
    <<semigroup[G:t,mul:t,i:l]>>,semigroupDT
   ]
let resource intro +=
   [<<semigroup[i:l]>>,wrap_intro (semigroupDT 0);
    <<semigroup[G:t,mul:t,i:l]>>, wrap_intro (semigroupDT 0)
   ]


define integers : integers <-->
   rcrd["Z":t]{int;
   rcrd["+":t]{.lambda{x.lambda{y. 'x +@ 'y}};
   rcrd["*":t]{.lambda{x.lambda{y. 'x *@ 'y}}
              }}}

interactive integers_add_semigroup 'H :
   sequent['ext] {'H >- integers IN semigroup["Z":t,"+":t,0:l]}

interactive integers_mul_semigroup 'H :
   sequent['ext] {'H >- integers IN semigroup["Z":t,"*":t,0:l]}


define morphisms : morphisms{'A}  <-->
   rcrd["M":t]{.'A -> 'A;rcrd["*":t]{lambda{f.lambda{g. lambda{x. 'f ('g 'x)}}}}}

interactive morphisms_semigroup 'H :
   sequent[squash] {'H >- 'A IN univ[i:l]} -->
   sequent['ext] {'H >- morphisms{'A} IN semigroup["M":t,"*":t,i:l]}

interactive semigroupAssos4 'H semigroup[i:l] :
   sequent[squash] {'H  >- 'g IN semigroup[i:l]} -->
   sequent['ext] {'H  >-
    all a:field["G":t]{'g}. all b:field["G":t]{'g}. all c:field["G":t]{'g}. all d:field["G":t]{'g}.
      (field["*":t]{'g} (field["*":t]{'g} (field["*":t]{'g} 'a 'b) 'c) 'd =
       field["*":t]{'g} 'a (field["*":t]{'g} 'b (field["*":t]{'g} 'c 'd)) in field["G":t]{'g}
      )}



(*!
 * Data structures
 *)


define unfold_stack :
      Stack[i:l]{'A} <-->                     (* The stack of elements of A *)
         record["car":t]{univ[i:l]; car.
         record["empty":t]{'car;  empty.
         record["push":t]{.'car->'A->'car; push.
         record["pop":t]{.'car->('car * 'A + unit); pop.
         tsquash{.
            (all s: 'car. all a:'A. ('pop('push 's 'a) = inl{('s,'a)} in ('car * 'A + unit)))
            & ('pop('empty) = inr{it} in ('car * 'A + unit))
         }}}}}


define stack_as_list :
         list_stack{'A} <-->
            rcrd["car":t]{list{'A};
            rcrd["empty":t]{nil;
            rcrd["push":t]{lambda{s.lambda{a.cons{'a;'s}}};
            rcrd["pop":t]{lambda{s.list_ind{'s; inr{it}; a,s,f.inl{('s,'a)}}}
         }}}}



interactive stack_as_list_wf 'H :
   sequent[squash] {'H >- 'A IN univ[i:l]} -->
   sequent['ext] {'H >- list_stack{'A} IN Stack[i:l]{'A}}


(*
 * @begin[doc]
 * Using records, one can define a module with mutually recursive functions.
 * E.g. let us define the module with two functions:
 *   foo x = if x>0 then fee (x-1) else 0
 * and
 *   fee x = if x>0 then foo (x-1) else 1
 * @end[doc]
 *)

define unfold_a_module : a_module <-->
   fix{self.
          rcrd["foo":t]{lambda{x.ifthenelse{gt_bool{'x;0};.field["fee":t]{'self} ('x -@ 1);0}};
          rcrd["fee":t]{lambda{x.ifthenelse{gt_bool{'x;0};.field["foo":t]{'self} ('x -@ 1);1}}}}}

let fold_a_module =
   makeFoldC <<a_module>> unfold_a_module;;

let eval_a_module =
   unfold_a_module thenC reduceTopC thenC higherC fold_a_module;;

interactive_rw foo_eval :
   (field["foo":t]{a_module} 'x) <--> ifthenelse{gt_bool{'x;0};.field["fee":t]{a_module} ('x -@ 1);0}

interactive_rw fee_eval :
   (field["fee":t]{a_module} 'x) <--> ifthenelse{gt_bool{'x;0};.field["foo":t]{a_module} ('x -@ 1);1}

let resource reduce +=
   [<< field["foo":t]{a_module} 'x  >>, foo_eval;
    << field["fee":t]{a_module} 'x  >>, fee_eval]


interactive_rw example_of_evaluation :
  (field["foo":t]{a_module} 5) <--> 1

(*! @docoff *)

interactive tst 'H :
   sequent['ext]  { 'H >-  'C} -->
   sequent['ext]  { 'H >-  'C}


dform plane:  plane = mathbbP `"lane"
dform space:  space = mathbbS `"pace"
dform colored_plane:  cplane = mathbbC `"olored" plane
dform colored_space:  cspace = mathbbC `"olored" space

dform o: O = `"O"
dform a: A = `"A"
dform b: B = `"B"
dform redA: redA = `"redA"

dform point2: point{'a;'b;'e} = `"point(" 'a `"," 'b ")"
dform point3: point{'a;'b;'c;'e} = `"point(" 'a `"," 'b `"," 'c ")"

dform length: length{'p} = `"|" 'p `"|" subtwo


dform self_mul_df  : except_mode [src] ::  (self["*":t]{'mul} 'x 'y) = `"(" 'x `"*" 'y `")"

dform mul_df  : except_mode [src] ::  (field["*":t]{'r} 'x 'y) = `"(" 'x `" "  `"*" sub{'r} " " 'y `")"



(*
let unfoldAllT = rwaAll [unfold_plane;unfold_space;unfoldColoredSpace;unfoldCol;unfoldField;unfoldRecordOrt]
*)
