doc <:doc<
   @module[Itt_record_exm]

   This theory contains some examples of how to use records.
>>

extends Itt_record

doc docoff

extends Itt_int_base
extends Itt_int_ext
extends Itt_atom
extends Itt_set
extends Itt_dfun
extends Itt_tsquash
extends Itt_list
extends Itt_labels

open Basic_tactics
open Itt_rfun

doc <:doc<
   @modsection{Simple Records}
   First, let us define two record types: <<plane>> and <<space>>.
>>

define unfold_plane:  plane <--> {x:int; y:int}

define unfold_space:  space <--> {x:int; y:int; z:int}

interactive planeType {|intro[] |} :
   sequent{ <H> >- "type"{plane} }

interactive spaceType {|intro[] |} :
   sequent{ <H> >- "type"{space} }

doc <:doc<
   The elements of these types are records. E.g., the point <<O>> is an element of the type <<space>>:
>>

define unfold_O: O <-->  {x=0; y=0; z=0}

interactive oInSpace {|intro[] |} :
   sequent{ <H> >- O in space }

doc <:doc<
   <<O>> also can be considered as an element of the type <<plane>>:
>>

interactive oInPlane {|intro[] |} :
   sequent{ <H> >- O in plane }

doc <:doc<
   In general <<space>> is a subtype of <<plane>>.
>>

interactive spacePlane {|intro[] |} :
   sequent{ <H> >- space  subtype plane }

doc <:doc<
   Let us consider two points <<A>> and <<B>>:
>>

define unfold_A: A <--> {x=1; y=2; z=3}
define unfold_B: B <--> {z=0; y=2; x=1}

doc docoff

interactive aInSpace {|intro[] |} :
   sequent{ <H> >- A in space }

interactive bInSpace {|intro[] |} :
   sequent{ <H> >- B in space }

doc <:doc<
   These points are equal in <<plane>>, since they have
   the same <<label["x":t]>> and <<label["y":t]>> coordinates,
   But they are not equal in <<space>>, since they differ in <<label["z":t]>> coordinate.
>>

interactive abInPlane {|intro[] |} :
   sequent{ <H> >- A = B in plane }

interactive abInSpace {|intro[] |} :
   sequent{ <H> >- not{A = B in space} }

doc <:doc<
   We can change the order of fields with different labels. E.g.,
>>

interactive_rw a_rw  :
   A <--> {y=2; z=3; x=1}

doc <:doc<
   However if two fields have the same label, then the rightmost field covers others. E.g.,
>>

interactive_rw cover_rw  :
   {x=3; x=2} <-->    {x=2}

doc <:doc<
   The field operator <<field[x:t]{'r}>> gets the field <<label[x:t]>> of the record <<'r>>. E.g.,
>>

interactive_rw a_z_rw  :
   (A^y) <--> 2

doc <:doc<
   Let us define
>>

define plane_point: point{'a;'b;'e} <--> rcrd["x":t]{'a; rcrd["y":t]{'b;'e }}
define space_point: point{'a;'b; 'c;'e} <--> rcrd["x":t]{'a; rcrd["y":t]{'b; rcrd["z":t]{'c;'e}}}

doc docoff

let unfold_point = plane_point orelseC space_point

let fold_point =
   makeFoldC <<point{'a;'b;'c;'e}>> space_point orelseC
   makeFoldC <<point{'a;'b;'e}>> plane_point

doc docon

interactive planeIntro {|intro[] |} :
   sequent{ <H> >- 'a in int} -->
   sequent{ <H> >- 'b in int} -->
   sequent{ <H> >- point{'a;'b;rcrd} in plane}

interactive spaceIntro {|intro[] |} :
   sequent{ <H> >- 'a in int} -->
   sequent{ <H> >- 'b in int} -->
   sequent{ <H> >- 'c in int} -->
   sequent{ <H> >- point{'a;'b;'c;rcrd} in space}

doc <:doc<
   Then we have the following reductions:
>>

interactive_rw point_beta1_rw {| reduce |} : (point{'a;'b;'e}^x) <--> 'a

interactive_rw point_beta2_rw {| reduce |} : (point{'a;'b;'e}^y) <--> 'b

interactive point_eta :
   sequent{ <H> >- 'p in plane } -->
   sequent{ <H> >-   point{'p^x;.'p^y;'p} ~ 'p }

doc <:doc<
   The last reduction says that any element of <<plane>> is a point of the form <<point{'a;'b;rcrd}>>.
   Therefore we have the following elimination rule:
>>

interactive planeElim {|elim[] |} 'H :
   sequent{ <H>; a:int; b:int; e:record; <J[point{'a;'b;'e}]> >- 'C[point{'a;'b;'e}] } -->
   sequent{ <H>; p:plane; <J['p]> >- 'C['p] }

doc docoff

interactive spaceElim {|elim[] |} 'H :
   sequent{ <H>; a:int; b:int; c:int; e:record; <J[point{'a;'b;'c;'e}]> >- 'C[point{'a;'b;'c;'e}] } -->
   sequent{ <H>; p:space; <J['p]> >- 'C['p] }

doc <:doc<
   Now we can define length of a point:
>>

define unfold_length: length{'p} <--> ('p^x *@ 'p^x  +@  'p^y *@  'p^y)

doc <:doc<
   That is,
>>

interactive_rw reduce_length {| reduce |} : length{point{'a;'b;'e}} <--> ('a *@ 'a +@ 'b *@ 'b)

doc <:doc<
   For example,
>>

interactive length_A {|intro[] |} :
   sequent{ <H> >- length{point{3;4;'e}} = 25 in int }

doc <:doc<
   Now, using the @tt[reduce_length] and @hrefrule[planeElim] rule, we can prove that
>>

interactive length_wf {|intro[] |} :
   sequent{ <H> >- 'p in plane } -->
   sequent{ <H> >- length{'p} in int }

doc <:doc<
   Record can be extended. For example we can define <<cplane>> and <<cspace>> types.
>>

define unfold_colored_plane:  cplane <--> record["color":t]{atom;plane}
define unfold_colored_space:  cspace <--> record["color":t]{atom;space}

define unfold_redA: redA <--> rcrd["color":t]{token["red":t]; A}

interactive redAInCSpace {|intro[] |} :
   sequent{ <H> >- redA in cspace }

interactive cspaceElim {|elim[] |} 'H :
   sequent{ <H>; a:int; b:int; c:int; color:atom; e:record; <J[rcrd["color":t]{'color;point{'a;'b; 'c; 'e}}]> >- 'C[rcrd["color":t]{'color;point{'a;'b; 'c; 'e}}] } -->
   sequent{ <H>; p:cspace; <J['p]> >- 'C['p] }

doc <:doc<
   @modsection{Dependent Records}
   @modsubsection{Algebraic structures}

>>

define unfold_semigroup1 : semigroup[G:t,mul:t,i:l] <-->
   record[G:t]{univ[i:l];m.record[mul:t]{'m -> 'm -> 'm;mul.
   tsquash{all x:'m.all y:'m.all z:'m. ('mul ('mul 'x 'y) 'z = 'mul 'x ('mul 'y 'z) in 'm)}}}

(*
define unfold_semigroup2 : semigroup[i:l] <--> semigroup["G":t,"*":t,i:l]
*)

define  unfold_mul_semigroup : semigroup[i:l] <-->
   {car : univ[i:l];
    "*" : ^car -> ^car -> ^car;
    all x: ^car. all y:^car .all z:^car. ('x ^* 'y) ^* 'z =  'x ^* ('y ^* 'z) in ^car
   }

doc docoff

(* let unfold_semigroup = (tryC unfold_semigroup2) thenC unfold_semigroup1 *)

let unfold_semigroup = unfold_mul_semigroup orelseC unfold_semigroup1

let semigroupDT n = rw unfold_semigroup n thenT dT n

let resource elim +=
   [ <<semigroup[i:l]>>,semigroupDT;
     <<semigroup[G:t,mul:t,i:l]>>,semigroupDT
   ]
let resource intro +=
   [<<semigroup[i:l]>>,wrap_intro (semigroupDT 0);
    <<semigroup[G:t,mul:t,i:l]>>, wrap_intro (semigroupDT 0)
   ]

doc docon

define integers : integers <-->
   {car = int;
    "+" = lambda{x.lambda{y. 'x +@ 'y}};
    "*" = lambda{x.lambda{y. 'x *@ 'y}}
   }

interactive integers_add_semigroup :
   sequent{ <H> >- integers in semigroup["car":t,"+":t,0:l]}

interactive integers_mul_semigroup :
   sequent{ <H> >- integers in semigroup["car":t,"*":t,0:l]}

define morphisms : morphisms{'A}  <-->
   {car = 'A -> 'A;
    "*" = lambda{f.lambda{g. lambda{x. 'f ('g 'x)}}}
   }

interactive morphisms_semigroup :
   sequent{ <H> >- 'A in univ[i:l]} -->
   sequent{ <H> >- morphisms{'A} in semigroup["car":t,"*":t,i:l]}

interactive semigroupAssos4 semigroup[i:l] :
   sequent{ <H>  >-
    forany semigroup[i:l].
     all a:^car. all b:^car. all c:^car. all d:^car.
      (('a ^* 'b) ^* 'c) ^* 'd = 'a ^* ('b ^* ('c ^* 'd)) in ^car
      }

doc <:doc<
   @modsubsection{Data structures}
>>

define unfold_stack :
      Stack[i:l]{'A} <-->                     (* The stack of elements of A *)
        {car : univ[i:l];
         empty : ^car;
         push :  ^car -> 'A -> ^car;
         pop:  ^car-> ^car * 'A + unit;
         all s: ^car. all a:'A. (^pop(^push 's 'a) = inl{('s,'a)} in (^car * 'A + unit));
         ^pop(^empty) = inr{it} in (^car * 'A + unit)
        }

define stack_as_list :
         list_stack{'A} <-->
          { car = list{'A};
            empty = nil;
            push = lambda{s.lambda{a.cons{'a;'s}}};
            pop = lambda{s.list_ind{'s; inr{it}; a,s,f.inl{('s,'a)}}}
         }

interactive stack_as_list_wf {| intro [] |}:
   sequent{ <H> >- 'A in univ[i:l]} -->
   sequent{ <H> >- list_stack{'A} in Stack[i:l]{'A}}

doc <:doc<
   @modsection{Mutually recursive functions}
   Using records, one can define a module with mutually recursive functions.
   E.g. let us define the module with two functions:
     @code{foo x = if x>0 then fee (x-1) else 0}
   and
     @code{fee x = if x>0 then foo (x-1) else 1}
>>

define unfold_a_module : a_module <-->
   fix{self.
          {foo = lambda{x.ifthenelse{gt_bool{'x;0};. ^fee ('x -@ 1);0}};
           fee = lambda{x.ifthenelse{gt_bool{'x;0};. ^foo ('x -@ 1);1}}
          }}

doc docoff

let fold_a_module =
   makeFoldC <<a_module>> unfold_a_module;;

let eval_a_module =
   unfold_a_module thenC reduce_fix thenC higherC fold_a_module;;

doc docon

interactive_rw foo_eval {| reduce |} :
   (a_module^foo 'x) <--> ifthenelse{gt_bool{'x;0};.a_module^fee ('x -@ 1);0}

interactive_rw fee_eval {| reduce |} :
   (a_module^fee 'x) <--> ifthenelse{gt_bool{'x;0};.a_module^foo ('x -@ 1);1}

interactive_rw example_of_evaluation :
  (a_module^foo 5) <--> 1

doc docoff

interactive tst :
   sequent{ <H> >-  'C} -->
   sequent{ <H> >-  'C}

dform plane:  plane = mathbbP `"lane"
dform space:  space = mathbbS `"pace"
dform colored_plane:  cplane = mathbbC `"olored" plane
dform colored_space:  cspace = mathbbC `"olored" space

dform point2: point{'a;'b;'e} = `"point(" 'a `"," 'b ")"
dform point3: point{'a;'b;'c;'e} = `"point(" 'a `"," 'b `"," 'c ")"

dform length: length{'p} = `"|" 'p `"|" subtwo

dform self_mul_df  : except_mode [src] ::  (self["*":t]{'mul} 'x 'y) = `"(" 'x `"*" 'y `")"

dform mul_df  : except_mode [src] ::  (field["*":t]{'r} 'x 'y) = `"(" 'x `" "  `"*" sub{'r} " " 'y `")"

(*
let unfoldAllT = rwaAll [unfold_plane;unfold_space;unfoldColoredSpace;unfoldCol;unfoldField;unfoldRecordOrt]
*)
