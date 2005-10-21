extends Itt_record
extends Itt_labels

open Basic_tactics

(******************)
(*  Terms         *)
(******************)


(* canonical terms *)

define unfold_obj: obj{self. 'record['self]} <--> lambda {self. 'record['self]}


(* non-canonical terms*)

define unfold_empty_obj {| reduce |}: obj{} <--> obj{self.rcrd}

define unfold_apply: apply[m:t]{'obj} <--> field[m:t]{'obj 'obj}

define unfold_update_field:  update[m:t]{'f;'obj} <--> lambda {self. rcrd[m:t]{'f;'obj 'self}}

define unfold_update_method: update[m:t]{self.'f['self];'obj} <--> lambda {self. rcrd[m:t]{'f['self]; 'obj 'self}}

(******************)
(*  Rewrites      *)
(******************)

interactive_rw apply_reduce {| reduce |}:
   apply[m:t]{obj{self. 'record['self]}} <--> field[m:t]{'record[ obj{self. 'record['self]} ]}

interactive_rw update_f_reduce {| reduce |}:
   update[m:t]{'f;obj{self. 'record['self]}} <--> obj{self.rcrd[m:t]{'f;'record['self]}}

interactive_rw update_m_reduce {| reduce |}:
   update[m:t]{self.'f['self];obj{self. 'record['self]}} <--> obj{self.rcrd[m:t]{'f['self];'record['self]}}



(******************)
(*  Display Forms *)
(******************)

open Itt_rfun

declare obj_dot
dform obj_dot_df : obj_dot = subzero
declare obj_assign
dform obj_assign_df : obj_assign = `":="

dform obj_df  : parens :: except_mode [src] :: "prec"[prec_lambda] ::
      obj{self.'a} = `"obj " slot{'self} `"." slot{'a}

dform obj_empty_df  : parens :: except_mode [src] :: "prec"[prec_lambda] ::
      obj{} = `"obj " rcrd

dform apply_df  : parens :: except_mode [src] ::
      apply[m:t]{'o} = slot{'o} obj_dot label[m:t]

dform update_field_df  : parens :: except_mode [src] ::
      update[m:t]{'f;'o} = slot{'o} obj_dot label[m:t] obj_assign slot{'f}

dform update_method_df  : parens :: except_mode [src] ::
      update[m:t]{s.'f;'o} = slot{'o} obj_dot label[m:t] "(" slot{'s} ")" obj_assign slot{'f}


(******************)
(*  Examples      *)
(******************)

define flea : flea <-->
   obj{ self.
           {x=1;
            getX = apply["x":t]{'self};                            (* x *)
            getNextX =  apply["x":t]{'self} +@ 1;                  (* x+1 *)
            move = update["x":t]{apply["getNextX":t]{'self};'self} (* x:=getNextX *)
           }}

interactive_rw example1 : apply["getX":t]{apply["move":t]{apply["move":t]{flea}}} <--> 3

define fastFlea: fastFlea <--> update["getNextX":t]{self. apply["x":t]{'self} +@ 2; flea}
  (* fastFlea = flea . getX := sigma (x+2) *)

interactive_rw example2 : apply["getX":t]{apply["move":t]{apply["move":t]{fastFlea}}} <--> 5


(******************)
(*  Recursion     *)
(******************)

define recursiveFlea:  recursiveFlea <-->
   update["moveBy":t]{self.
       lambda{n.
         if 'n=@ 0 then 'self
           else apply["moveBy":t]{apply["move":t]{'self}} ('n -@ 1) };
   flea}

interactive_rw example3 : apply["getX":t]{apply["moveBy":t]{recursiveFlea} 5} <--> 6


define feeFoo: feeFoo <-->
   obj{ self.
           {foo =  lambda{n. ifthenelse{ 'n =@ 0 ;
                                         0 ;
                                         .apply["fee":t]{'self} ('n -@ 1)}};
            fee =  lambda{n. ifthenelse{ 'n =@ 0 ;
                                         1 ;
                                         .apply["foo":t]{'self} ('n -@ 1)}}
           }}


interactive_rw example4 : (apply["foo":t]{feeFoo} 5) <--> 1

