extends Kat_terms

open Top_conversionals
open Dtactic


prim_rw prod_assotiative {|reduce |}: (('x * 'y) * 'z) <--> ('x * ('y * 'z))

interactive_rw rev_prod_assotiative: ('x * ('y * 'z)) <--> (('x * 'y) * 'z)

prim_rw prod_1_r {|reduce |}:  ('x * 1) <--> 'x

prim_rw prod_1_l {|reduce |}:  (1 *'x) <--> 'x

prim_rw prod_0_r {|reduce |}:  ('x * 0) <--> 0

prim_rw prod_0_l {|reduce |}:  (0 *'x) <--> 0



prim_rw plus_assotiative {|reduce |}: (('x + 'y) + 'z) <--> ('x + ('y + 'z))

interactive_rw rev_plus_assotiative: ('x + ('y + 'z)) <--> (('x + 'y) + 'z)

prim_rw plus_commutative:  ('x + 'y)  <--> ('y + 'x)

prim_rw plus_0_r {|reduce |}:  ('x + 0) <--> 'x

prim_rw plus_0_l {|reduce |}:  (0 + 'x) <--> 'x


let resource associative +=
   [ <<'a * 'b>>, (prod_assotiative, rev_prod_assotiative);
     <<'a + 'b>>, (plus_assotiative, rev_plus_assotiative)]





prim_rw and_commutative:
      ('x in bool) -->
      ('y in bool)  -->
      ('x * 'y)  <--> ('y * 'x)


let resource commutative +=
   [ <<'a * 'b>>, and_commutative;
     <<'a + 'b>>, plus_commutative]


prim_rw neg_l {|reduce |}:   (-1)  <--> 0
prim_rw neg_0 {|reduce |}:   (-0)  <--> 1


prim_rw double_neg {|reduce |}:
   ('b in bool)  -->  (-(-'b)) <--> 'b



(* Theorems: *)

interactive transitivity 'y:
  sequent{ <H> >- 'x <= 'y } -->
  sequent{ <H> >- 'y <= 'z } -->
  sequent{ <H> >- 'x <= 'z }

interactive asymmetry:
   sequent { <H> >- 'x <= 'y } -->
   sequent { <H> >- 'y <= 'x } -->
   sequent { <H> >- 'x ~ 'y }




define ifthenelse: ifthenelse{'b;'e1;'e2} <--> ('b * 'e1  + (- 'b) * 'e2)

dform ifthenelse_df : parens :: ifthenelse{'e1; 'e2; 'e3} =
   szone pushm[0] pushm[3] `"if" `" " szone{'e1} `" " `"then" hspace
   szone{'e2} popm hspace
   pushm[3] `"else" hspace szone{'e3} popm popm ezone


interactive_rw reduce_ifthenelse_true {| reduce |} : (if 1 then 'e1 else 'e2) <--> 'e1

interactive_rw reduce_ifthenelse_false {| reduce |} : (if 0 then 'e1 else 'e2) <--> 'e2



interactive_rw one_times_one: (1 * 1) <--> 1
