extends Kat_terms

open Top_conversionals
open Base_select
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


(* Less and greater *)

define le : le{'x;'y} <--> ('x + 'y) ~ 'y

define ge : ge{'x;'y} <--> le{'y;'x}

dform le_df : ('x <= 'y) = 'x " " le " " 'y
dform ge_df : ('x >= 'y) = 'x " " ge " " 'y



prim neg_wf {| intro[] |}:
   sequent { <H> >- 'b in bool} -->
   sequent { <H> >- - 'b in bool} = it

prim and_wf {| intro[] |}:
   sequent { <H> >- 'b in bool} -->
   sequent { <H> >- 'c in bool} -->
   sequent { <H> >- 'b * 'c in bool} = it

prim or_wf {| intro[] |}:
   sequent { <H> >- 'b in bool} -->
   sequent { <H> >- 'c in bool} -->
   sequent { <H> >- 'b + 'c in bool} = it


prim_rw ref_eq_l : ('x in kleene) -->
('x) <--> ('x)

prim_rw ref_eq_r : ('x in kleene) -->
('x) <--> ('x)

prim ref_eq :      sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- ('x) ~ ('x) } = it

prim_rw sym_l 'x :
('y in kleene) -->
('x in kleene) -->
(('x) ~ ('y)) -->
('y) <--> ('x)

prim_rw sym_r 'y :
('y in kleene) -->
('x in kleene) -->
(('x) ~ ('y)) -->
('x) <--> ('y)

prim sym :
     sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- ('x) ~ ('y) } -->
     sequent{ <H> >- ('y) ~ ('x) } = it

prim_rw trans_eq_l 'z 'y :
('z in kleene) -->
('y in kleene) -->
('x in kleene) -->
(('y) ~ ('z)) -->
(('x) ~ ('y)) -->
('x) <--> ('z)

prim_rw trans_eq_r 'x 'y :
('z in kleene) -->
('y in kleene) -->
('x in kleene) -->
(('y) ~ ('z)) -->
(('x) ~ ('y)) -->
('z) <--> ('x)

prim trans_eq 'y:
     sequent{ <H> >- 'z in kleene} -->
     sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- ('y) ~ ('z) } -->
     sequent{ <H> >- ('x) ~ ('y) } -->
     sequent{ <H> >- ('x) ~ ('z) } = it

prim_rw cong_plusR_l 'y :
('z in kleene) -->
('y in kleene) -->
('x in kleene) -->
(('x) ~ ('y)) -->
(('x) + (('z))) <--> (('y) + (('z)))

prim_rw cong_plusR_r 'x :
('z in kleene) -->
('y in kleene) -->
('x in kleene) -->
(('x) ~ ('y)) -->
(('y) + (('z))) <--> (('x) + (('z)))

prim cong_plusR :
     sequent{ <H> >- 'z in kleene} -->
     sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- ('x) ~ ('y) } -->
     sequent{ <H> >- (('x) + (('z))) ~ (('y) + (('z))) } = it

prim_rw cong_timesL_l 'z :
('x in kleene) -->
('z in kleene) -->
('y in kleene) -->
(('y) ~ ('z)) -->
(('x) * (('y))) <--> (('x) * (('z)))

prim_rw cong_timesL_r 'y :
('x in kleene) -->
('z in kleene) -->
('y in kleene) -->
(('y) ~ ('z)) -->
(('x) * (('z))) <--> (('x) * (('y)))

prim cong_timesL :
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- 'z in kleene} -->
     sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >- ('y) ~ ('z) } -->
     sequent{ <H> >- (('x) * (('y))) ~ (('x) * (('z))) } = it

prim_rw cong_timesR_l 'y :
('z in kleene) -->
('y in kleene) -->
('x in kleene) -->
(('x) ~ ('y)) -->
(('x) * (('z))) <--> (('y) * (('z)))

prim_rw cong_timesR_r 'x :
('z in kleene) -->
('y in kleene) -->
('x in kleene) -->
(('x) ~ ('y)) -->
(('y) * (('z))) <--> (('x) * (('z)))

prim cong_timesR :
     sequent{ <H> >- 'z in kleene} -->
     sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- ('x) ~ ('y) } -->
     sequent{ <H> >- (('x) * (('z))) ~ (('y) * (('z))) } = it

prim_rw cong_star_l 'y :
('y in kleene) -->
('x in kleene) -->
(('x) ~ ('y)) -->
(star{('x)}) <--> (star{('y)})

prim_rw cong_star_r 'x :
('y in kleene) -->
('x in kleene) -->
(('x) ~ ('y)) -->
(star{('y)}) <--> (star{('x)})

prim cong_star :
     sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- ('x) ~ ('y) } -->
     sequent{ <H> >- (star{('x)}) ~ (star{('y)}) } = it

prim _leqintro :
     sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- (('x) + (('y))) ~ ('y) } -->
     sequent{ <H> >- ('x) <= ('y) } = it

prim_rw _leqelim_l :
('y in kleene) -->
('x in kleene) -->
(('x) <= ('y)) -->
(('x) + (('y))) <--> ('y)

prim_rw _leqelim_r 'x :
('y in kleene) -->
('x in kleene) -->
(('x) <= ('y)) -->
('y) <--> (('x) + (('y)))

prim _leqelim :
     sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- ('x) <= ('y) } -->
     sequent{ <H> >- (('x) + (('y))) ~ ('y) } = it

prim_rw commut_plus_l : ('y in kleene) -->
('x in kleene) -->
(('x) + (('y))) <--> (('y) + (('x)))

prim_rw commut_plus_r : ('y in kleene) -->
('x in kleene) -->
(('y) + (('x))) <--> (('x) + (('y)))

prim commut_plus :      sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- (('x) + (('y))) ~ (('y) + (('x))) } = it

prim_rw id_plusR_l : ('x in kleene) -->
(('x) + ((0))) <--> ('x)

prim_rw id_plusR_r : ('x in kleene) -->
('x) <--> (('x) + ((0)))

prim id_plusR :      sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- (('x) + ((0))) ~ ('x) } = it

prim_rw idemp_plus_l : ('x in kleene) -->
(('x) + (('x))) <--> ('x)

prim_rw idemp_plus_r : ('x in kleene) -->
('x) <--> (('x) + (('x)))

prim idemp_plus :      sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- (('x) + (('x))) ~ ('x) } = it

prim_rw id_timesL_l : ('x in kleene) -->
((1) * (('x))) <--> ('x)

prim_rw id_timesL_r : ('x in kleene) -->
('x) <--> ((1) * (('x)))

prim id_timesL :      sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- ((1) * (('x))) ~ ('x) } = it

prim_rw id_timesR_l : ('x in kleene) -->
(('x) * ((1))) <--> ('x)

prim_rw id_timesR_r : ('x in kleene) -->
('x) <--> (('x) * ((1)))

prim id_timesR :      sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- (('x) * ((1))) ~ ('x) } = it

prim_rw annihL_l : ('x in kleene) -->
((0) * (('x))) <--> (0)

prim_rw annihL_r 'x : ('x in kleene) -->
(0) <--> ((0) * (('x)))

prim annihL :      sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- ((0) * (('x))) ~ (0) } = it

prim_rw annihR_l : ('x in kleene) -->
(('x) * ((0))) <--> (0)

prim_rw annihR_r 'x : ('x in kleene) -->
(0) <--> (('x) * ((0)))

prim annihR :      sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- (('x) * ((0))) ~ (0) } = it

prim_rw distrL_l : ('z in kleene) -->
('y in kleene) -->
('x in kleene) -->
(('x) * ((('y) + (('z))))) <--> ((('x) * (('y))) + ((('x) * (('z)))))

prim_rw distrL_r : ('z in kleene) -->
('y in kleene) -->
('x in kleene) -->
((('x) * (('y))) + ((('x) * (('z))))) <--> (('x) * ((('y) + (('z)))))

prim distrL :      sequent{ <H> >- 'z in kleene} -->
     sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- (('x) * ((('y) + (('z))))) ~ ((('x) * (('y))) + ((('x) * (('z))))) } = it

prim_rw distrR_l : ('z in kleene) -->
('y in kleene) -->
('x in kleene) -->
((('x) + (('y))) * (('z))) <--> ((('x) * (('z))) + ((('y) * (('z)))))

prim_rw distrR_r : ('z in kleene) -->
('y in kleene) -->
('x in kleene) -->
((('x) * (('z))) + ((('y) * (('z))))) <--> ((('x) + (('y))) * (('z)))

prim distrR :      sequent{ <H> >- 'z in kleene} -->
     sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- ((('x) + (('y))) * (('z))) ~ ((('x) * (('z))) + ((('y) * (('z))))) } = it

prim_rw unwindL_l : ('x in kleene) -->
((1) + ((('x) * ((star{('x)}))))) <--> (star{('x)})

prim_rw unwindL_r : ('x in kleene) -->
(star{('x)}) <--> ((1) + ((('x) * ((star{('x)})))))

prim unwindL :      sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- ((1) + ((('x) * ((star{('x)}))))) ~ (star{('x)}) } = it

prim_rw unwindR_l : ('x in kleene) -->
((1) + (((star{('x)}) * (('x))))) <--> (star{('x)})

prim_rw unwindR_r : ('x in kleene) -->
(star{('x)}) <--> ((1) + (((star{('x)}) * (('x)))))

prim unwindR :      sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- ((1) + (((star{('x)}) * (('x))))) ~ (star{('x)}) } = it

prim _starL :
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >- 'z in kleene} -->
     sequent{ <H> >- ((('z) * (('y))) + (('x))) <= ('z) } -->
     sequent{ <H> >- (('x) * ((star{('y)}))) <= ('z) } = it

prim _starR :
     sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >- 'z in kleene} -->
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- ((('x) * (('z))) + (('y))) <= ('z) } -->
     sequent{ <H> >- ((star{('x)}) * (('y))) <= ('z) } = it

