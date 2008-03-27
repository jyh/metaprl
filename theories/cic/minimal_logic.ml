extends Cic_ind_type
extends Cic_ind_elim
open Basic_tactics
open Dtactic

extends Cic_ind_elim_dep
open Cic_ind_elim_dep

interactive implication_wf {| intro [] |} :
   sequent { <H> >- 'A in Prop } -->
   sequent { <H> >- 'B in Prop } -->
   sequent { <H> >- (x:'A -> 'B) in Prop }

interactive distr_impl :
	sequent { A : Prop; B : Prop; C : Prop >-  ('A->('B->'C))->(('A->'B)->('A->'C)) }

interactive syllogism :
   sequent {
      A : Prop; B : Prop; C : Prop
      >- ('A -> 'B) -> (('B -> 'C) -> ('A -> 'C))
   }

extends Cic_prop_connectives
open Cic_prop_connectives

interactive commutative_and :
	sequent { A : Prop; B : Prop >- ( (And 'A 'B) -> (And 'B 'A) ) }
