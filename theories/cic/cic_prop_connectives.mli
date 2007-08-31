extends Cic_ind_type
extends Cic_ind_elim
open Basic_tactics

extends Cic_ind_elim_dep

define unfold_and : And <-->
sequent [IndParams] { A : Prop; B : Prop >-
	sequent [IndTypes] { And : Prop >-
		sequent [IndConstrs] {conj: 'A -> 'B -> 'And >- 'And}}}

define unfold_conj : conj <-->
sequent [IndParams] { A : Prop; B : Prop >-
	sequent [IndTypes] { And : Prop >-
		sequent [IndConstrs] {conj: 'A -> 'B -> 'And >- 'conj}}}

topval fold_and : conv
topval fold_conj : conv

prec prec_and
