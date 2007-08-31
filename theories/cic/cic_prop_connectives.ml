extends Cic_ind_type
extends Cic_ind_elim
open Basic_tactics
open Dtactic

extends Cic_ind_elim_dep
open Cic_ind_elim_dep

(*********************************************************
*			Propositional Calculus Connectives					*
**********************************************************)

(* Definition of AND in Coq:
	 Inductive and (A B:Prop) : Prop := conj (_:A) (_:B). *)

define unfold_and : And <-->
sequent [IndParams] { A : Prop; B : Prop >-
	sequent [IndTypes] { And : Prop >-
		sequent [IndConstrs] {conj: 'A -> 'B -> 'And >- 'And}}}

define unfold_conj : conj <-->
sequent [IndParams] { A : Prop; B : Prop >-
	sequent [IndTypes] { And : Prop >-
		sequent [IndConstrs] {conj: 'A -> 'B -> 'And >- 'conj}}}

let fold_and = makeFoldC <<And>> unfold_and
let fold_conj = makeFoldC <<conj>> unfold_conj

prec prec_and

dform and_df :
(And 't 'u) = slot{'t} hspace wedge `" " slot{'u}

interactive andDef_wf {| intro [] |} :
	sequent { <H> >-
		sequent [IndParamsWF] { A : Prop; B : Prop >-
			sequent [IndTypesWF] { And : Prop >-
				sequent [IndConstrsWF] {conj: 'A -> 'B -> 'And >- it } }	} }

interactive and_wf {| intro [] |} :
	sequent { <H> >- And in Prop -> Prop -> Prop }

interactive conj_wf {| intro [] |} :
	sequent { <H> >- conj in (A : Prop -> B : Prop -> ('A -> 'B -> (And 'A 'B))) }

interactive and_intro_lemma :
	sequent { <H>; A: Prop; B: Prop; a: 'A; b: 'B >- And 'A 'B }

interactive and_intro {| intro [] |} :
	[wf] sequent { <H> >- 'A in Prop } -->
	[wf] sequent { <H> >- 'B in Prop } -->
	sequent { <H> >- 'A } -->
	sequent { <H> >- 'B } -->
	sequent { <H> >- And 'A 'B }

interactive and_elimL {| elim [] |} 'H :
	sequent { <H> >- 'A in Prop } -->
	sequent { <H> >- 'B in Prop } -->
	sequent { <H> ; x: (And 'A 'B) ; <J['x]> >- 'A }

interactive and_elimR {| elim [] |} 'H :
	sequent { <H> >- 'A in Prop } -->
	sequent { <H> >- 'B in Prop } -->
	sequent { <H> ; x: (And 'A 'B) ; <J['x]> >- 'B }
