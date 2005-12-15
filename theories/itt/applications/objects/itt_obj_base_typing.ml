define iform unfold_union: union{'T} <--> Union X :'T.'X
define iform unfold_isect: isect{'T} <--> Isect X :'T.'X



define record{'a;'b; i.'x['i]; 'A['i]} <-->

define iform unfold_monotone: monotone[l:l]{X.'M['X]} <-->
   all X:univ[l:l].  all Y:univ[l:l]. ('X subtype 'Y => 'M['X] subtype 'M['Y])




define unfold_Obj: Obj[l:l]{X.'N['X]} <--> union{ {X:univ[l:l] | 'X subtype 'N['X] } }


interactive apply_object_wf_lemma {| intro[] |} :
   sequent{ <H> >- monotone[l:l]{'X.'M['X]} } -->
   sequent{ <H> >- 'o in  Obj[l:l]{X.'X -> 'M['X]} } -->
   sequent{ <H> >- 'o 'o in  'M[ Obj[l:l]{X.'X -> 'M['X]} ] }


interactive apply_object_wf {| intro[AutoMustComplete; intro_typeinf<<'o>> ] |} <<Obj[l:l]{X.'X -> 'M['X]}>> :
   sequent{ <H> >- monotone[l:l]{'X.'M['X]} } -->
   sequent{ <H> >- 'o in  Obj[l:l]{X.'X -> 'M['X]} } -->
   sequent{ <H> >- 'M[Obj[l:l]{X.'X -> 'M['X]}] subtype record[m:t]{'A} } -->
   sequent{ <H> >- apply[m:t]{'o} in 'A }



interactive apply_object_wf {| intro[AutoMustComplete; intro_typeinf<<'o>> ] |}
   declare EObj{ Self.'M['Self]; 'P['Self] }



(*********************************************)

define unfold_Z Z{'X;'A} <--> 'X subtype ('X -> 'A)

interactive Z_elim 'X:
   sequent { <H> >- Z{'X;'A} } -->
   sequent { <H> >- 'o in 'X } -->
   sequent { <H> >- 'o 'o in 'A }

interactive Z_elim_cor 'X:
   sequent { <H> >- Z{'X;'} } -->
   sequent { <H>; r:'R >- 'r in M } -->
   sequent { <H> >- apply[m:t]{'o} in 'M }

R = {xi
o o in M


define unfold_Obj:  Obj{ Self.'M['Self] } <--> Isect 'Self:univ[i:l]


declare EObj{ Self.'M['Self] }
declare EObj{ Self.'M['Self]; 'P['Self] }





