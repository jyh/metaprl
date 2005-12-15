doc <:doc<
   @module[Itt_closed_subtyping]
      A subset <<'U>> of <<univ[l:l]>> is closed (w.r.t intersection) iff intersection of
      any family of types from <<'U>> is also in <<'U>>.

   @parents
>>
extends Itt_subset
extends Itt_isect
extends Itt_bisect

open Basic_tactics


define is_closed: is_closed[l:l]{'U} <-->
   all I:univ[l:l]. all X:'I->'U. Isect i:'I.('X 'i) in 'U subset univ[l:l]


interactive is_closed_wf {| intro [] |}  :
   sequent { <H> >- 'U subtype univ[l:l] } -->
   sequent { <H> >- "type"{is_closed[l:l]{'U}} }


define closed: closed[l:l] <--> {U:univ[l':l] | 'U subset univ[l:l] & is_closed[l:l]{'U} }

interactive closed_wf {| intro [] |}  :
   sequent { <H> >- "type"{closed[l:l]} }


interactive closed_elim0a {| elim [] |} 'H :
   sequent { <H>; U:closed[l:l]; <J['U]> >- 'U in univ[l':l] }

interactive closed_elim0b {| elim [] |} 'H :
   sequent { <H>; U:closed[l:l]; <J['U]> >- 'U subtype univ[l:l] }

interactive closed_elim1a {| elim [] |} 'H:
   sequent { <H>; U:closed[l:l]; <J['U]> >- 'I in univ[l:l] } -->
   sequent { <H>; U:closed[l:l]; <J['U]>; i:'I >- 'X['i] in 'U } -->
   sequent { <H>; U:closed[l:l]; <J['U]> >-  Isect i:'I.'X['i] in 'U }

interactive closed_elim1b {| elim [] |} 'H:
   sequent { <H>; U:closed[l:l]; <J['U]> >- 'A in 'U } -->
   sequent { <H>; U:closed[l:l]; <J['U]> >- 'B in 'U } -->
   sequent { <H>; U:closed[l:l]; <J['U]> >- 'A isect 'B in 'U }

interactive closed_elim1c {| elim [] |} 'H :
   sequent { <H>; U:closed[l:l]; <J['U]> >- top in 'U }






define semicont: semicont[l:l]{x.'f['x]; 'A} <-->
   all I:univ[l:l]. all X:'I->'A. Isect i:'I.'f['X 'i] subtype 'f[Isect i:'I.('X 'i)]

