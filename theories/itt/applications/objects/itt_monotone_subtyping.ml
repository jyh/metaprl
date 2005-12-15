extends Itt_subtype
extends Itt_logic
open Basic_tactics


define monotone: monotone[l:l]{X.'M['X]} <-->
   (all X:univ[l:l]. 'M['X] in univ[l:l]) &
   (all X:univ[l:l]. all Y:univ[l:l]. ('X subtype 'Y => 'M['X] subtype 'M['Y]))


interactive monotone_elim {| elim[] |} 'H ('A subtype 'B):
      [wf] sequent { <H>; u: monotone[l:l]{X.'M['X]}; <J['u]> >- 'A in univ[l:l]  } -->
      [wf] sequent { <H>; u: monotone[l:l]{X.'M['X]}; <J['u]> >- 'B in univ[l:l]  } -->
      sequent { <H>; u: monotone[l:l]{X.'M['X]}; <J['u]> >- 'A subtype 'B  } -->
      sequent { <H>; u: monotone[l:l]{X.'M['X]}; <J['u]> >- 'M['A] subtype 'M['B]  }

interactive use_monotone monotone[l:l]{X.'M['X]} ('A subtype 'B):
      [wf] sequent { <H> >- 'A in univ[l:l]  } -->
      [wf] sequent { <H> >- 'B in univ[l:l]  } -->
      sequent { <H> >- 'A subtype 'B  } -->
      sequent { <H> >-  monotone[l:l]{X.'M['X]} } -->
      sequent { <H> >- 'M['A] subtype 'M['B]  }

interactive use_monotone2 monotone[l:l]{X.'M['X]} 'A :
      [wf] sequent { <H> >-  'A in univ[l:l] } -->
      sequent { <H> >-  monotone[l:l]{X.'M['X]} } -->
      sequent { <H> >- 'M['A] in univ[l:l] }

interactive use_monotone3 monotone[l:l]{X.'M['X]} 'A :
      [wf] sequent { <H> >-  'A in univ[l:l] } -->
      sequent { <H> >-  monotone[l:l]{X.'M['X]} } -->
      sequent { <H> >- "type"{'M['A]} }



