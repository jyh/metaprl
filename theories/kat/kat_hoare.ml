extends Kat_std
extends Kat_bool

open Top_conversionals
open Base_select
open Dtactic

define hoare: hoare{'A;'e;'B} <--> ('A * 'e * 'B ~ 'A * 'e)

dform hoare_df : parens :: hoare{'A;'e;'B} = szone `"{" szone{'A}
`"}" szone{'e} `"{" szone{'B} `"}"

define ifthenelse: ifthenelse{'b;'e1;'e2} <--> ('b * 'e1  + (- 'b) * 'e2)

dform ifthenelse_df : parens :: ifthenelse{'e1; 'e2; 'e3} =
   szone pushm[0] pushm[3] `"if" `" " szone{'e1} `" " `"then" hspace
   szone{'e2} popm hspace
   pushm[3] `"else" hspace szone{'e3} popm popm ezone

define hwhile: hwhile{'b;'e1} <--> (star{('b * 'e1)} * (-('b)))

interactive hifrule:
     [wf] sequent{ <H> >- 'B in bool} -->
     [wf] sequent{ <H> >- 'A in bool} -->
     [wf] sequent{ <H> >- 'C in bool} -->
     [wf] sequent{ <H> >- 'x in kleene} -->
     [wf] sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >-  hoare{'A * 'B;'x;'C}} -->
     sequent{ <H> >-  hoare{-('B) * 'A;'y;'C}} -->
     sequent{ <H> >-  hoare{'A;ifthenelse{'B;'x;'y};'C}}

interactive hwhilerule:
     [wf] sequent{ <H> >- 'A in bool} -->
     [wf] sequent{ <H> >- 'B in bool} -->
     [wf] sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >-  hoare{'A * 'B;'x;'A}} -->
     sequent{ <H> >-  hoare{'A;hwhile{'B;'x};-('B) * 'A}}

interactive hseqrule 'C:
     [wf] sequent{ <H> >- 'B in bool} -->
     [wf] sequent{ <H> >- 'A in bool} -->
     [wf] sequent{ <H> >- 'C in bool} -->
     [wf] sequent{ <H> >- 'x in kleene} -->
     [wf] sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >-  hoare{'A;'x;'C}} -->
     sequent{ <H> >-  hoare{'C;'y;'B}} -->
     sequent{ <H> >-  hoare{'A;'x * 'y;'B}}