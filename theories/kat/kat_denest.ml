extends Kat_std
extends Kat_bool

open Top_conversionals
open Base_select
open Dtactic

interactive denestwhile {| intro[] |}:
     [wf] sequent{ <H> >- 'q in kleene} -->
     [wf] sequent{ <H> >- 'p in kleene} -->
     [wf] sequent{ <H> >- 'C in bool} -->
     [wf] sequent{ <H> >- 'B in bool} -->
     sequent{ <H> >- ((star{('B * ('p * ((star{('C * 'q)}) * (-('C)))))}) * (-('B))) ~ (('B * ('p * ((star{(('B + 'C) * (('C * 'q) + ((-('C)) * 'p)))}) * (-(('B + 'C)))))) + (-('B))) }

interactive_rw denestwhile_rw :
     ('q in kleene) -->
     ('p in kleene) -->
     ('C in bool) -->
     ('B in bool) -->
     ((star{('B * ('p * ((star{('C * 'q)}) * (-('C)))))}) * (-('B))) <--> (('B * ('p * ((star{(('B + 'C) * (('C * 'q) + ((-('C)) * 'p)))}) * (-(('B + 'C)))))) + (-('B)))

