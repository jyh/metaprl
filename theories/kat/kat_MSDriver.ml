extends Kat_std
extends Kat_bool

open Top_conversionals
open Base_select
open Dtactic

interactive msdriver :
     [wf] sequent{ <H> >- 'u in kleene} -->
     [wf] sequent{ <H> >- 'n in kleene} -->
     [wf] sequent{ <H> >- 'm in kleene} -->
     [wf] sequent{ <H> >- 'kR in kleene} -->
     [wf] sequent{ <H> >- 'kA in kleene} -->
     [wf] sequent{ <H> >- 'R in bool} -->
     [wf] sequent{ <H> >- 'B in bool} -->
     [wf] sequent{ <H> >- 'A in bool} -->
     sequent{ <H> >- ('B * 'kR) ~ ('kR * 'B) } -->
     sequent{ <H> >- ('B * 'u) ~ ('u * 'B) } -->
     sequent{ <H> >- ('A * 'm) ~ ('m * 'A) } -->
     sequent{ <H> >- ('A * 'u) ~ ('u * 'A) } -->
     sequent{ <H> >- ('A * 'n) ~ ('n * 'A) } -->
     sequent{ <H> >- 'n ~ ('n * 'B) } -->
     sequent{ <H> >- ('B * 'm) ~ ('B * ('m * (-('B)))) } -->
     sequent{ <H> >- 'kR ~ ('kR * (-('A))) } -->
     sequent{ <H> >- 'kA ~ ('kA * 'A) } -->
     sequent{ <H> >- ((-('A)) * ('kA * ('n * ((('R * ('u * ('kR * 'm))) + (-('R))) * ((star{((-('B)) * ('kA * ('n * (('R * ('u * ('kR * 'm))) + (-('R))))))}) * ('B * 'kR)))))) ~ ((-('A)) * ((-('A)) * ('kA * ('n * ((('R * ('u * ('A * ('kR * 'm)))) + (-('R))) * ((star{((-('B)) * ((-('A)) * ('kA * ('n * (('R * ('u * ('A * ('kR * 'm)))) + (-('R)))))))}) * ('B * ('A * 'kR)))))))) }

interactive_rw msdriver_rw :
     ('u in kleene) -->
     ('n in kleene) -->
     ('m in kleene) -->
     ('kR in kleene) -->
     ('kA in kleene) -->
     ('R in bool) -->
     ('B in bool) -->
     ('A in bool) -->
     (('B * 'kR) ~ ('kR * 'B)) -->
     (('B * 'u) ~ ('u * 'B)) -->
     (('A * 'm) ~ ('m * 'A)) -->
     (('A * 'u) ~ ('u * 'A)) -->
     (('A * 'n) ~ ('n * 'A)) -->
     ('n ~ ('n * 'B)) -->
     (('B * 'm) ~ ('B * ('m * (-('B))))) -->
     ('kR ~ ('kR * (-('A)))) -->
     ('kA ~ ('kA * 'A)) -->
     ((-('A)) * ('kA * ('n * ((('R * ('u * ('kR * 'm))) + (-('R))) * ((star{((-('B)) * ('kA * ('n * (('R * ('u * ('kR * 'm))) + (-('R))))))}) * ('B * 'kR)))))) <--> ((-('A)) * ((-('A)) * ('kA * ('n * ((('R * ('u * ('A * ('kR * 'm)))) + (-('R))) * ((star{((-('B)) * ((-('A)) * ('kA * ('n * (('R * ('u * ('A * ('kR * 'm)))) + (-('R)))))))}) * ('B * ('A * 'kR))))))))

