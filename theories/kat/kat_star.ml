extends Kat_std
extends Kat_bool

open Top_conversionals
open Base_select
open Dtactic

interactive _star_oner :
     [wf] sequent{ <H> >- 'y in kleene} -->
     [wf] sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- (('x * 'y) + 1) <= 'y } -->
     sequent{ <H> >- (star{'x}) <= 'y }

interactive _star_onel :
     [wf] sequent{ <H> >- 'x in kleene} -->
     [wf] sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >- (('y * 'x) + 1) <= 'y } -->
     sequent{ <H> >- (star{'x}) <= 'y }

interactive _leq_star :
     [wf] sequent{ <H> >- 'y in kleene} -->
     [wf] sequent{ <H> >- 'z in kleene} -->
     [wf] sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- 'y <= (star{'z}) } -->
     sequent{ <H> >- 'x <= (star{'z}) } -->
     sequent{ <H> >- ('x * 'y) <= (star{'z}) }

interactive _onex_star {| intro[] |}:
     [wf] sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- 1 <= (star{'x}) }

interactive _star_star {| intro[] |}:
     [wf] sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- (star{(star{'x})}) <= (star{'x}) }

interactive xx_star {| intro[] |}:
     [wf] sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- 'x <= (star{'x}) }

interactive x_starx_star {| intro[] |}:
     [wf] sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- ((star{'x}) * (star{'x})) <= (star{'x}) }

interactive app_starr :
     [wf] sequent{ <H> >- 'z in kleene} -->
     [wf] sequent{ <H> >- 'y in kleene} -->
     [wf] sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- 'x <= 'y } -->
     sequent{ <H> >- 'x <= ('y * (star{'z})) }

interactive app_starl :
     [wf] sequent{ <H> >- 'x in kleene} -->
     [wf] sequent{ <H> >- 'z in kleene} -->
     [wf] sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >- 'y <= 'z } -->
     sequent{ <H> >- 'y <= ((star{'x}) * 'z) }

