extends Kat_std
extends Kat_bool

open Top_conversionals
open Base_select
open Dtactic

interactive hwhile :
     [wf] sequent{ <H> >- 'p in kleene} -->
     [wf] sequent{ <H> >- 'C in bool} -->
     [wf] sequent{ <H> >- 'B in bool} -->
     sequent{ <H> >- ('B * ('C * 'p)) ~ ('B * ('C * ('p * 'C))) } -->
     sequent{ <H> >- ('C * ((star{('B * 'p)}) * (-('B)))) ~ ('C * ((star{('B * 'p)}) * ((-('B)) * ('C * (-('B)))))) }

interactive_rw while_rw :
     ('p in kleene) -->
     ('C in bool) -->
     ('B in bool) -->
     (('B * ('C * 'p)) ~ ('B * ('C * ('p * 'C)))) -->
     ('C * ((star{('B * 'p)}) * (-('B)))) <--> ('C * ((star{('B * 'p)}) * ((-('B)) * ('C * (-('B))))))

interactive while' :
     [wf] sequent{ <H> >- 'q in kleene} -->
     [wf] sequent{ <H> >- 'C in bool} -->
     sequent{ <H> >- ('C * 'q) ~ ('C * ('q * 'C)) } -->
     sequent{ <H> >- ('C * (star{'q})) ~ ('C * ((star{'q}) * 'C)) }

interactive_rw while'_rw :
     ('q in kleene) -->
     ('C in bool) -->
     (('C * 'q) ~ ('C * ('q * 'C))) -->
     ('C * (star{'q})) <--> ('C * ((star{'q}) * 'C))

interactive comp 'D :
     [wf] sequent{ <H> >- 'q in kleene} -->
     [wf] sequent{ <H> >- 'p in kleene} -->
     [wf] sequent{ <H> >- 'E in bool} -->
     [wf] sequent{ <H> >- 'D in bool} -->
     [wf] sequent{ <H> >- 'C in bool} -->
     sequent{ <H> >- ('D * 'q) ~ ('D * ('q * 'E)) } -->
     sequent{ <H> >- ('C * 'p) ~ ('C * ('p * 'D)) } -->
     sequent{ <H> >- ('C * ('p * 'q)) ~ ('C * ('p * ('q * 'E))) }

interactive_rw comp_rw 'E 'D :
     ('q in kleene) -->
     ('p in kleene) -->
     ('E in bool) -->
     ('D in bool) -->
     ('C in bool) -->
     (('D * 'q) ~ ('D * ('q * 'E))) -->
     (('C * 'p) ~ ('C * ('p * 'D))) -->
     ('C * ('p * 'q)) <--> ('C * ('p * ('q * 'E)))

interactive cond :
     [wf] sequent{ <H> >- 'q in kleene} -->
     [wf] sequent{ <H> >- 'p in kleene} -->
     [wf] sequent{ <H> >- 'D in bool} -->
     [wf] sequent{ <H> >- 'B in bool} -->
     [wf] sequent{ <H> >- 'C in bool} -->
     sequent{ <H> >- ('C * ((-('B)) * ('q * (-('D))))) ~ 0 } -->
     sequent{ <H> >- ('C * ('B * ('p * (-('D))))) ~ 0 } -->
     sequent{ <H> >- ('C * ((('B * 'p) + ((-('B)) * 'q)) * (-('D)))) ~ 0 }

interactive_rw cond_rw :
     ('q in kleene) -->
     ('p in kleene) -->
     ('D in bool) -->
     ('B in bool) -->
     ('C in bool) -->
     (('C * ((-('B)) * ('q * (-('D))))) ~ 0) -->
     (('C * ('B * ('p * (-('D))))) ~ 0) -->
     ('C * ((('B * 'p) + ((-('B)) * 'q)) * (-('D)))) <--> 0

interactive assg :
     [wf] sequent{ <H> >- 'p in kleene} -->
     [wf] sequent{ <H> >- 'C in bool} -->
     [wf] sequent{ <H> >- 'B in bool} -->
     sequent{ <H> >- ('B * 'p) ~ ('p * 'C) } -->
     sequent{ <H> >- ((-('B)) * 'p) ~ ('p * (-('C))) }

interactive_rw assg_rw 'C :
     ('p in kleene) -->
     ('C in bool) -->
     ('B in bool) -->
     (('B * 'p) ~ ('p * 'C)) -->
     ((-('B)) * 'p) <--> ('p * (-('C)))

interactive bp2 :
     [wf] sequent{ <H> >- 'p in kleene} -->
     [wf] sequent{ <H> >- 'B in bool} -->
     sequent{ <H> >- ((-('B)) * 'p) ~ 0 } -->
     sequent{ <H> >- 'p ~ ('B * 'p) }

interactive_rw bp2_rw 'B :
     ('p in kleene) -->
     ('B in bool) -->
     (((-('B)) * 'p) ~ 0) -->
     'p <--> ('B * 'p)

interactive bp_one :
     [wf] sequent{ <H> >- 'p in kleene} -->
     [wf] sequent{ <H> >- 'B in bool} -->
     sequent{ <H> >- 'p ~ ('B * 'p) } -->
     sequent{ <H> >- ((-('B)) * 'p) ~ 0 }

interactive_rw bp_one_rw :
     ('p in kleene) -->
     ('B in bool) -->
     ('p ~ ('B * 'p)) -->
     ((-('B)) * 'p) <--> 0

interactive bp4 :
     [wf] sequent{ <H> >- 'p in kleene} -->
     [wf] sequent{ <H> >- 'B in bool} -->
     sequent{ <H> >- ('B * 'p) ~ 0 } -->
     sequent{ <H> >- 'p ~ ((-('B)) * 'p) }

interactive_rw bp4_rw 'B :
     ('p in kleene) -->
     ('B in bool) -->
     (('B * 'p) ~ 0) -->
     'p <--> ((-('B)) * 'p)

interactive bp3 :
     [wf] sequent{ <H> >- 'p in kleene} -->
     [wf] sequent{ <H> >- 'B in bool} -->
     sequent{ <H> >- 'p ~ ((-('B)) * 'p) } -->
     sequent{ <H> >- ('B * 'p) ~ 0 }

interactive_rw bp3_rw :
     ('p in kleene) -->
     ('B in bool) -->
     ('p ~ ((-('B)) * 'p)) -->
     ('B * 'p) <--> 0

interactive pc4 :
     [wf] sequent{ <H> >- 'p in kleene} -->
     [wf] sequent{ <H> >- 'C in bool} -->
     sequent{ <H> >- ('p * 'C) ~ 0 } -->
     sequent{ <H> >- 'p ~ ('p * (-('C))) }

interactive_rw pc4_rw 'C :
     ('p in kleene) -->
     ('C in bool) -->
     (('p * 'C) ~ 0) -->
     'p <--> ('p * (-('C)))

interactive pc3 :
     [wf] sequent{ <H> >- 'p in kleene} -->
     [wf] sequent{ <H> >- 'C in bool} -->
     sequent{ <H> >- 'p ~ ('p * (-('C))) } -->
     sequent{ <H> >- ('p * 'C) ~ 0 }

interactive_rw pc3_rw :
     ('p in kleene) -->
     ('C in bool) -->
     ('p ~ ('p * (-('C)))) -->
     ('p * 'C) <--> 0

interactive pc2 :
     [wf] sequent{ <H> >- 'p in kleene} -->
     [wf] sequent{ <H> >- 'C in bool} -->
     sequent{ <H> >- ('p * (-('C))) ~ 0 } -->
     sequent{ <H> >- 'p ~ ('p * 'C) }

interactive_rw pc2_rw 'C :
     ('p in kleene) -->
     ('C in bool) -->
     (('p * (-('C))) ~ 0) -->
     'p <--> ('p * 'C)

interactive pc_one :
     [wf] sequent{ <H> >- 'p in kleene} -->
     [wf] sequent{ <H> >- 'C in bool} -->
     sequent{ <H> >- 'p ~ ('p * 'C) } -->
     sequent{ <H> >- ('p * (-('C))) ~ 0 }

interactive_rw pc_one_rw :
     ('p in kleene) -->
     ('C in bool) -->
     ('p ~ ('p * 'C)) -->
     ('p * (-('C))) <--> 0

interactive _leq_eq :
     [wf] sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- 'x <= 0 } -->
     sequent{ <H> >- 'x ~ 0 }

interactive_rw _leq_eq_rw :
     ('x in kleene) -->
     ('x <= 0) -->
     'x <--> 0

interactive sup_zero :
     [wf] sequent{ <H> >- 'y in kleene} -->
     [wf] sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- 'y ~ 0 } -->
     sequent{ <H> >- 'x ~ 0 } -->
     sequent{ <H> >- ('x + 'y) ~ 0 }

interactive_rw sup_zero_rw :
     ('y in kleene) -->
     ('x in kleene) -->
     ('y ~ 0) -->
     ('x ~ 0) -->
     ('x + 'y) <--> 0

interactive sup_zerol 'y :
     [wf] sequent{ <H> >- 'y in kleene} -->
     [wf] sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- ('x + 'y) ~ 0 } -->
     sequent{ <H> >- 'x ~ 0 }

interactive_rw sup_zerol_rw 'y :
     ('y in kleene) -->
     ('x in kleene) -->
     (('x + 'y) ~ 0) -->
     'x <--> 0

interactive sup_zeror 'x :
     [wf] sequent{ <H> >- 'y in kleene} -->
     [wf] sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- ('x + 'y) ~ 0 } -->
     sequent{ <H> >- 'y ~ 0 }

interactive_rw sup_zeror_rw 'x :
     ('y in kleene) -->
     ('x in kleene) -->
     (('x + 'y) ~ 0) -->
     'y <--> 0

