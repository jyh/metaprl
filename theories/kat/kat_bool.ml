extends Kat_terms

open Top_conversionals
open Base_select
open Dtactic

interactive abs_times {| intro[] |}:
     [wf] sequent{ <H> >- 'C in bool} -->
     [wf] sequent{ <H> >- 'B in bool} -->
     sequent{ <H> >- ('B * ('B + 'C)) ~ 'B }

interactive_rw abs_timesl_rw  {|reduce|}:
     ('C in bool) -->
     ('B in bool) -->
     ('B * ('B + 'C)) <--> 'B

interactive_rw abs_timesr_rw 'C :
     ('C in bool) -->
     ('B in bool) -->
     'B <--> ('B * ('B + 'C))

interactive abs_plus {| intro[] |}:
     [wf] sequent{ <H> >- 'C in bool} -->
     [wf] sequent{ <H> >- 'B in bool} -->
     sequent{ <H> >- ('B + ('B * 'C)) ~ 'B }

interactive_rw abs_plusl_rw  {|reduce|}:
     ('C in bool) -->
     ('B in bool) -->
     ('B + ('B * 'C)) <--> 'B

interactive_rw abs_plusr_rw 'C :
     ('C in bool) -->
     ('B in bool) -->
     'B <--> ('B + ('B * 'C))

prim distr_timesr {| intro[] |}:
     [wf] sequent{ <H> >- 'D in bool} -->
     [wf] sequent{ <H> >- 'C in bool} -->
     [wf] sequent{ <H> >- 'B in bool} -->
     sequent{ <H> >- (('B * 'C) + 'D) ~ (('B + 'D) * ('C + 'D)) } = it

interactive_rw distr_timesr_l :
     ('D in bool) -->
     ('C in bool) -->
     ('B in bool) -->
     (('B * 'C) + 'D) <--> (('B + 'D) * ('C + 'D))

interactive_rw distr_timesr_r :
     ('D in bool) -->
     ('C in bool) -->
     ('B in bool) -->
     (('B + 'D) * ('C + 'D)) <--> (('B * 'C) + 'D)

prim distr_timesl {| intro[] |}:
     [wf] sequent{ <H> >- 'D in bool} -->
     [wf] sequent{ <H> >- 'C in bool} -->
     [wf] sequent{ <H> >- 'B in bool} -->
     sequent{ <H> >- ('B + ('C * 'D)) ~ (('B + 'C) * ('B + 'D)) } = it

interactive_rw distr_timesl_l :
     ('D in bool) -->
     ('C in bool) -->
     ('B in bool) -->
     ('B + ('C * 'D)) <--> (('B + 'C) * ('B + 'D))

interactive_rw distr_timesl_r :
     ('D in bool) -->
     ('C in bool) -->
     ('B in bool) -->
     (('B + 'C) * ('B + 'D)) <--> ('B + ('C * 'D))

prim _leq_one {| intro[] |}:
     [wf] sequent{ <H> >- 'B in bool} -->
     sequent{ <H> >- ('B + 1) ~ 1 } = it

interactive_rw _leq_one_l  {|reduce|}:
     ('B in bool) -->
     ('B + 1) <--> 1

interactive_rw _leq_one_r 'B :
     ('B in bool) -->
     1 <--> ('B + 1)

prim compl_times {| intro[] |}:
     [wf] sequent{ <H> >- 'B in bool} -->
     sequent{ <H> >- ('B * (-('B))) ~ 0 } = it

interactive_rw compl_times_l  {|reduce|}:
     ('B in bool) -->
     ('B * (-('B))) <--> 0

interactive_rw compl_times_r 'B :
     ('B in bool) -->
     0 <--> ('B * (-('B)))

prim compl_plus {| intro[] |}:
     [wf] sequent{ <H> >- 'B in bool} -->
     sequent{ <H> >- ('B + (-('B))) ~ 1 } = it

interactive_rw compl_plus_l  {|reduce|}:
     ('B in bool) -->
     ('B + (-('B))) <--> 1

interactive_rw compl_plus_r 'B :
     ('B in bool) -->
     1 <--> ('B + (-('B)))

prim _not_one {| intro[] |}:
     sequent{ <H> >- (-(1)) ~ 0 } = it

interactive_rw _not_one_l  {|reduce|}:
     (-(1)) <--> 0

interactive_rw _not_one_r :
     0 <--> (-(1))

prim _not_zero {| intro[] |}:
     sequent{ <H> >- (-(0)) ~ 1 } = it

interactive_rw _not_zero_l  {|reduce|}:
     (-(0)) <--> 1

interactive_rw _not_zero_r :
     1 <--> (-(0))

prim demorgan_times {| intro[] |}:
     [wf] sequent{ <H> >- 'C in bool} -->
     [wf] sequent{ <H> >- 'B in bool} -->
     sequent{ <H> >- (-(('B * 'C))) ~ ((-('B)) + (-('C))) } = it

interactive_rw demorgan_times_l :
     ('C in bool) -->
     ('B in bool) -->
     (-(('B * 'C))) <--> ((-('B)) + (-('C)))

interactive_rw demorgan_times_r :
     ('C in bool) -->
     ('B in bool) -->
     ((-('B)) + (-('C))) <--> (-(('B * 'C)))

prim demorgan_plus {| intro[] |}:
     [wf] sequent{ <H> >- 'C in bool} -->
     [wf] sequent{ <H> >- 'B in bool} -->
     sequent{ <H> >- (-(('B + 'C))) ~ ((-('B)) * (-('C))) } = it

interactive_rw demorgan_plus_l :
     ('C in bool) -->
     ('B in bool) -->
     (-(('B + 'C))) <--> ((-('B)) * (-('C)))

interactive_rw demorgan_plus_r :
     ('C in bool) -->
     ('B in bool) -->
     ((-('B)) * (-('C))) <--> (-(('B + 'C)))

prim _not_not {| intro[] |}:
     [wf] sequent{ <H> >- 'B in bool} -->
     sequent{ <H> >- (-((-('B)))) ~ 'B } = it

interactive_rw _not_not_l  {|reduce|}:
     ('B in bool) -->
     (-((-('B)))) <--> 'B

interactive_rw _not_not_r :
     ('B in bool) -->
     'B <--> (-((-('B))))

prim idemp_times {| intro[] |}:
     [wf] sequent{ <H> >- 'B in bool} -->
     sequent{ <H> >- ('B * 'B) ~ 'B } = it

interactive_rw idemp_times_l  {|reduce|}:
     ('B in bool) -->
     ('B * 'B) <--> 'B

interactive_rw idemp_times_r :
     ('B in bool) -->
     'B <--> ('B * 'B)

prim commut_times {| intro[] |}:
     [wf] sequent{ <H> >- 'C in bool} -->
     [wf] sequent{ <H> >- 'B in bool} -->
     sequent{ <H> >- ('B * 'C) ~ ('C * 'B) } = it

interactive_rw commut_times_l :
     ('C in bool) -->
     ('B in bool) -->
     ('B * 'C) <--> ('C * 'B)

interactive_rw commut_times_r :
     ('C in bool) -->
     ('B in bool) -->
     ('C * 'B) <--> ('B * 'C)

prim mono_not :
     [wf] sequent{ <H> >- 'C in bool} -->
     [wf] sequent{ <H> >- 'B in bool} -->
     sequent{ <H> >- 'B <= 'C } -->
     sequent{ <H> >- (-('C)) <= (-('B)) } = it

prim cong_not :
     [wf] sequent{ <H> >- 'C in bool} -->
     [wf] sequent{ <H> >- 'B in bool} -->
     sequent{ <H> >- 'B ~ 'C } -->
     sequent{ <H> >- (-('B)) ~ (-('C)) } = it

interactive_rw cong_not_l 'C :
     ('C in bool) -->
     ('B in bool) -->
     ('B ~ 'C) -->
     (-('B)) <--> (-('C))

interactive_rw cong_not_r 'B :
     ('C in bool) -->
     ('B in bool) -->
     ('B ~ 'C) -->
     (-('C)) <--> (-('B))

