extends Kat_terms

open Top_conversionals
open Base_select
open Dtactic

interactive_rw denestwhile_rw :
     ('q in kleene) -->
     ('p in kleene) -->
     ('C in bool) -->
     ('B in bool) -->
     ((star{(('B) * (('p) * ((star{(('C) * (('q)))}) * ((-('C))))))}) * ((-('B)))) <--> ((('B) * (('p) * ((star{((('B) + (('C))) * (((('C) * (('q))) + (((-('C)) * (('p)))))))}) * ((-(('B) + (('C)))))))) + ((-('B))))

interactive enestwhile :
     sequent{ <H> >- 'q in kleene} -->
     sequent{ <H> >- 'p in kleene} -->
     sequent{ <H> >- 'C in bool} -->
     sequent{ <H> >- 'B in bool} -->
     sequent{ <H> >- ((star{(('B) * (('p) * ((star{(('C) * (('q)))}) * ((-('C))))))}) * ((-('B)))) ~ ((('B) * (('p) * ((star{((('B) + (('C))) * (((('C) * (('q))) + (((-('C)) * (('p)))))))}) * ((-(('B) + (('C)))))))) + ((-('B)))) }

interactive_rw msdriver_rw :
     ('u in kleene) -->
     ('n in kleene) -->
     ('m in kleene) -->
     ('kR in kleene) -->
     ('kA in kleene) -->
     ('R in bool) -->
     ('B in bool) -->
     ('A in bool) -->
     ((('B) * (('kR))) ~ (('kR) * (('B)))) -->
     ((('B) * (('u))) ~ (('u) * (('B)))) -->
     ((('A) * (('m))) ~ (('m) * (('A)))) -->
     ((('A) * (('u))) ~ (('u) * (('A)))) -->
     ((('A) * (('n))) ~ (('n) * (('A)))) -->
     (('n) ~ (('n) * (('B)))) -->
     ((('B) * (('m))) ~ (('B) * (('m) * ((-('B)))))) -->
     (('kR) ~ (('kR) * ((-('A))))) -->
     (('kA) ~ (('kA) * (('A)))) -->
     ((-('A)) * (('kA) * (('n) * (((('R) * (('u) * (('kR) * (('m))))) + ((-('R)))) * ((star{((-('B)) * (('kA) * (('n) * (((('R) * (('u) * (('kR) * (('m))))) + ((-('R))))))))}) * (('B) * (('kR)))))))) <--> ((-('A)) * ((-('A)) * (('kA) * (('n) * (((('R) * (('u) * (('A) * (('kR) * (('m)))))) + ((-('R)))) * ((star{((-('B)) * ((-('A)) * (('kA) * (('n) * (((('R) * (('u) * (('A) * (('kR) * (('m)))))) + ((-('R)))))))))}) * (('B) * (('A) * (('kR))))))))))

interactive msdriver :
     sequent{ <H> >- 'u in kleene} -->
     sequent{ <H> >- 'n in kleene} -->
     sequent{ <H> >- 'm in kleene} -->
     sequent{ <H> >- 'kR in kleene} -->
     sequent{ <H> >- 'kA in kleene} -->
     sequent{ <H> >- 'R in bool} -->
     sequent{ <H> >- 'B in bool} -->
     sequent{ <H> >- 'A in bool} -->
     sequent{ <H> >- (('B) * (('kR))) ~ (('kR) * (('B))) } -->
     sequent{ <H> >- (('B) * (('u))) ~ (('u) * (('B))) } -->
     sequent{ <H> >- (('A) * (('m))) ~ (('m) * (('A))) } -->
     sequent{ <H> >- (('A) * (('u))) ~ (('u) * (('A))) } -->
     sequent{ <H> >- (('A) * (('n))) ~ (('n) * (('A))) } -->
     sequent{ <H> >- ('n) ~ (('n) * (('B))) } -->
     sequent{ <H> >- (('B) * (('m))) ~ (('B) * (('m) * ((-('B))))) } -->
     sequent{ <H> >- ('kR) ~ (('kR) * ((-('A)))) } -->
     sequent{ <H> >- ('kA) ~ (('kA) * (('A))) } -->
     sequent{ <H> >- ((-('A)) * (('kA) * (('n) * (((('R) * (('u) * (('kR) * (('m))))) + ((-('R)))) * ((star{((-('B)) * (('kA) * (('n) * (((('R) * (('u) * (('kR) * (('m))))) + ((-('R))))))))}) * (('B) * (('kR)))))))) ~ ((-('A)) * ((-('A)) * (('kA) * (('n) * (((('R) * (('u) * (('A) * (('kR) * (('m)))))) + ((-('R)))) * ((star{((-('B)) * ((-('A)) * (('kA) * (('n) * (((('R) * (('u) * (('A) * (('kR) * (('m)))))) + ((-('R)))))))))}) * (('B) * (('A) * (('kR)))))))))) }

prim_rw ref_eq_l :
     ('x in kleene) -->
     ('x) <--> ('x)

prim_rw ref_eq_r :
     ('x in kleene) -->
     ('x) <--> ('x)

prim ref_eq :
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- ('x) ~ ('x) } = it

prim_rw sym_l 'x :
     ('y in kleene) -->
     ('x in kleene) -->
     (('x) ~ ('y)) -->
     ('y) <--> ('x)

prim_rw sym_r 'y :
     ('y in kleene) -->
     ('x in kleene) -->
     (('x) ~ ('y)) -->
     ('x) <--> ('y)

prim sym :
     sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- ('x) ~ ('y) } -->
     sequent{ <H> >- ('y) ~ ('x) } = it

prim_rw trans_eq_l 'z 'y :
     ('z in kleene) -->
     ('y in kleene) -->
     ('x in kleene) -->
     (('y) ~ ('z)) -->
     (('x) ~ ('y)) -->
     ('x) <--> ('z)

prim_rw trans_eq_r 'x 'y :
     ('z in kleene) -->
     ('y in kleene) -->
     ('x in kleene) -->
     (('y) ~ ('z)) -->
     (('x) ~ ('y)) -->
     ('z) <--> ('x)

prim trans_eq 'y :
     sequent{ <H> >- 'z in kleene} -->
     sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- ('y) ~ ('z) } -->
     sequent{ <H> >- ('x) ~ ('y) } -->
     sequent{ <H> >- ('x) ~ ('z) } = it

prim_rw cong_plusr_l 'y :
     ('z in kleene) -->
     ('y in kleene) -->
     ('x in kleene) -->
     (('x) ~ ('y)) -->
     (('x) + (('z))) <--> (('y) + (('z)))

prim_rw cong_plusr_r 'x :
     ('z in kleene) -->
     ('y in kleene) -->
     ('x in kleene) -->
     (('x) ~ ('y)) -->
     (('y) + (('z))) <--> (('x) + (('z)))

prim cong_plusr :
     sequent{ <H> >- 'z in kleene} -->
     sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- ('x) ~ ('y) } -->
     sequent{ <H> >- (('x) + (('z))) ~ (('y) + (('z))) } = it

prim_rw cong_timesl_l 'z :
     ('x in kleene) -->
     ('z in kleene) -->
     ('y in kleene) -->
     (('y) ~ ('z)) -->
     (('x) * (('y))) <--> (('x) * (('z)))

prim_rw cong_timesl_r 'y :
     ('x in kleene) -->
     ('z in kleene) -->
     ('y in kleene) -->
     (('y) ~ ('z)) -->
     (('x) * (('z))) <--> (('x) * (('y)))

prim cong_timesl :
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- 'z in kleene} -->
     sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >- ('y) ~ ('z) } -->
     sequent{ <H> >- (('x) * (('y))) ~ (('x) * (('z))) } = it

prim_rw cong_timesr_l 'y :
     ('z in kleene) -->
     ('y in kleene) -->
     ('x in kleene) -->
     (('x) ~ ('y)) -->
     (('x) * (('z))) <--> (('y) * (('z)))

prim_rw cong_timesr_r 'x :
     ('z in kleene) -->
     ('y in kleene) -->
     ('x in kleene) -->
     (('x) ~ ('y)) -->
     (('y) * (('z))) <--> (('x) * (('z)))

prim cong_timesr :
     sequent{ <H> >- 'z in kleene} -->
     sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- ('x) ~ ('y) } -->
     sequent{ <H> >- (('x) * (('z))) ~ (('y) * (('z))) } = it

prim_rw cong_star_l 'y :
     ('y in kleene) -->
     ('x in kleene) -->
     (('x) ~ ('y)) -->
     (star{('x)}) <--> (star{('y)})

prim_rw cong_star_r 'x :
     ('y in kleene) -->
     ('x in kleene) -->
     (('x) ~ ('y)) -->
     (star{('y)}) <--> (star{('x)})

prim cong_star :
     sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- ('x) ~ ('y) } -->
     sequent{ <H> >- (star{('x)}) ~ (star{('y)}) } = it

prim _leqintro :
     sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- (('x) + (('y))) ~ ('y) } -->
     sequent{ <H> >- ('x) <= ('y) } = it

prim_rw _leqelim_l :
     ('y in kleene) -->
     ('x in kleene) -->
     (('x) <= ('y)) -->
     (('x) + (('y))) <--> ('y)

prim_rw _leqelim_r 'x :
     ('y in kleene) -->
     ('x in kleene) -->
     (('x) <= ('y)) -->
     ('y) <--> (('x) + (('y)))

prim _leqelim :
     sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- ('x) <= ('y) } -->
     sequent{ <H> >- (('x) + (('y))) ~ ('y) } = it

prim_rw commut_plus_l :
     ('y in kleene) -->
     ('x in kleene) -->
     (('x) + (('y))) <--> (('y) + (('x)))

prim_rw commut_plus_r :
     ('y in kleene) -->
     ('x in kleene) -->
     (('y) + (('x))) <--> (('x) + (('y)))

prim commut_plus :
     sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- (('x) + (('y))) ~ (('y) + (('x))) } = it

prim_rw id_plusr_l :
     ('x in kleene) -->
     (('x) + ((0))) <--> ('x)

prim_rw id_plusr_r :
     ('x in kleene) -->
     ('x) <--> (('x) + ((0)))

prim id_plusr :
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- (('x) + ((0))) ~ ('x) } = it

prim_rw idemp_plus_l :
     ('x in kleene) -->
     (('x) + (('x))) <--> ('x)

prim_rw idemp_plus_r :
     ('x in kleene) -->
     ('x) <--> (('x) + (('x)))

prim idemp_plus :
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- (('x) + (('x))) ~ ('x) } = it

prim_rw id_timesl_l :
     ('x in kleene) -->
     ((1) * (('x))) <--> ('x)

prim_rw id_timesl_r :
     ('x in kleene) -->
     ('x) <--> ((1) * (('x)))

prim id_timesl :
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- ((1) * (('x))) ~ ('x) } = it

prim_rw id_timesr_l :
     ('x in kleene) -->
     (('x) * ((1))) <--> ('x)

prim_rw id_timesr_r :
     ('x in kleene) -->
     ('x) <--> (('x) * ((1)))

prim id_timesr :
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- (('x) * ((1))) ~ ('x) } = it

prim_rw annihl_l :
     ('x in kleene) -->
     ((0) * (('x))) <--> (0)

prim_rw annihl_r 'x :
     ('x in kleene) -->
     (0) <--> ((0) * (('x)))

prim annihl :
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- ((0) * (('x))) ~ (0) } = it

prim_rw annihr_l :
     ('x in kleene) -->
     (('x) * ((0))) <--> (0)

prim_rw annihr_r 'x :
     ('x in kleene) -->
     (0) <--> (('x) * ((0)))

prim annihr :
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- (('x) * ((0))) ~ (0) } = it

prim_rw distrl_l :
     ('z in kleene) -->
     ('y in kleene) -->
     ('x in kleene) -->
     (('x) * ((('y) + (('z))))) <--> ((('x) * (('y))) + ((('x) * (('z)))))

prim_rw distrl_r :
     ('z in kleene) -->
     ('y in kleene) -->
     ('x in kleene) -->
     ((('x) * (('y))) + ((('x) * (('z))))) <--> (('x) * ((('y) + (('z)))))

prim distrl :
     sequent{ <H> >- 'z in kleene} -->
     sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- (('x) * ((('y) + (('z))))) ~ ((('x) * (('y))) + ((('x) * (('z))))) } = it

prim_rw distrr_l :
     ('z in kleene) -->
     ('y in kleene) -->
     ('x in kleene) -->
     ((('x) + (('y))) * (('z))) <--> ((('x) * (('z))) + ((('y) * (('z)))))

prim_rw distrr_r :
     ('z in kleene) -->
     ('y in kleene) -->
     ('x in kleene) -->
     ((('x) * (('z))) + ((('y) * (('z))))) <--> ((('x) + (('y))) * (('z)))

prim distrr :
     sequent{ <H> >- 'z in kleene} -->
     sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- ((('x) + (('y))) * (('z))) ~ ((('x) * (('z))) + ((('y) * (('z))))) } = it

prim_rw unwindl_l :
     ('x in kleene) -->
     ((1) + ((('x) * ((star{('x)}))))) <--> (star{('x)})

prim_rw unwindl_r :
     ('x in kleene) -->
     (star{('x)}) <--> ((1) + ((('x) * ((star{('x)})))))

prim unwindl :
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- ((1) + ((('x) * ((star{('x)}))))) ~ (star{('x)}) } = it

prim_rw unwindr_l :
     ('x in kleene) -->
     ((1) + (((star{('x)}) * (('x))))) <--> (star{('x)})

prim_rw unwindr_r :
     ('x in kleene) -->
     (star{('x)}) <--> ((1) + (((star{('x)}) * (('x)))))

prim unwindr :
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- ((1) + (((star{('x)}) * (('x))))) ~ (star{('x)}) } = it

prim _starl :
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >- 'z in kleene} -->
     sequent{ <H> >- ((('z) * (('y))) + (('x))) <= ('z) } -->
     sequent{ <H> >- (('x) * ((star{('y)}))) <= ('z) } = it

prim _starr :
     sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >- 'z in kleene} -->
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- ((('x) * (('z))) + (('y))) <= ('z) } -->
     sequent{ <H> >- ((star{('x)}) * (('y))) <= ('z) } = it

interactive_rw while_rw :
     ('p in kleene) -->
     ('C in bool) -->
     ('B in bool) -->
     ((('B) * (('C) * (('p)))) ~ (('B) * (('C) * (('p) * (('C)))))) -->
     (('C) * ((star{(('B) * (('p)))}) * ((-('B))))) <--> (('C) * ((star{(('B) * (('p)))}) * ((-('B)) * (('C) * ((-('B)))))))

interactive kat_while :
     sequent{ <H> >- 'p in kleene} -->
     sequent{ <H> >- 'C in bool} -->
     sequent{ <H> >- 'B in bool} -->
     sequent{ <H> >- (('B) * (('C) * (('p)))) ~ (('B) * (('C) * (('p) * (('C))))) } -->
     sequent{ <H> >- (('C) * ((star{(('B) * (('p)))}) * ((-('B))))) ~ (('C) * ((star{(('B) * (('p)))}) * ((-('B)) * (('C) * ((-('B))))))) }

interactive_rw while'_rw :
     ('q in kleene) -->
     ('C in bool) -->
     ((('C) * (('q))) ~ (('C) * (('q) * (('C))))) -->
     (('C) * ((star{('q)}))) <--> (('C) * ((star{('q)}) * (('C))))

interactive while' :
     sequent{ <H> >- 'q in kleene} -->
     sequent{ <H> >- 'C in bool} -->
     sequent{ <H> >- (('C) * (('q))) ~ (('C) * (('q) * (('C)))) } -->
     sequent{ <H> >- (('C) * ((star{('q)}))) ~ (('C) * ((star{('q)}) * (('C)))) }

interactive_rw comp_rw 'E 'D :
     ('q in kleene) -->
     ('p in kleene) -->
     ('E in bool) -->
     ('D in bool) -->
     ('C in bool) -->
     ((('D) * (('q))) ~ (('D) * (('q) * (('E))))) -->
     ((('C) * (('p))) ~ (('C) * (('p) * (('D))))) -->
     (('C) * (('p) * (('q)))) <--> (('C) * (('p) * (('q) * (('E)))))

interactive comp 'D :
     sequent{ <H> >- 'q in kleene} -->
     sequent{ <H> >- 'p in kleene} -->
     sequent{ <H> >- 'E in bool} -->
     sequent{ <H> >- 'D in bool} -->
     sequent{ <H> >- 'C in bool} -->
     sequent{ <H> >- (('D) * (('q))) ~ (('D) * (('q) * (('E)))) } -->
     sequent{ <H> >- (('C) * (('p))) ~ (('C) * (('p) * (('D)))) } -->
     sequent{ <H> >- (('C) * (('p) * (('q)))) ~ (('C) * (('p) * (('q) * (('E))))) }

interactive_rw cond_rw :
     ('q in kleene) -->
     ('p in kleene) -->
     ('D in bool) -->
     ('B in bool) -->
     ('C in bool) -->
     ((('C) * ((-('B)) * (('q) * ((-('D)))))) ~ (0)) -->
     ((('C) * (('B) * (('p) * ((-('D)))))) ~ (0)) -->
     (('C) * (((('B) * (('p))) + (((-('B)) * (('q))))) * ((-('D))))) <--> (0)

interactive cond :
     sequent{ <H> >- 'q in kleene} -->
     sequent{ <H> >- 'p in kleene} -->
     sequent{ <H> >- 'D in bool} -->
     sequent{ <H> >- 'B in bool} -->
     sequent{ <H> >- 'C in bool} -->
     sequent{ <H> >- (('C) * ((-('B)) * (('q) * ((-('D)))))) ~ (0) } -->
     sequent{ <H> >- (('C) * (('B) * (('p) * ((-('D)))))) ~ (0) } -->
     sequent{ <H> >- (('C) * (((('B) * (('p))) + (((-('B)) * (('q))))) * ((-('D))))) ~ (0) }

interactive_rw assg_rw 'C :
     ('p in kleene) -->
     ('C in bool) -->
     ('B in bool) -->
     ((('B) * (('p))) ~ (('p) * (('C)))) -->
     ((-('B)) * (('p))) <--> (('p) * ((-('C))))

interactive assg :
     sequent{ <H> >- 'p in kleene} -->
     sequent{ <H> >- 'C in bool} -->
     sequent{ <H> >- 'B in bool} -->
     sequent{ <H> >- (('B) * (('p))) ~ (('p) * (('C))) } -->
     sequent{ <H> >- ((-('B)) * (('p))) ~ (('p) * ((-('C)))) }

interactive_rw bp2_rw 'B :
     ('p in kleene) -->
     ('B in bool) -->
     (((-('B)) * (('p))) ~ (0)) -->
     ('p) <--> (('B) * (('p)))

interactive bp2 :
     sequent{ <H> >- 'p in kleene} -->
     sequent{ <H> >- 'B in bool} -->
     sequent{ <H> >- ((-('B)) * (('p))) ~ (0) } -->
     sequent{ <H> >- ('p) ~ (('B) * (('p))) }

interactive_rw bp1_rw :
     ('p in kleene) -->
     ('B in bool) -->
     (('p) ~ (('B) * (('p)))) -->
     ((-('B)) * (('p))) <--> (0)

interactive bp1 :
     sequent{ <H> >- 'p in kleene} -->
     sequent{ <H> >- 'B in bool} -->
     sequent{ <H> >- ('p) ~ (('B) * (('p))) } -->
     sequent{ <H> >- ((-('B)) * (('p))) ~ (0) }

interactive_rw bp4_rw 'B :
     ('p in kleene) -->
     ('B in bool) -->
     ((('B) * (('p))) ~ (0)) -->
     ('p) <--> ((-('B)) * (('p)))

interactive bp4 :
     sequent{ <H> >- 'p in kleene} -->
     sequent{ <H> >- 'B in bool} -->
     sequent{ <H> >- (('B) * (('p))) ~ (0) } -->
     sequent{ <H> >- ('p) ~ ((-('B)) * (('p))) }

interactive_rw bp3_rw :
     ('p in kleene) -->
     ('B in bool) -->
     (('p) ~ ((-('B)) * (('p)))) -->
     (('B) * (('p))) <--> (0)

interactive bp3 :
     sequent{ <H> >- 'p in kleene} -->
     sequent{ <H> >- 'B in bool} -->
     sequent{ <H> >- ('p) ~ ((-('B)) * (('p))) } -->
     sequent{ <H> >- (('B) * (('p))) ~ (0) }

interactive_rw pc4_rw 'C :
     ('p in kleene) -->
     ('C in bool) -->
     ((('p) * (('C))) ~ (0)) -->
     ('p) <--> (('p) * ((-('C))))

interactive pc4 :
     sequent{ <H> >- 'p in kleene} -->
     sequent{ <H> >- 'C in bool} -->
     sequent{ <H> >- (('p) * (('C))) ~ (0) } -->
     sequent{ <H> >- ('p) ~ (('p) * ((-('C)))) }

interactive_rw pc3_rw :
     ('p in kleene) -->
     ('C in bool) -->
     (('p) ~ (('p) * ((-('C))))) -->
     (('p) * (('C))) <--> (0)

interactive pc3 :
     sequent{ <H> >- 'p in kleene} -->
     sequent{ <H> >- 'C in bool} -->
     sequent{ <H> >- ('p) ~ (('p) * ((-('C)))) } -->
     sequent{ <H> >- (('p) * (('C))) ~ (0) }

interactive_rw pc2_rw 'C :
     ('p in kleene) -->
     ('C in bool) -->
     ((('p) * ((-('C)))) ~ (0)) -->
     ('p) <--> (('p) * (('C)))

interactive pc2 :
     sequent{ <H> >- 'p in kleene} -->
     sequent{ <H> >- 'C in bool} -->
     sequent{ <H> >- (('p) * ((-('C)))) ~ (0) } -->
     sequent{ <H> >- ('p) ~ (('p) * (('C))) }

interactive_rw pc1_rw :
     ('p in kleene) -->
     ('C in bool) -->
     (('p) ~ (('p) * (('C)))) -->
     (('p) * ((-('C)))) <--> (0)

interactive pc1 :
     sequent{ <H> >- 'p in kleene} -->
     sequent{ <H> >- 'C in bool} -->
     sequent{ <H> >- ('p) ~ (('p) * (('C))) } -->
     sequent{ <H> >- (('p) * ((-('C)))) ~ (0) }

interactive_rw _leq_eq_rw :
     ('x in kleene) -->
     (('x) <= (0)) -->
     ('x) <--> (0)

interactive _leq_eq :
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- ('x) <= (0) } -->
     sequent{ <H> >- ('x) ~ (0) }

interactive_rw sup0_rw :
     ('y in kleene) -->
     ('x in kleene) -->
     (('y) ~ (0)) -->
     (('x) ~ (0)) -->
     (('x) + (('y))) <--> (0)

interactive sup0 :
     sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- ('y) ~ (0) } -->
     sequent{ <H> >- ('x) ~ (0) } -->
     sequent{ <H> >- (('x) + (('y))) ~ (0) }

interactive_rw sup0l_rw 'y :
     ('y in kleene) -->
     ('x in kleene) -->
     ((('x) + (('y))) ~ (0)) -->
     ('x) <--> (0)

interactive sup0l 'y :
     sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- (('x) + (('y))) ~ (0) } -->
     sequent{ <H> >- ('x) ~ (0) }

interactive_rw sup0r_rw 'x :
     ('y in kleene) -->
     ('x in kleene) -->
     ((('x) + (('y))) ~ (0)) -->
     ('y) <--> (0)

interactive sup0r 'x :
     sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- (('x) + (('y))) ~ (0) } -->
     sequent{ <H> >- ('y) ~ (0) }

interactive_rw denest_rw :
     ('y in kleene) -->
     ('x in kleene) -->
     ((star{('x)}) * ((star{(('y) * ((star{('x)})))}))) <--> (star{(('x) + (('y)))})

interactive denest :
     sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- ((star{('x)}) * ((star{(('y) * ((star{('x)})))}))) ~ (star{(('x) + (('y)))}) }

interactive_rw slide_rw :
     ('y in kleene) -->
     ('x in kleene) -->
     (('x) * ((star{(('y) * (('x)))}))) <--> ((star{(('x) * (('y)))}) * (('x)))

interactive slide :
     sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- (('x) * ((star{(('y) * (('x)))}))) ~ ((star{(('x) * (('y)))}) * (('x))) }

interactive mono_star :
     sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- ('x) <= ('y) } -->
     sequent{ <H> >- (star{('x)}) <= (star{('y)}) }

interactive mono_timesr :
     sequent{ <H> >- 'z in kleene} -->
     sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- ('x) <= ('y) } -->
     sequent{ <H> >- (('x) * (('z))) <= (('y) * (('z))) }

interactive mono_timesl :
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- 'z in kleene} -->
     sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >- ('y) <= ('z) } -->
     sequent{ <H> >- (('x) * (('y))) <= (('x) * (('z))) }

interactive mono_plusr :
     sequent{ <H> >- 'z in kleene} -->
     sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- ('x) <= ('y) } -->
     sequent{ <H> >- (('x) + (('z))) <= (('y) + (('z))) }

interactive mono_plusl :
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- 'z in kleene} -->
     sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >- ('y) <= ('z) } -->
     sequent{ <H> >- (('x) + (('y))) <= (('x) + (('z))) }

interactive _eq_leq :
     sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- ('x) ~ ('y) } -->
     sequent{ <H> >- ('x) <= ('y) }

interactive sup :
     sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >- 'z in kleene} -->
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- ('y) <= ('z) } -->
     sequent{ <H> >- ('x) <= ('z) } -->
     sequent{ <H> >- (('x) + (('y))) <= ('z) }

interactive supr:
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >- ('y) <= (('x) + (('y))) }

interactive supl:
     sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- ('x) <= (('x) + (('y))) }

interactive trans_leq 'y :
     sequent{ <H> >- 'z in kleene} -->
     sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- ('y) <= ('z) } -->
     sequent{ <H> >- ('x) <= ('y) } -->
     sequent{ <H> >- ('x) <= ('z) }

interactive_rw antisym_rw 'y :
     ('y in kleene) -->
     ('x in kleene) -->
     (('y) <= ('x)) -->
     (('x) <= ('y)) -->
     ('x) <--> ('y)

interactive antisym :
     sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- ('y) <= ('x) } -->
     sequent{ <H> >- ('x) <= ('y) } -->
     sequent{ <H> >- ('x) ~ ('y) }

interactive ref_leq:
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- ('x) <= ('x) }

interactive_rw cong_plusl_rw 'z :
     ('x in kleene) -->
     ('z in kleene) -->
     ('y in kleene) -->
     (('y) ~ ('z)) -->
     (('x) + (('y))) <--> (('x) + (('z)))

interactive cong_plusl :
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- 'z in kleene} -->
     sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >- ('y) ~ ('z) } -->
     sequent{ <H> >- (('x) + (('y))) ~ (('x) + (('z))) }

interactive_rw id_plusl_rw :
     ('x in kleene) -->
     ((0) + (('x))) <--> ('x)

interactive id_plusl :
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- ((0) + (('x))) ~ ('x) }

interactive_rw abs_times_rw :
     ('C in bool) -->
     ('B in bool) -->
     (('B) * ((('B) + (('C))))) <--> ('B)

interactive abs_times :
     sequent{ <H> >- 'C in bool} -->
     sequent{ <H> >- 'B in bool} -->
     sequent{ <H> >- (('B) * ((('B) + (('C))))) ~ ('B) }

interactive_rw abs_plus_rw :
     ('C in bool) -->
     ('B in bool) -->
     (('B) + ((('B) * (('C))))) <--> ('B)

interactive abs_plus :
     sequent{ <H> >- 'C in bool} -->
     sequent{ <H> >- 'B in bool} -->
     sequent{ <H> >- (('B) + ((('B) * (('C))))) ~ ('B) }

prim_rw distr_timesr_l :
     ('D in bool) -->
     ('C in bool) -->
     ('B in bool) -->
     ((('B) * (('C))) + (('D))) <--> ((('B) + (('D))) * ((('C) + (('D)))))

prim_rw distr_timesr_r :
     ('D in bool) -->
     ('C in bool) -->
     ('B in bool) -->
     ((('B) + (('D))) * ((('C) + (('D))))) <--> ((('B) * (('C))) + (('D)))

prim distr_timesr :
     sequent{ <H> >- 'D in bool} -->
     sequent{ <H> >- 'C in bool} -->
     sequent{ <H> >- 'B in bool} -->
     sequent{ <H> >- ((('B) * (('C))) + (('D))) ~ ((('B) + (('D))) * ((('C) + (('D))))) } = it

prim_rw distr_timesl_l :
     ('D in bool) -->
     ('C in bool) -->
     ('B in bool) -->
     (('B) + ((('C) * (('D))))) <--> ((('B) + (('C))) * ((('B) + (('D)))))

prim_rw distr_timesl_r :
     ('D in bool) -->
     ('C in bool) -->
     ('B in bool) -->
     ((('B) + (('C))) * ((('B) + (('D))))) <--> (('B) + ((('C) * (('D)))))

prim distr_timesl :
     sequent{ <H> >- 'D in bool} -->
     sequent{ <H> >- 'C in bool} -->
     sequent{ <H> >- 'B in bool} -->
     sequent{ <H> >- (('B) + ((('C) * (('D))))) ~ ((('B) + (('C))) * ((('B) + (('D))))) } = it

prim_rw _leq1_l :
     ('B in bool) -->
     (('B) + ((1))) <--> (1)

prim_rw _leq1_r 'B :
     ('B in bool) -->
     (1) <--> (('B) + ((1)))

prim _leq1 :
     sequent{ <H> >- 'B in bool} -->
     sequent{ <H> >- (('B) + ((1))) ~ (1) } = it

prim_rw compl_times_l :
     ('B in bool) -->
     (('B) * ((-('B)))) <--> (0)

prim_rw compl_times_r 'B :
     ('B in bool) -->
     (0) <--> (('B) * ((-('B))))

prim compl_times :
     sequent{ <H> >- 'B in bool} -->
     sequent{ <H> >- (('B) * ((-('B)))) ~ (0) } = it

prim_rw compl_plus_l :
     ('B in bool) -->
     (('B) + ((-('B)))) <--> (1)

prim_rw compl_plus_r 'B :
     ('B in bool) -->
     (1) <--> (('B) + ((-('B))))

prim compl_plus :
     sequent{ <H> >- 'B in bool} -->
     sequent{ <H> >- (('B) + ((-('B)))) ~ (1) } = it

prim_rw _not1_l :
     (-(1)) <--> (0)

prim_rw _not1_r :
     (0) <--> (-(1))

prim _not1 :
     sequent{ <H> >- (-(1)) ~ (0) } = it

prim_rw _not0_l :
     (-(0)) <--> (1)

prim_rw _not0_r :
     (1) <--> (-(0))

prim _not0 :
     sequent{ <H> >- (-(0)) ~ (1) } = it

prim_rw demorgan_times_l :
     ('C in bool) -->
     ('B in bool) -->
     (-(('B) * (('C)))) <--> ((-('B)) + ((-('C))))

prim_rw demorgan_times_r :
     ('C in bool) -->
     ('B in bool) -->
     ((-('B)) + ((-('C)))) <--> (-(('B) * (('C))))

prim demorgan_times :
     sequent{ <H> >- 'C in bool} -->
     sequent{ <H> >- 'B in bool} -->
     sequent{ <H> >- (-(('B) * (('C)))) ~ ((-('B)) + ((-('C)))) } = it

prim_rw demorgan_plus_l :
     ('C in bool) -->
     ('B in bool) -->
     (-(('B) + (('C)))) <--> ((-('B)) * ((-('C))))

prim_rw demorgan_plus_r :
     ('C in bool) -->
     ('B in bool) -->
     ((-('B)) * ((-('C)))) <--> (-(('B) + (('C))))

prim demorgan_plus :
     sequent{ <H> >- 'C in bool} -->
     sequent{ <H> >- 'B in bool} -->
     sequent{ <H> >- (-(('B) + (('C)))) ~ ((-('B)) * ((-('C)))) } = it

prim_rw _not_not_l :
     ('B in bool) -->
     (-(-('B))) <--> ('B)

prim_rw _not_not_r :
     ('B in bool) -->
     ('B) <--> (-(-('B)))

prim _not_not :
     sequent{ <H> >- 'B in bool} -->
     sequent{ <H> >- (-(-('B))) ~ ('B) } = it

prim_rw idemp_times_l :
     ('B in bool) -->
     (('B) * (('B))) <--> ('B)

prim_rw idemp_times_r :
     ('B in bool) -->
     ('B) <--> (('B) * (('B)))

prim idemp_times :
     sequent{ <H> >- 'B in bool} -->
     sequent{ <H> >- (('B) * (('B))) ~ ('B) } = it

prim_rw commut_times_l :
     ('C in bool) -->
     ('B in bool) -->
     (('B) * (('C))) <--> (('C) * (('B)))

prim_rw commut_times_r :
     ('C in bool) -->
     ('B in bool) -->
     (('C) * (('B))) <--> (('B) * (('C)))

prim commut_times :
     sequent{ <H> >- 'C in bool} -->
     sequent{ <H> >- 'B in bool} -->
     sequent{ <H> >- (('B) * (('C))) ~ (('C) * (('B))) } = it

prim mono_not :
     sequent{ <H> >- 'C in bool} -->
     sequent{ <H> >- 'B in bool} -->
     sequent{ <H> >- ('B) <= ('C) } -->
     sequent{ <H> >- (-('C)) <= (-('B)) } = it

prim_rw cong_not_l 'C :
     ('C in bool) -->
     ('B in bool) -->
     (('B) ~ ('C)) -->
     (-('B)) <--> (-('C))

prim_rw cong_not_r 'B :
     ('C in bool) -->
     ('B in bool) -->
     (('B) ~ ('C)) -->
     (-('C)) <--> (-('B))

prim cong_not :
     sequent{ <H> >- 'C in bool} -->
     sequent{ <H> >- 'B in bool} -->
     sequent{ <H> >- ('B) ~ ('C) } -->
     sequent{ <H> >- (-('B)) ~ (-('C)) } = it

interactive _star1r :
     sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- ((('x) * (('y))) + ((1))) <= ('y) } -->
     sequent{ <H> >- (star{('x)}) <= ('y) }

interactive _star1l :
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >- ((('y) * (('x))) + ((1))) <= ('y) } -->
     sequent{ <H> >- (star{('x)}) <= ('y) }

interactive _leq_star :
     sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >- 'z in kleene} -->
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- ('y) <= (star{('z)}) } -->
     sequent{ <H> >- ('x) <= (star{('z)}) } -->
     sequent{ <H> >- (('x) * (('y))) <= (star{('z)}) }

interactive one_x_star:
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- (1) <= (star{('x)}) }

interactive _star_star:
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- (star{(star{('x)})}) <= (star{('x)}) }

interactive xx_star:
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- ('x) <= (star{('x)}) }

interactive x_starx_star:
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- ((star{('x)}) * ((star{('x)}))) <= (star{('x)}) }

interactive app_starr :
     sequent{ <H> >- 'z in kleene} -->
     sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- ('x) <= ('y) } -->
     sequent{ <H> >- ('x) <= (('y) * ((star{('z)}))) }

interactive app_starl :
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- 'z in kleene} -->
     sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >- ('y) <= ('z) } -->
     sequent{ <H> >- ('y) <= ((star{('x)}) * (('z))) }

interactive mono_timeslr :
     sequent{ <H> >- 'w in kleene} -->
     sequent{ <H> >- 'z in kleene} -->
     sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- ('z) <= ('w) } -->
     sequent{ <H> >- ('x) <= ('y) } -->
     sequent{ <H> >- (('x) * (('z))) <= (('y) * (('w))) }

interactive monosupr :
     sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >- 'z in kleene} -->
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- ('x) <= ('z) } -->
     sequent{ <H> >- ('x) <= (('y) + (('z))) }

interactive monosupl :
     sequent{ <H> >- 'z in kleene} -->
     sequent{ <H> >- 'y in kleene} -->
     sequent{ <H> >- 'x in kleene} -->
     sequent{ <H> >- ('x) <= ('y) } -->
     sequent{ <H> >- ('x) <= (('y) + (('z))) }

