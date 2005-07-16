open Basic_tactics
open S4_logic

extends S4_logic

interactive test0 :
	sequent { box[0]{'a} >- concl{| box[1]{'a} |} }

interactive test1 :
	sequent { box[2]{box[0]{'a}} >- concl{| box[1]{'a} |} }

interactive test2 :
	sequent { >- concl {| box[1]{box[2]{'a}} => box[1]{box[2]{box[2]{'a}}} |} }

interactive test3 :
   sequent { >- concl {| box[1]{box[2]{'a}} => box[1]{'a} |} }

interactive test4 :
	sequent { box[1]{not{box[2]{'a}}} >- concl {| box[1]{not{box[2]{'a & 'b}}} |} }

(********************************
 * WISE MEN                     *
 ********************************)

declare m1
declare m2
declare m3

define unfold_kwh : kwh[i:n]{'a} <--> box[i:n]{'a} or box[i:n]{not{'a}}

define unfold_kao : KAO <-->
	kwh[1]{m2} & kwh[1]{m3} &
	kwh[2]{m1} & kwh[2]{m3}

define unfold_w0 : w0 <--> box[0]{KAO} & box[0]{not{not{m1} & not{m2} & not{m3}}}
define unfold_w2 : w2 <--> w0 and box[0]{not{kwh[1]{m1}}} and box[0]{not{kwh[2]{m2}}}

let unfold_wmT = byDefsT [unfold_w2; unfold_w0; unfold_kao; unfold_kwh]
let wmT = unfold_wmT thenT simple_proverT

interactive lemma0 :
	sequent { box[0]{kwh[1]{m2}}; m2 >- concl{| box[1]{m2} |} }

interactive lemma1 :
   sequent { box[0]{kwh[1]{m2}}; m2 >- concl{| box[0]{m2} |} }

interactive lemma2 :
   sequent { box[1]{kwh[1]{m2}}; m2 >- concl{| box[1]{m2} |} }

interactive box0_m3 :
	sequent { w2 >- concl{| box[0]{m3} |} }

(********************************
 * MUDDY CHILDREN               *
 ********************************)

declare c1
declare c2
declare c3
declare c4

define unfold_mchKAO : mchKAO <-->
	kwh[1]{c2} & kwh[1]{c3} & kwh[1]{c4} &
   kwh[2]{c1} & kwh[2]{c3} & kwh[2]{c4} &
   kwh[3]{c1} & kwh[3]{c2} & kwh[3]{c4} &
   kwh[4]{c1} & kwh[4]{c2} & kwh[4]{c3}

define unfold_s0 : s0 <--> c1 & c2 & not{c3} & not{c4} & mchKAO
define unfold_s1 : s1 <--> s0 & box[0]{c1 or c2 or c3 or c4}
define unfold_s2 : s2 <-->
	s1 &
	box[0]{
		(c1 & c2) or
      (c1 & c3) or
      (c1 & c4) or
      (c2 & c3) or
      (c2 & c4) or
      (c3 & c4)
	}

define unfold_s3 : s3 <-->
	s2 &
	box[0]{
		kwh[1]{c1} &
		kwh[2]{c2}
	}


let unfold_mchT =
	byDefsT [unfold_s3; unfold_s2; unfold_s1; unfold_s0; unfold_mchKAO; unfold_kao; unfold_kwh]

interactive lemma3 :
	sequent { s2 >- concl {| kwh[1]{c1} & kwh[2]{c2} |} }

interactive wrong :
	sequent { s2 >- concl {| kwh[1]{c1} & kwh[2]{c2} & kwh[3]{c3} & kwh[4]{c4} |} }

interactive lemma4 :
   sequent { s3 >- concl {| kwh[3]{c3} |} }

interactive muddy_children :
   sequent { s3 >- concl {| kwh[1]{c1} & kwh[2]{c2} & kwh[3]{c3} & kwh[4]{c4} |} }

