open Basic_tactics
open S4_logic

extends S4_logic

interactive test0 :
	sequent { box[0]{'a} >- concl{| box[1]{'a} |} }

interactive test1 :
	sequent { box[2]{box[0]{'a}} >- concl{| box[1]{'a} |} }

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

let wmT = byDefsT [unfold_w2; unfold_w0; unfold_kao; unfold_kwh] thenT proverT

interactive box0_m3 :
	sequent { w2 >- concl{| box[0]{m3} |} }

(********************************
 * MUDDY CHILDREN               *
 ********************************)


