doc <:doc<
	@module{This module contains tests for S4nJ}

	<<box[0]{'a}>> plays the role of J and all other boxes are normal S4-modalities
>>

open Basic_tactics
open S4_logic

doc <:doc< @parents >>
extends S4_logic

doc <:doc< @modsection{Standalone tests} >>

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

interactive test5 :
	sequent { box[0]{'a} >- concl {| box[1]{box[2]{'a}} |} }

interactive test6 :
	sequent { box[1]{box[2]{'a}} >- concl {| box[1]{box[1]{box[2]{'a}}} |} }

interactive test7 :
	sequent { box[1]{box[2]{'a}} >- concl {| box[2]{box[2]{'a}} |} }

doc <:doc< @modsection{Wise Men} >>

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

doc <:doc< This one is not provable >>
interactive lemma1 :
   sequent { box[0]{kwh[1]{m2}}; m2 >- concl{| box[0]{m2} |} }

interactive lemma2 :
   sequent { box[1]{kwh[1]{m2}}; m2 >- concl{| box[1]{m2} |} }

interactive box0_m3 :
	sequent { w2 >- concl{| box[0]{m3} |} }

doc <:doc<
 @modsection{Muddy Children}
>>

declare c1
declare c2
declare c3
declare c4

doc <:doc< @modsubsection{2 children} >>

define unfold_mch2_KAO : mch2_KAO <-->	box[0]{kwh[1]{c2} & kwh[2]{c1}}

define unfold_s2_0 : s2_0 <--> c1 & not{c2} & mch2_KAO

define unfold_s2_1 : s2_1 <--> box[0]{not{kwh[1]{c1}} & not{kwh[2]{c2}}}

define unfold_s2_2 : s2_2 <--> box[0]{c1 or c2}

define unfold_s2_3 : s2_3 <--> box[0]{box[1]{c1}}

let unfold_mch2T = byDefsT
	[unfold_s2_3; unfold_s2_2; unfold_s2_1; unfold_s2_0; unfold_mch2_KAO; unfold_kwh]

interactive mch2_lemma0 :
	sequent {
		box[1]{box[2]{c1 or c2}};
		box[1]{box[2]{c1} or box[2]{not{c1}}};
		box[1]{not{box[2]{c2}}}
		>- concl{| box[1]{c1} |} }

interactive mch2_lemma1 :
   sequent {
      box[1]{box[2]{c1 or c2}};
      box[1]{kwh[2]{c1}};
      box[1]{not{box[2]{c2}}}
      >- concl{| box[1]{c1} |} }

interactive mch2_lemma2 :
   sequent {
      box[0]{c1 or c2};             (* s2_2 *)
      box[0]{kwh[2]{c1}};           (* KAO  *)
      box[0]{not{box[2]{c2}}}       (* s2_1 *)
      >- concl{| box[1]{c1} |} }

interactive mch2_2 :
   sequent { s2_0; s2_2 >- concl{| box[1]{c1} |} }

interactive mch2_3 :
   sequent { mch2_KAO; s2_1; s2_2 >- concl{| box[2]{not{c2}} |} }

interactive mch2 :
	sequent { mch2_KAO; s2_1; s2_2 >- concl{| kwh[1]{c1} & kwh[2]{c2} |} }

doc <:doc< @modsubsection{3 children} >>

define unfold_mch3_KAO : mch3_KAO <-->
	box[0]{
		kwh[1]{c2} & kwh[1]{c3} &
		kwh[2]{c1} & kwh[2]{c3}
	}

define unfold_s3_0 : s3_0 <--> c1 & not{c2} & not{c3} & mch3_KAO

define unfold_s3_1 : s3_1 <--> box[0]{not{kwh[1]{c1}} & not{kwh[2]{c2}} & not{kwh[3]{c3}}}

define unfold_s3_2 : s3_2 <--> box[0]{c1 or c2 or c3}

define unfold_s3_3 : s3_3 <--> box[0]{box[1]{c1}}

let unfold_mch3T = byDefsT
   [unfold_s3_3; unfold_s3_2; unfold_s3_1; unfold_s3_0; unfold_mch3_KAO; unfold_kwh]

interactive mch3_2 :
   sequent { s3_0; s3_2 >- concl{| box[1]{c1} |} }

interactive mch3_3 :
   sequent { s3_0; s3_1; s3_2 >- concl{| box[2]{not{c2}} |} }

interactive mch3 :
   sequent { s3_0; s3_1; s3_2 >- concl{| kwh[1]{c1} & kwh[2]{c2} & kwh[3]{c3} |} }

doc <:doc< @modsubsection{4 children} >>

define unfold_mch4_KAO : mch4_KAO <-->
	box[0]{
		kwh[1]{c2} & kwh[1]{c3} & kwh[1]{c4} &
   	kwh[2]{c1} & kwh[2]{c3} & kwh[2]{c4} &
	   kwh[3]{c1} & kwh[3]{c2} & kwh[3]{c4} &
   	kwh[4]{c1} & kwh[4]{c2} & kwh[4]{c3}
	}

define unfold_NBK : NBK <-->
	box[0]{
		not{kwh[1]{c1}} & not{kwh[2]{c2}} & not{kwh[3]{c3} & not{kwh[4]{c4}}}
	}

define unfold_s0 : s0 <--> c1 & c2 & not{c3} & not{c4} & mch4_KAO
define unfold_s1 : s1 <--> box[0]{c1 or c2 or c3 or c4}
define unfold_s2 : s2 <-->
	box[0]{
		(c1 & c2) or
      (c1 & c3) or
      (c1 & c4) or
      (c2 & c3) or
      (c2 & c4) or
      (c3 & c4)
	}

define unfold_s3 : s3 <-->
	box[0]{
		kwh[1]{c1} &
		kwh[2]{c2}
	}


let unfold_mchT = byDefsT
	[unfold_s3; unfold_s2; unfold_s1; unfold_s0;
	 unfold_NBK; unfold_mch4_KAO; unfold_kwh]

interactive lemma3 :
	sequent { s0; s2 >- concl {| kwh[1]{c1} & kwh[2]{c2} |} }

interactive wrong :
	sequent { s0; NBK; s2 >- concl {| kwh[1]{c1} & kwh[2]{c2} & kwh[3]{c3} & kwh[4]{c4} |} }

interactive lemma4 :
   sequent { s0; s2; NBK >- concl {| kwh[3]{c3} |} }

interactive lemma5 :
   sequent { s0; s2; NBK >- concl {| kwh[3]{c3} |} }

interactive muddy_children :
   sequent { s0; s2; NBK; s3 >- concl {| kwh[1]{c1} & kwh[2]{c2} & kwh[3]{c3} & kwh[4]{c4} |} }

