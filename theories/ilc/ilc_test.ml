extends Ilc_extend



 interactive tt:
  ilc{| <H> >- linear{| 'A;'B;'C;'D;'E >- one|} |}

 interactive commute_tensor:
  ilc{| <H> >- linear{| "tensor"{'B;'A} >- "tensor"{'A;'B}|} |}


   interactive dup_bang:
   ilc{| <H> >- linear{|  >- impl{bang{'A}; tensor{'A; bang{'A}} }|} |}

  interactive forall_forall:
   ilc{| <H> >- linear{|  forall{z.'B['z]} >- forall{y.'B['y]}  |} |}

  interactive exists_exists:
   ilc{| <H> >- linear{|  exists{x.'B['x]} >- exists{y.'B['y]} |} |}

  interactive forall_exists:
   ilc{| <H> >- linear{|  forall{x.'B['x]} >- exists{y.'B['y]} |} |}

  interactive forall_forall2:
  ilc{| <H> >- linear{|  >- forall{s. forall{y.'B['y;'s]}}  |} |}

  interactive circ1:
  ilc{| <H> >- linear {| >- circ{"and"{"true";'b}} |} |}

   interactive con_exists:
   ilc{| <H> >- linear{| <#J> >- impl{'P[upd{alpha;1;3}]; exists{x.'P['x]}} |} |}

(*   interactive conc_exists: *)
(*    ilc{| <H> >- linear{|  'B[data{1}] >- exists{y.'B['y]}  |} |} *)

  interactive t2:
  ilc{| >- linear{| >-
  forall{l2.impl{'Lin['l2;3];
		 exists{x1.conj{tensor{'Lin['l2;'x1];top};
				top}}}} |} |}

  interactive test:
  ilc{| >- linear{| >- bang{circ{"not"{lt{4;0}}}} |} |}


   interactive t4:
   ilc{| >- linear{| >-
   forall{l5.impl{'Array['l5;10;alpha];
 	       exists{x3.exists{x4.conj{tensor{tensor{'Array['l5;'x3;'x4];
 						      bang{circ{"and"{lt{4;'x3};"not"{lt{4;0}}}}}};
 					       top};
 					exists{x1.exists{x2.tensor{tensor{'Array['l5;'x1;'x2];
 									  bang{circ{"and"{lt{5;'x1};"not"{lt{5;0}}}}}};
 								   impl{'Array['l5;'x1;upd{'x2;5;sel{'x4;4}}];
 									top}
 								 }}}}}}}}
   |} |}


  interactive t5:
  ilc{| >- linear{| >-
  forall{l5.impl{'Linear['l5;10];
		 exists{x4.conj{tensor{'Linear['l5;'x4];top};
                                forall{l3.impl{'Array['l3;'x4;alpha];
					       conj{top; conj{impl{bang{circ{"and"{lt{100;'x4};lt{0;100}}}};
								   exists{x1.exists{x2.tensor{tensor{'Array['l3;'x1;'x2];
												     bang{circ{"and"{lt{100;'x1};"not"{lt{100;0}}}}}};
											      impl{'Array['l3;'x1;upd{'x2;100;10}];top}}}}};
							      impl{bang{circ{"not"{"and"{lt{100;'x4};lt{0;100}}}}};top}}}}}}}}}
 |} |}

interactive t9:
  ilc{| >- linear{| >-
forall{x.forall{n.forall{ax.impl{ 'Array['x; 'n; 'ax];
exists{x9.exists{x10.conj{tensor{'Array['x;'x9;'x10];top};forall{l8.impl{'Array['l8;sub{'x9;1};alpha];forall{l7.impl{'Linear['l7;0];tensor{exists{x6.conj{conj{tensor{'Linear['l7;'x6];top};top};conj{impl{bang{circ{lt{'x6;sub{'x9;1}}}};exists{x4.exists{x5.conj{tensor{tensor{'Array['x;'x4;'x5];bang{circ{"and"{lt{'x6;'x4};"not"{lt{'x6;0}}}}}};top};exists{x2.exists{x3.tensor{tensor{'Array['l8;'x2;'x3];bang{circ{"and"{lt{'x6;'x2};"not"{lt{'x6;0}}}}}};impl{'Array['l8;'x2;upd{'x3;'x6;sel{'x5;'x6}}];tensor{exists{x1.'Linear['l7;'x1]};impl{'Linear['l7;add{'x6;1}];exists{v.exists{n2.exists{a.exists{b.tensor{tensor{tensor{tensor{tensor{tensor{'Array['x;'n;'a];'Array['l8;'n2;'b]};bang{circ{beq_int{'n;add{'n2;1}}}}};'Linear['l7;'v]};bang{circ{"not"{lt{'v;0}}}}};bang{circ{lt{'v;'n}}}};forall{j.impl{tensor{bang{circ{"not"{lt{'j;0}}}};bang{circ{lt{'j;'v}}}};bang{circ{beq_int{sel{'a;'j};sel{'b;'j}}}}}}}}}}}}}}}}}}}}};impl{bang{circ{"not"{lt{'x6;sub{'x9;1}}}}};exists{m1.exists{m2.exists{c.exists{d.exists{lx.exists{ly.tensor{tensor{tensor{tensor{'Array['lx;'m1;'c];'Array['ly;'m2;'d]};bang{circ{beq_int{'m1;add{'m2;1}}}}};top};forall{i.impl{tensor{bang{circ{"not"{lt{'i;0}}}};bang{circ{lt{'i;'m2}}}};bang{circ{beq_int{sel{'c;'i};sel{'d;'i}}}}}}}}}}}}}}}}};bang{impl{exists{v.exists{n2.exists{a.exists{b.tensor{tensor{tensor{tensor{tensor{tensor{'Array['x;'n;'a];'Array['l8;'n2;'b]};bang{circ{beq_int{'n;add{'n2;1}}}}};'Linear['l7;'v]};bang{circ{"not"{lt{'v;0}}}}};bang{circ{lt{'v;'n}}}};forall{j.impl{tensor{bang{circ{"not"{lt{'j;0}}}};bang{circ{lt{'j;'v}}}};bang{circ{beq_int{sel{'a;'j};sel{'b;'j}}}}}}}}}}};exists{x6.conj{conj{tensor{'Linear['l7;'x6];top};top};conj{impl{bang{circ{lt{'x6;sub{'x9;1}}}};exists{x4.exists{x5.conj{tensor{tensor{'Array['x;'x4;'x5];bang{circ{"and"{lt{'x6;'x4};"not"{lt{'x6;0}}}}}};top};exists{x2.exists{x3.tensor{tensor{'Array['l8;'x2;'x3];bang{circ{"and"{lt{'x6;'x2};"not"{lt{'x6;0}}}}}};impl{'Array['l8;'x2;upd{'x3;'x6;sel{'x5;'x6}}];tensor{exists{x1.'Linear['l7;'x1]};impl{'Linear['l7;add{'x6;1}];exists{v.exists{n2.exists{a.exists{b.tensor{tensor{tensor{tensor{tensor{tensor{'Array['x;'n;'a];'Array['l8;'n2;'b]};bang{circ{beq_int{'n;add{'n2;1}}}}};'Linear['l7;'v]};bang{circ{"not"{lt{'v;0}}}}};bang{circ{lt{'v;'n}}}};forall{j.impl{tensor{bang{circ{"not"{lt{'j;0}}}};bang{circ{lt{'j;'v}}}};bang{circ{beq_int{sel{'a;'j};sel{'b;'j}}}}}}}}}}}}}}}}}}}}};impl{bang{circ{"not"{lt{'x6;sub{'x9;1}}}}};exists{m1.exists{m2.exists{c.exists{d.exists{lx.exists{ly.tensor{tensor{tensor{tensor{'Array['lx;'m1;'c];'Array['ly;'m2;'d]};bang{circ{beq_int{'m1;add{'m2;1}}}}};top};forall{i.impl{tensor{bang{circ{"not"{lt{'i;0}}}};bang{circ{lt{'i;'m2}}}};bang{circ{beq_int{sel{'c;'i};sel{'d;'i}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
|} |}


 interactive t19:
 ilc {| >- linear {| >-
 forall{y.forall{al.impl{List{'y; 0;'al}; forall{l7.impl{tensor{Record{'l7;itemnext};tensor{tensor{one;Lin{add{'l7;0};5}};Lin{add{'l7;1};0}}};exists{x4.exists{x5.exists{x6.conj{tensor{bang{circ{Belong{next;'x4;'x5}}};tensor{Record{'l7;'x4};top}};tensor{Lin{add{'l7;'x5};'x6};impl{Lin{add{'l7;'x5};'y};tensor{plus{bang{circ{beq_int{'l7;0}}};exists{x3.exists{x1.exists{x2.tensor{bang{circ{beq_int{cons{5;'al};cons{'x1;'x3}}}};tensor{tensor{Record{'l7;itemnext};tensor{Lin{'l7;'x1};Lin{add{'l7;1};'x2}}};List{'x2;0;'x3}}}}}}};
impl{List{'l7;0;cons{5;'al}};List{'l7;0;cons{5;'al}}}}}}}}}}}}
			  }}}
 |}|}

interactive t20:
 ilc {| >- linear {| >-
forall{x.forall{al.forall{ y.forall{vy.impl{tensor{List{'x; 0; 'al}; Lin{'y; 'vy}};
conj{top;conj{impl{bang{circ{beq_int{'x;0}}};tensor{exists{x1.Lin{'y;'x1}};impl{Lin{'y;'x};exists{v.tensor{Lin{'y;'v};plus{bang{circ{beq_int{'v;0}}};tensor{exists{i.exists{beta.tensor{List{'v;0;'beta};bang{circ{beq_int{'al;cons{'i;'beta}}}}}}};top}}}}}}};impl{bang{circ{"not"{beq_int{'x;0}}}};exists{x9.tensor{List{'x;'tx;'x9};impl{plus{bang{circ{beq_int{'x;'tx}}};exists{x8.exists{x6.exists{x7.tensor{bang{circ{beq_int{'x9;cons{'x6;'x8}}}};tensor{tensor{Record{'x;itemnext};tensor{Lin{'x;'x6};Lin{add{'x;1};'x7}}};List{'x7;'tx;'x8}}}}}}};exists{x3.exists{x4.exists{x5.conj{tensor{bang{circ{Belong{next;'x3;'x4}}};tensor{Record{'x;'x3};tensor{Lin{add{'x;'x4};'x5};top}}};tensor{exists{x2.Lin{'y;'x2}};impl{Lin{'y;'x5};exists{v.tensor{Lin{'y;'v};plus{bang{circ{beq_int{'v;0}}};tensor{exists{i.exists{beta.tensor{List{'v;0;'beta};bang{circ{beq_int{'al;cons{'i;'beta}}}}}}};top}}}}}}}}}}}}}}}}}}}}}

|} |}

interactive t201:
 ilc {| >- linear {| >-
forall{x.forall{al.forall{ y.forall{vy.impl{tensor{List{'x; 0; 'al}; Lin{'y; 'vy}};
conj{top;conj{impl{bang{circ{beq_int{'x;0}}};tensor{exists{x1.Lin{'y;'x1}};impl{Lin{'y;'x};exists{v.tensor{Lin{'y;'v};tensor{exists{i.exists{beta.tensor{List{'v;0;'beta};bang{circ{beq_int{'al;cons{'i;'beta}}}}}}};top}}}}}};impl{bang{circ{"not"{beq_int{'x;0}}}};exists{x9.tensor{List{'x;0;'x9};impl{plus{tensor{bang{circ{beq_int{'x;0}}};bang{circ{beq_int{'x9;nil}}}};exists{x10.exists{x5.exists{x8.exists{x6.exists{x7.tensor{bang{circ{"not"{beq_int{'x;0}}}};tensor{bang{circ{beq_int{'x9;cons{'x6;'x8}}}};tensor{tensor{Array{'x;'x5;'x10};tensor{tensor{bang{circ{beq_int{sel{'x10;0};'x6}}};bang{circ{beq_int{sel{'x10;1};'x7}}}};bang{circ{beq_int{'x5;2}}}}};List{'x7;0;'x8}}}}}}}}}};exists{x3.exists{x4.conj{tensor{tensor{Array{'x;'x3;'x4};bang{circ{"and"{lt{1;'x3};"not"{lt{1;0}}}}}};top};tensor{exists{x2.Lin{'y;'x2}};impl{Lin{'y;sel{'x4;1}};exists{v.tensor{Lin{'y;'v};tensor{exists{i.exists{beta.tensor{List{'v;0;'beta};bang{circ{beq_int{'al;cons{'i;'beta}}}}}}};top}}}}}}}}}}}}}}
					  } }}}}
|} |}

interactive t21:
ilc {| >- linear {| >-
forall{a.forall{al.
forall{parent.forall{loopv.
impl{tensor{tensor{List{'a;'a;nil};List{'a;0;'al}};
	    tensor{ bang{circ{"not"{beq_int{'a;0}}}};
		    tensor{ Lin{'loopv; 'a}; Lin{'parent; 'a}}}};
exists{x18.tensor{List{'a;0;'x18};impl{plus{bang{circ{beq_int{'a;0}}};exists{x17.exists{x15.exists{x16.tensor{bang{circ{beq_int{'x18;cons{'x15;'x17}}}};tensor{tensor{Record{'a;itemnext};tensor{Lin{'a;'x15};Lin{add{'a;1};'x16}}};List{'x16;0;'x17}}}}}}};tensor{exists{x11.exists{x14.conj{conj{tensor{Lin{'loopv;'x14};top};conj{exists{x12.exists{x13.tensor{bang{circ{Belong{next;'x12;'x13}}};tensor{Record{'x14;'x12};tensor{Lin{add{'x14;'x13};'x11};top}}}}};top}};conj{impl{bang{circ{"not"{beq_int{'x11;0}}}};tensor{exists{x10.Lin{'parent;'x10}};impl{Lin{'parent;'x14};tensor{exists{x9.Lin{'loopv;'x9}};impl{Lin{'loopv;'x11};plus{tensor{bang{circ{beq_int{'a;'x14}}};impl{List{'a;'x14;nil};exists{x4.tensor{List{'x11;0;'x4};impl{plus{bang{circ{beq_int{'x11;0}}};exists{x3.exists{x1.exists{x2.tensor{bang{circ{beq_int{'x4;cons{'x1;'x3}}}};tensor{tensor{Record{'x11;itemnext};tensor{Lin{'x11;'x1};Lin{add{'x11;1};'x2}}};List{'x2;0;'x3}}}}}}};exists{beta1.exists{beta2.exists{b.exists{c.exists{d.exists{i.exists{j.tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{List{'a;'b;'beta1};Lin{'parent;'b}};Record{'b;'itemnext}};Lin{'b;'i}};Lin{add{'b;1};'c}};Lin{'loopv;'c}};Record{'c;'itemnext}};Lin{'c;'j}};Lin{add{'c;1};'d}};List{'d;0;'beta2}};bang{circ{beq_int{'al;cons{cons{cons{'beta1;'i};'j};'beta2}}}}}}}}}}}}}}}}};exists{x7.exists{x5.exists{x6.tensor{tensor{tensor{Record{'x6;itemnext};tensor{Lin{'x6;'x5};Lin{add{'x6;1};'x14}}};List{'a;'x6;'x7}};forall{x8.impl{tensor{List{'a;'x14;'x8};bang{circ{beq_int{'x8;cons{'x7;'x5}}}}};exists{x4.tensor{List{'x11;0;'x4};impl{plus{bang{circ{beq_int{'x11;0}}};exists{x3.exists{x1.exists{x2.tensor{bang{circ{beq_int{'x4;cons{'x1;'x3}}}};tensor{tensor{Record{'x11;itemnext};tensor{Lin{'x11;'x1};Lin{add{'x11;1};'x2}}};List{'x2;0;'x3}}}}}}};exists{beta1.exists{beta2.exists{b.exists{c.exists{d.exists{i.exists{j.tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{List{'a;'b;'beta1};Lin{'parent;'b}};Record{'b;'itemnext}};Lin{'b;'i}};Lin{add{'b;1};'c}};Lin{'loopv;'c}};Record{'c;'itemnext}};Lin{'c;'j}};Lin{add{'c;1};'d}};List{'d;0;'beta2}};bang{circ{beq_int{'al;cons{cons{cons{'beta1;'i};'j};'beta2}}}}}}}}}}}}}}}}}}}}}}}}}}};impl{bang{circ{"not"{"not"{beq_int{'x11;0}}}}};plus{exists{it.tensor{tensor{tensor{tensor{tensor{tensor{Lin{'parent;'a};Lin{'loopv;'a}};List{'a;'a;'nil}};Record{'a;'itemnext}};Lin{'a;'it}};Lin{add{'a;1};0}};List{0;0;'nil}}};exists{alpha.exists{ta.exists{it.exists{lv.exists{itt.tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{List{'a;'ta;'alpha};Lin{'parent;'ta}};Record{'ta;'itemnext}};Lin{'ta;'it}};Lin{add{'ta;1};'lv}};Lin{'loopv;'lv}};Record{'lv;'itemnext}};Lin{'lv;'itt}};Lin{add{'lv;1};0}};bang{circ{beq_int{'al;cons{cons{'alpha;'it};'itt}}}}};List{0;0;'nil}}}}}}}}}}}}};bang{impl{exists{beta1.exists{beta2.exists{b.exists{c.exists{d.exists{i.exists{j.tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{List{'a;'b;'beta1};Lin{'parent;'b}};Record{'b;'itemnext}};Lin{'b;'i}};Lin{add{'b;1};'c}};Lin{'loopv;'c}};Record{'c;'itemnext}};Lin{'c;'j}};Lin{add{'c;1};'d}};List{'d;0;'beta2}};bang{circ{beq_int{'al;cons{cons{cons{'beta1;'i};'j};'beta2}}}}}}}}}}}};exists{x11.exists{x14.conj{conj{tensor{Lin{'loopv;'x14};top};conj{exists{x12.exists{x13.tensor{bang{circ{Belong{next;'x12;'x13}}};tensor{Record{'x14;'x12};tensor{Lin{add{'x14;'x13};'x11};top}}}}};top}};conj{impl{bang{circ{"not"{beq_int{'x11;0}}}};tensor{exists{x10.Lin{'parent;'x10}};impl{Lin{'parent;'x14};tensor{exists{x9.Lin{'loopv;'x9}};impl{Lin{'loopv;'x11};plus{tensor{bang{circ{beq_int{'a;'x14}}};impl{List{'a;'x14;nil};exists{x4.tensor{List{'x11;0;'x4};impl{plus{bang{circ{beq_int{'x11;0}}};exists{x3.exists{x1.exists{x2.tensor{bang{circ{beq_int{'x4;cons{'x1;'x3}}}};tensor{tensor{Record{'x11;itemnext};tensor{Lin{'x11;'x1};Lin{add{'x11;1};'x2}}};List{'x2;0;'x3}}}}}}};exists{beta1.exists{beta2.exists{b.exists{c.exists{d.exists{i.exists{j.tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{List{'a;'b;'beta1};Lin{'parent;'b}};Record{'b;'itemnext}};Lin{'b;'i}};Lin{add{'b;1};'c}};Lin{'loopv;'c}};Record{'c;'itemnext}};Lin{'c;'j}};Lin{add{'c;1};'d}};List{'d;0;'beta2}};bang{circ{beq_int{'al;cons{cons{cons{'beta1;'i};'j};'beta2}}}}}}}}}}}}}}}}};exists{x7.exists{x5.exists{x6.tensor{tensor{tensor{Record{'x6;itemnext};tensor{Lin{'x6;'x5};Lin{add{'x6;1};'x14}}};List{'a;'x6;'x7}};forall{x8.impl{tensor{List{'a;'x14;'x8};bang{circ{beq_int{'x8;cons{'x7;'x5}}}}};exists{x4.tensor{List{'x11;0;'x4};impl{plus{bang{circ{beq_int{'x11;0}}};exists{x3.exists{x1.exists{x2.tensor{bang{circ{beq_int{'x4;cons{'x1;'x3}}}};tensor{tensor{Record{'x11;itemnext};tensor{Lin{'x11;'x1};Lin{add{'x11;1};'x2}}};List{'x2;0;'x3}}}}}}};exists{beta1.exists{beta2.exists{b.exists{c.exists{d.exists{i.exists{j.tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{List{'a;'b;'beta1};Lin{'parent;'b}};Record{'b;'itemnext}};Lin{'b;'i}};Lin{add{'b;1};'c}};Lin{'loopv;'c}};Record{'c;'itemnext}};Lin{'c;'j}};Lin{add{'c;1};'d}};List{'d;0;'beta2}};bang{circ{beq_int{'al;cons{cons{cons{'beta1;'i};'j};'beta2}}}}}}}}}}}}}}}}}}}}}}}}}}};impl{bang{circ{"not"{"not"{beq_int{'x11;0}}}}};plus{exists{it.tensor{tensor{tensor{tensor{tensor{tensor{Lin{'parent;'a};Lin{'loopv;'a}};List{'a;'a;'nil}};Record{'a;'itemnext}};Lin{'a;'it}};Lin{add{'a;1};0}};List{0;0;'nil}}};exists{alpha.exists{ta.exists{it.exists{lv.exists{itt.tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{List{'a;'ta;'alpha};Lin{'parent;'ta}};Record{'ta;'itemnext}};Lin{'ta;'it}};Lin{add{'ta;1};'lv}};Lin{'loopv;'lv}};Record{'lv;'itemnext}};Lin{'lv;'itt}};Lin{add{'lv;1};0}};bang{circ{beq_int{'al;cons{cons{'alpha;'it};'itt}}}}};List{0;0;'nil}}}}}}}}}}}}}}}}}}}
   } }}}}
|} |}

interactive t211:
ilc {| >- linear {| >-
forall{a.forall{al.
forall{parent.forall{loopv.
impl{tensor{tensor{List{'a;'a;nil};List{'a;0;'al}};
	    tensor{ bang{circ{"not"{beq_int{'a;0}}}};
		    tensor{ Lin{'loopv; 'a}; Lin{'parent; 'a}}}};
exists{x21.tensor{List{'a;0;'x21};impl{plus{tensor{bang{circ{beq_int{'a;0}}};bang{circ{beq_int{'x21;nil}}}};exists{x22.exists{x17.exists{x20.exists{x18.exists{x19.tensor{bang{circ{"not"{beq_int{'a;0}}}};tensor{bang{circ{beq_int{'x21;cons{'x18;'x20}}}};tensor{tensor{Array{'a;'x17;'x22};tensor{tensor{bang{circ{beq_int{sel{'x22;0};'x18}}};bang{circ{beq_int{sel{'x22;1};'x19}}}};bang{circ{beq_int{'x17;2}}}}};List{'x19;0;'x20}}}}}}}}}};tensor{exists{x15.exists{x14.exists{x16.conj{conj{tensor{Lin{'loopv;'x16};top};conj{tensor{Array{'x16;'x14;'x15};tensor{bang{circ{"and"{lt{1;'x14};"not"{lt{1;0}}}}};top}};top}};conj{impl{bang{circ{"not"{beq_int{sel{'x15;1};0}}}};tensor{exists{x13.Lin{'parent;'x13}};impl{Lin{'parent;'x16};tensor{exists{x12.Lin{'loopv;'x12}};impl{Lin{'loopv;sel{'x15;1}};plus{tensor{bang{circ{beq_int{'a;'x16}}};impl{bang{List{'a;'x16;nil}};exists{x5.tensor{List{sel{'x15;1};0;'x5};impl{plus{tensor{bang{circ{beq_int{sel{'x15;1};0}}};bang{circ{beq_int{'x5;nil}}}};exists{x6.exists{x1.exists{x4.exists{x2.exists{x3.tensor{bang{circ{"not"{beq_int{sel{'x15;1};0}}}};tensor{bang{circ{beq_int{'x5;cons{'x2;'x4}}}};tensor{tensor{Array{sel{'x15;1};'x1;'x6};tensor{tensor{bang{circ{beq_int{sel{'x6;0};'x2}}};bang{circ{beq_int{sel{'x6;1};'x3}}}};bang{circ{beq_int{'x1;2}}}}};List{'x3;0;'x4}}}}}}}}}};exists{beta1.exists{beta2.exists{b.exists{c.exists{d.exists{a1.exists{a2.exists{i.exists{j.tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{List{'a;'b;'beta1};Lin{'parent;'b}};Array{'b;2;'a1}};bang{circ{beq_int{sel{'a1;0};'i}}}};bang{circ{beq_int{sel{'a1;1};'c}}}};Lin{'loopv;'c}};Array{'c;2;'a2}};bang{circ{beq_int{sel{'a2;0};'j}}}};bang{circ{beq_int{sel{'a2;1};'d}}}};List{'d;0;'beta2}};bang{circ{beq_int{'al;cons{cons{cons{'beta1;'i};'j};'beta2}}}}}}}}}}}}}}}}}}};tensor{exists{x11.exists{x7.exists{x10.exists{x8.exists{x9.tensor{bang{circ{"not"{beq_int{'a;'x16}}}};tensor{tensor{Array{'x9;'x7;'x11};tensor{tensor{bang{circ{beq_int{sel{'x11;0};'x8}}};bang{circ{beq_int{sel{'x11;1};'x16}}}};bang{circ{beq_int{'x7;2}}}}};List{'a;'x9;'x10}}}}}}}};impl{List{'a;'x16;cons{'x10;'x8}};exists{x5.tensor{List{sel{'x15;1};0;'x5};impl{plus{tensor{bang{circ{beq_int{sel{'x15;1};0}}};bang{circ{beq_int{'x5;nil}}}};exists{x6.exists{x1.exists{x4.exists{x2.exists{x3.tensor{bang{circ{"not"{beq_int{sel{'x15;1};0}}}};tensor{bang{circ{beq_int{'x5;cons{'x2;'x4}}}};tensor{tensor{Array{sel{'x15;1};'x1;'x6};tensor{tensor{bang{circ{beq_int{sel{'x6;0};'x2}}};bang{circ{beq_int{sel{'x6;1};'x3}}}};bang{circ{beq_int{'x1;2}}}}};List{'x3;0;'x4}}}}}}}}}};exists{beta1.exists{beta2.exists{b.exists{c.exists{d.exists{a1.exists{a2.exists{i.exists{j.tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{List{'a;'b;'beta1};Lin{'parent;'b}};Array{'b;2;'a1}};bang{circ{beq_int{sel{'a1;0};'i}}}};bang{circ{beq_int{sel{'a1;1};'c}}}};Lin{'loopv;'c}};Array{'c;2;'a2}};bang{circ{beq_int{sel{'a2;0};'j}}}};bang{circ{beq_int{sel{'a2;1};'d}}}};List{'d;0;'beta2}};bang{circ{beq_int{'al;cons{cons{cons{'beta1;'i};'j};'beta2}}}}}}}}}}}}}}}}}}}}}}}}};impl{bang{circ{"not"{"not"{beq_int{sel{'x15;1};0}}}}};plus{exists{it.exists{a1.tensor{tensor{tensor{tensor{tensor{tensor{Lin{'parent;'a};Lin{'loopv;'a}};List{'a;'a;'nil}};Array{'a;2;'a1}};bang{circ{beq_int{sel{'a1;0};'it}}}};bang{circ{beq_int{sel{'a1;1};0}}}};List{0;0;'nil}}}};exists{alpha.exists{ta.exists{it.exists{lv.exists{itt.exists{a1.exists{a2.tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{List{'a;'ta;'alpha};Lin{'parent;'ta}};Array{'ta;2;'a1}};bang{circ{beq_int{sel{'a1;0};'it}}}};bang{circ{beq_int{sel{'a1;1};'lv}}}};Lin{'loopv;'lv}};Array{'lv;2;'a2}};bang{circ{beq_int{sel{'a2;0};'itt}}}};bang{circ{beq_int{sel{'a2;1};0}}}};bang{circ{beq_int{'al;cons{cons{'alpha;'it};'itt}}}}};List{0;0;'nil}}}}}}}}}}}}}}}};bang{impl{exists{beta1.exists{beta2.exists{b.exists{c.exists{d.exists{a1.exists{a2.exists{i.exists{j.tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{List{'a;'b;'beta1};Lin{'parent;'b}};Array{'b;2;'a1}};bang{circ{beq_int{sel{'a1;0};'i}}}};bang{circ{beq_int{sel{'a1;1};'c}}}};Lin{'loopv;'c}};Array{'c;2;'a2}};bang{circ{beq_int{sel{'a2;0};'j}}}};bang{circ{beq_int{sel{'a2;1};'d}}}};List{'d;0;'beta2}};bang{circ{beq_int{'al;cons{cons{cons{'beta1;'i};'j};'beta2}}}}}}}}}}}}}};exists{x15.exists{x14.exists{x16.conj{conj{tensor{Lin{'loopv;'x16};top};conj{tensor{Array{'x16;'x14;'x15};tensor{bang{circ{"and"{lt{1;'x14};"not"{lt{1;0}}}}};top}};top}};conj{impl{bang{circ{"not"{beq_int{sel{'x15;1};0}}}};tensor{exists{x13.Lin{'parent;'x13}};impl{Lin{'parent;'x16};tensor{exists{x12.Lin{'loopv;'x12}};impl{Lin{'loopv;sel{'x15;1}};plus{tensor{bang{circ{beq_int{'a;'x16}}};impl{bang{List{'a;'x16;nil}};exists{x5.tensor{List{sel{'x15;1};0;'x5};impl{plus{tensor{bang{circ{beq_int{sel{'x15;1};0}}};bang{circ{beq_int{'x5;nil}}}};exists{x6.exists{x1.exists{x4.exists{x2.exists{x3.tensor{bang{circ{"not"{beq_int{sel{'x15;1};0}}}};tensor{bang{circ{beq_int{'x5;cons{'x2;'x4}}}};tensor{tensor{Array{sel{'x15;1};'x1;'x6};tensor{tensor{bang{circ{beq_int{sel{'x6;0};'x2}}};bang{circ{beq_int{sel{'x6;1};'x3}}}};bang{circ{beq_int{'x1;2}}}}};List{'x3;0;'x4}}}}}}}}}};exists{beta1.exists{beta2.exists{b.exists{c.exists{d.exists{a1.exists{a2.exists{i.exists{j.tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{List{'a;'b;'beta1};Lin{'parent;'b}};Array{'b;2;'a1}};bang{circ{beq_int{sel{'a1;0};'i}}}};bang{circ{beq_int{sel{'a1;1};'c}}}};Lin{'loopv;'c}};Array{'c;2;'a2}};bang{circ{beq_int{sel{'a2;0};'j}}}};bang{circ{beq_int{sel{'a2;1};'d}}}};List{'d;0;'beta2}};bang{circ{beq_int{'al;cons{cons{cons{'beta1;'i};'j};'beta2}}}}}}}}}}}}}}}}}}};tensor{exists{x11.exists{x7.exists{x10.exists{x8.exists{x9.tensor{bang{circ{"not"{beq_int{'a;'x16}}}};tensor{tensor{Array{'x9;'x7;'x11};tensor{tensor{bang{circ{beq_int{sel{'x11;0};'x8}}};bang{circ{beq_int{sel{'x11;1};'x16}}}};bang{circ{beq_int{'x7;2}}}}};List{'a;'x9;'x10}}}}}}}};impl{List{'a;'x16;cons{'x10;'x8}};exists{x5.tensor{List{sel{'x15;1};0;'x5};impl{plus{tensor{bang{circ{beq_int{sel{'x15;1};0}}};bang{circ{beq_int{'x5;nil}}}};exists{x6.exists{x1.exists{x4.exists{x2.exists{x3.tensor{bang{circ{"not"{beq_int{sel{'x15;1};0}}}};tensor{bang{circ{beq_int{'x5;cons{'x2;'x4}}}};tensor{tensor{Array{sel{'x15;1};'x1;'x6};tensor{tensor{bang{circ{beq_int{sel{'x6;0};'x2}}};bang{circ{beq_int{sel{'x6;1};'x3}}}};bang{circ{beq_int{'x1;2}}}}};List{'x3;0;'x4}}}}}}}}}};exists{beta1.exists{beta2.exists{b.exists{c.exists{d.exists{a1.exists{a2.exists{i.exists{j.tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{List{'a;'b;'beta1};Lin{'parent;'b}};Array{'b;2;'a1}};bang{circ{beq_int{sel{'a1;0};'i}}}};bang{circ{beq_int{sel{'a1;1};'c}}}};Lin{'loopv;'c}};Array{'c;2;'a2}};bang{circ{beq_int{sel{'a2;0};'j}}}};bang{circ{beq_int{sel{'a2;1};'d}}}};List{'d;0;'beta2}};bang{circ{beq_int{'al;cons{cons{cons{'beta1;'i};'j};'beta2}}}}}}}}}}}}}}}}}}}}}}}}};impl{bang{circ{"not"{"not"{beq_int{sel{'x15;1};0}}}}};plus{exists{it.exists{a1.tensor{tensor{tensor{tensor{tensor{tensor{Lin{'parent;'a};Lin{'loopv;'a}};List{'a;'a;'nil}};Array{'a;2;'a1}};bang{circ{beq_int{sel{'a1;0};'it}}}};bang{circ{beq_int{sel{'a1;1};0}}}};List{0;0;'nil}}}};exists{alpha.exists{ta.exists{it.exists{lv.exists{itt.exists{a1.exists{a2.tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{List{'a;'ta;'alpha};Lin{'parent;'ta}};Array{'ta;2;'a1}};bang{circ{beq_int{sel{'a1;0};'it}}}};bang{circ{beq_int{sel{'a1;1};'lv}}}};Lin{'loopv;'lv}};Array{'lv;2;'a2}};bang{circ{beq_int{sel{'a2;0};'itt}}}};bang{circ{beq_int{sel{'a2;1};0}}}};bang{circ{beq_int{'al;cons{cons{'alpha;'it};'itt}}}}};List{0;0;'nil}}}}}}}}}}}}}}}}}}}}}}

   } }}}}
|}|}

interactive t212:
ilc {|a: data{Parameter}; al:data{Parameter} ; loopv:data{Parameter}; parent:data{Parameter};
sz: data{Parameter}; ele: data{Parameter}; beta:data{Parameter};
b: data{Parameter}; it:data{Parameter} ; bang{circ{"not"{beq_int{'a;0}}}};
bang{circ{beq_int{sel{'ele;0};'it}}};bang{circ{beq_int{sel{'ele;1};'b}}};
bang{circ{beq_int{'al;cons{'it;'beta}}}}; bang{circ{beq_int{'sz;2}}}
      >- linear {| Lin{'loopv; 'a};Lin{'parent; 'a};Array{'a;'sz;'ele}; List{'b;0;'beta}
      >-
exists{x15.exists{x14.exists{x16.conj{conj{tensor{Lin{'loopv;'x16};top};conj{tensor{Array{'x16;'x14;'x15};tensor{bang{circ{"and"{lt{1;'x14};"not"{lt{1;0}}}}};top}};top}};conj{impl{bang{circ{"not"{beq_int{sel{'x15;1};0}}}};tensor{exists{x13.Lin{'parent;'x13}};impl{Lin{'parent;'x16};tensor{exists{x12.Lin{'loopv;'x12}};impl{Lin{'loopv;sel{'x15;1}};plus{tensor{bang{circ{beq_int{'a;'x16}}};impl{bang{List{'a;'x16;nil}};exists{x5.tensor{List{sel{'x15;1};0;'x5};impl{plus{tensor{bang{circ{beq_int{sel{'x15;1};0}}};bang{circ{beq_int{'x5;nil}}}};exists{x6.exists{x1.exists{x4.exists{x2.exists{x3.tensor{bang{circ{"not"{beq_int{sel{'x15;1};0}}}};tensor{bang{circ{beq_int{'x5;cons{'x2;'x4}}}};tensor{tensor{Array{sel{'x15;1};'x1;'x6};tensor{tensor{bang{circ{beq_int{sel{'x6;0};'x2}}};bang{circ{beq_int{sel{'x6;1};'x3}}}};bang{circ{beq_int{'x1;2}}}}};List{'x3;0;'x4}}}}}}}}}};exists{beta1.exists{beta2.exists{b.exists{c.exists{d.exists{a1.exists{a2.exists{i.exists{j.tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{List{'a;'b;'beta1};Lin{'parent;'b}};Array{'b;2;'a1}};bang{circ{beq_int{sel{'a1;0};'i}}}};bang{circ{beq_int{sel{'a1;1};'c}}}};Lin{'loopv;'c}};Array{'c;2;'a2}};bang{circ{beq_int{sel{'a2;0};'j}}}};bang{circ{beq_int{sel{'a2;1};'d}}}};List{'d;0;'beta2}};bang{circ{beq_int{'al;cons{cons{cons{'beta1;'i};'j};'beta2}}}}}}}}}}}}}}}}}}};exists{x11.exists{x7.exists{x10.exists{x8.exists{x9.tensor{bang{circ{"not"{beq_int{'a;'x16}}}};tensor{Array{'x9;'x7;'x11};tensor{tensor{tensor{bang{circ{beq_int{sel{'x11;0};'x8}}};bang{circ{beq_int{sel{'x11;1};'x16}}}};bang{circ{beq_int{'x7;2}}}};tensor{List{'a;'x9;'x10};impl{List{'a;'x16;cons{'x10;'x8}};exists{x5.tensor{List{sel{'x15;1};0;'x5};impl{plus{tensor{bang{circ{beq_int{sel{'x15;1};0}}};bang{circ{beq_int{'x5;nil}}}};exists{x6.exists{x1.exists{x4.exists{x2.exists{x3.tensor{bang{circ{"not"{beq_int{sel{'x15;1};0}}}};tensor{bang{circ{beq_int{'x5;cons{'x2;'x4}}}};tensor{tensor{Array{sel{'x15;1};'x1;'x6};tensor{tensor{bang{circ{beq_int{sel{'x6;0};'x2}}};bang{circ{beq_int{sel{'x6;1};'x3}}}};bang{circ{beq_int{'x1;2}}}}};List{'x3;0;'x4}}}}}}}}}};exists{beta1.exists{beta2.exists{b.exists{c.exists{d.exists{a1.exists{a2.exists{i.exists{j.tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{List{'a;'b;'beta1};Lin{'parent;'b}};Array{'b;2;'a1}};bang{circ{beq_int{sel{'a1;0};'i}}}};bang{circ{beq_int{sel{'a1;1};'c}}}};Lin{'loopv;'c}};Array{'c;2;'a2}};bang{circ{beq_int{sel{'a2;0};'j}}}};bang{circ{beq_int{sel{'a2;1};'d}}}};List{'d;0;'beta2}};bang{circ{beq_int{'al;cons{cons{cons{'beta1;'i};'j};'beta2}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}};impl{bang{circ{"not"{"not"{beq_int{sel{'x15;1};0}}}}};plus{exists{it.exists{a1.tensor{tensor{tensor{tensor{tensor{Lin{'parent;'a};Lin{'loopv;'a}};Array{'a;2;'a1}};bang{circ{beq_int{sel{'a1;0};'it}}}};bang{circ{beq_int{sel{'a1;1};0}}}};List{0;0;'nil}}}};exists{alpha.exists{ta.exists{it.exists{lv.exists{itt.exists{a1.exists{a2.tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{List{'a;'ta;'alpha};Lin{'parent;'ta}};Array{'ta;2;'a1}};bang{circ{beq_int{sel{'a1;0};'it}}}};bang{circ{beq_int{sel{'a1;1};'lv}}}};Lin{'loopv;'lv}};Array{'lv;2;'a2}};bang{circ{beq_int{sel{'a2;0};'itt}}}};bang{circ{beq_int{sel{'a2;1};0}}}};bang{circ{beq_int{'al;cons{cons{'alpha;'it};'itt}}}}};List{0;0;'nil}}}}}}}}}}}}}}}}

|} |}


interactive t213:
ilc {|a: data{Parameter}; al:data{Parameter} ; loopv:data{Parameter}; parent:data{Parameter};
sz: data{Parameter}; ele: data{Parameter}; beta:data{Parameter};
b: data{Parameter}; it:data{Parameter} ; bang{circ{"not"{beq_int{'a;0}}}};
bang{circ{beq_int{sel{'ele;0};'it}}};bang{circ{beq_int{sel{'ele;1};'b}}};
bang{circ{beq_int{'al;cons{'it;'beta}}}}; bang{circ{beq_int{'sz;2}}}

      >- linear {|
      >-
bang{impl{exists{beta1.exists{beta2.exists{b.exists{c.exists{d.exists{a1.exists{a2.exists{i.exists{j.tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{List{'a;'b;'beta1};Lin{'parent;'b}};Array{'b;2;'a1}};bang{circ{beq_int{sel{'a1;0};'i}}}};bang{circ{beq_int{sel{'a1;1};'c}}}};Lin{'loopv;'c}};Array{'c;2;'a2}};bang{circ{beq_int{sel{'a2;0};'j}}}};bang{circ{beq_int{sel{'a2;1};'d}}}};List{'d;0;'beta2}};bang{circ{beq_int{'al;cons{cons{cons{'beta1;'i};'j};'beta2}}}}}}}}}}}}}};exists{x15.exists{x14.exists{x16.conj{conj{tensor{Lin{'loopv;'x16};top};conj{tensor{Array{'x16;'x14;'x15};tensor{bang{circ{"and"{lt{1;'x14};"not"{lt{1;0}}}}};top}};top}};conj{impl{bang{circ{"not"{beq_int{sel{'x15;1};0}}}};tensor{exists{x13.Lin{'parent;'x13}};impl{Lin{'parent;'x16};tensor{exists{x12.Lin{'loopv;'x12}};impl{Lin{'loopv;sel{'x15;1}};plus{tensor{bang{circ{beq_int{'a;'x16}}};impl{bang{List{'a;'x16;nil}};exists{x5.tensor{List{sel{'x15;1};0;'x5};impl{plus{tensor{bang{circ{beq_int{sel{'x15;1};0}}};bang{circ{beq_int{'x5;nil}}}};exists{x6.exists{x1.exists{x4.exists{x2.exists{x3.tensor{bang{circ{"not"{beq_int{sel{'x15;1};0}}}};tensor{bang{circ{beq_int{'x5;cons{'x2;'x4}}}};tensor{tensor{Array{sel{'x15;1};'x1;'x6};tensor{tensor{bang{circ{beq_int{sel{'x6;0};'x2}}};bang{circ{beq_int{sel{'x6;1};'x3}}}};bang{circ{beq_int{'x1;2}}}}};List{'x3;0;'x4}}}}}}}}}};exists{beta1.exists{beta2.exists{b.exists{c.exists{d.exists{a1.exists{a2.exists{i.exists{j.tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{List{'a;'b;'beta1};Lin{'parent;'b}};Array{'b;2;'a1}};bang{circ{beq_int{sel{'a1;0};'i}}}};bang{circ{beq_int{sel{'a1;1};'c}}}};Lin{'loopv;'c}};Array{'c;2;'a2}};bang{circ{beq_int{sel{'a2;0};'j}}}};bang{circ{beq_int{sel{'a2;1};'d}}}};List{'d;0;'beta2}};bang{circ{beq_int{'al;cons{cons{cons{'beta1;'i};'j};'beta2}}}}}}}}}}}}}}}}}}};exists{x11.exists{x7.exists{x10.exists{x8.exists{x9.tensor{bang{circ{"not"{beq_int{'a;'x16}}}};tensor{Array{'x9;'x7;'x11};tensor{tensor{tensor{bang{circ{beq_int{sel{'x11;0};'x8}}};bang{circ{beq_int{sel{'x11;1};'x16}}}};bang{circ{beq_int{'x7;2}}}};tensor{List{'a;'x9;'x10};impl{List{'a;'x16;cons{'x10;'x8}};exists{x5.tensor{List{sel{'x15;1};0;'x5};impl{plus{tensor{bang{circ{beq_int{sel{'x15;1};0}}};bang{circ{beq_int{'x5;nil}}}};exists{x6.exists{x1.exists{x4.exists{x2.exists{x3.tensor{bang{circ{"not"{beq_int{sel{'x15;1};0}}}};tensor{bang{circ{beq_int{'x5;cons{'x2;'x4}}}};tensor{tensor{Array{sel{'x15;1};'x1;'x6};tensor{tensor{bang{circ{beq_int{sel{'x6;0};'x2}}};bang{circ{beq_int{sel{'x6;1};'x3}}}};bang{circ{beq_int{'x1;2}}}}};List{'x3;0;'x4}}}}}}}}}};exists{beta1.exists{beta2.exists{b.exists{c.exists{d.exists{a1.exists{a2.exists{i.exists{j.tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{List{'a;'b;'beta1};Lin{'parent;'b}};Array{'b;2;'a1}};bang{circ{beq_int{sel{'a1;0};'i}}}};bang{circ{beq_int{sel{'a1;1};'c}}}};Lin{'loopv;'c}};Array{'c;2;'a2}};bang{circ{beq_int{sel{'a2;0};'j}}}};bang{circ{beq_int{sel{'a2;1};'d}}}};List{'d;0;'beta2}};bang{circ{beq_int{'al;cons{cons{cons{'beta1;'i};'j};'beta2}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}};impl{bang{circ{"not"{"not"{beq_int{sel{'x15;1};0}}}}};plus{exists{it.exists{a1.tensor{tensor{tensor{tensor{tensor{Lin{'parent;'a};Lin{'loopv;'a}};Array{'a;2;'a1}};bang{circ{beq_int{sel{'a1;0};'it}}}};bang{circ{beq_int{sel{'a1;1};0}}}};List{0;0;'nil}}}};exists{alpha.exists{ta.exists{it.exists{lv.exists{itt.exists{a1.exists{a2.tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{tensor{List{'a;'ta;'alpha};Lin{'parent;'ta}};Array{'ta;2;'a1}};bang{circ{beq_int{sel{'a1;0};'it}}}};bang{circ{beq_int{sel{'a1;1};'lv}}}};Lin{'loopv;'lv}};Array{'lv;2;'a2}};bang{circ{beq_int{sel{'a2;0};'itt}}}};bang{circ{beq_int{sel{'a2;1};0}}}};bang{circ{beq_int{'al;cons{cons{'alpha;'it};'itt}}}}};List{0;0;'nil}}}}}}}}}}}}}}}}}}




|} |}
