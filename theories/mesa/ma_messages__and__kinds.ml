extends Nuprl_messages__and__kinds

open Dtactic

interactive nuprl_mkid_eq_elim  {| elim[] |} 'Gamma:
   sequent  { <Gamma>; u: 'l_1 = 'l_2 in atom; v: 'n_1='n_2 in nat;  <Delta['u]> >- 'C['u] } -->
   sequent  { <Gamma>; u: mkid{'l_1;'n_1} = mkid{'l_2;'n_2} in Id;  <Delta['u]> >- 'C['u] }

interactive nuprl_not_locl_rcv  {| elim[] |} 'Gamma :
   sequent  { <Gamma>; u:"equal"[]{"Knd"[]{};"locl"[]{'"a"};"rcv"[]{'"l";'"tg"}}; <Delta['u]> >- 'C['u] }

interactive nuprl_not_rcv_locl  {| elim[] |} 'Gamma :
   sequent  { <Gamma>; u:"equal"[]{"Knd"[]{};"rcv"[]{'"l";'"tg"};"locl"[]{'"a"}}; <Delta['u]> >- 'C['u] }

interactive nuprl_knd_eq_elim1  {| elim[] |} 'Gamma :
   sequent  { <Gamma>; u:"equal"[]{Id; '"a_1"; '"a_2"};  <Delta['u]> >- 'C['u] } -->
   sequent  { <Gamma>; u:"equal"[]{"Knd"[]{};"locl"[]{'"a_1"};"locl"[]{'"a_2"}}; <Delta['u]> >- 'C['u] }

interactive nuprl_knd_eq_elim2  {| elim[] |} 'Gamma :
   sequent  { <Gamma>; u:"equal"[]{IdLnk; '"l_1"; '"l_2"}; v:"equal"[]{Id; '"tg_1"; '"tg_2"};  <Delta['u]> >- 'C['u] } -->
   sequent  { <Gamma>; u:"equal"[]{"Knd"[]{};"rcv"[]{'"l_1";'"tg_1"};"rcv"[]{'"l_2";'"tg_2"}}; <Delta['u]> >- 'C['u] }


let resource typeinf += <<mkid{'l;'n}>>,  Typeinf.infer_const <<Id>>

