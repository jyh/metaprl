open Basic_tactics

declare bterm
declare sequent_arg{'t}
declare term

declare if_bterm{'t; 'tt}

declare dest_bterm{'bt}

declare make_bterm{'bt; 'bt1}

val reduce_ifbterm : conv
