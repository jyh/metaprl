extends Czf_itt_set
extends Czf_itt_eq
extends Czf_itt_empty
extends Czf_itt_singleton
extends Czf_itt_setdiff
extends Czf_itt_union
extends Czf_itt_isect
extends Itt_bool
extends Itt_logic
extends Itt_theory

open Tactic_type.Conversionals

declare boolset
declare strue
declare sfalse
declare snot{'x}
declare sor{'a; 'b}
declare sand{'a; 'b}
declare sprop{'x}
declare simplies{'a; 'b}
declare siff{'a; 'b}
declare scand{'a; 'b}
declare scor{'a; 'b}
declare sxor{'a; 'b}
declare sxand{'a; 'b}

prec prec_snot
prec prec_sand
prec prec_sxand
prec prec_sxor
prec prec_sor
prec prec_simplies
prec prec_siff
prec prec_sprop

rewrite unfold_boolset   : boolset <--> collect{bool; x. ifthenelse{'x; sing{empty}; empty}}
rewrite unfold_strue    : strue <--> collect{unit; x. empty}
rewrite unfold_sfalse   : sfalse <--> collect{void; x. 'x}
rewrite unfold_snot     : snot{'x} <--> setdiff{sing{empty}; 'x}
rewrite unfold_sor      : sor{'a; 'b} <--> "union"{'a; 'b}
rewrite unfold_sand     : sand{'a; 'b} <--> "isect"{'a; 'b}
rewrite unfold_sprop    : sprop{'x} <--> eq{'x; strue}
rewrite unfold_simplies : simplies{'a; 'b} <--> sor{snot{'a}; 'b}
rewrite unfold_siff     : siff{'a; 'b} <--> sand{simplies{'a; 'b}; simplies{'b; 'a}}
rewrite unfold_scand    : scand{'a; 'b} <--> sand{'a; 'b}
rewrite unfold_scor     : scor{'a; 'b} <--> sor{'a; sand{snot{'a}; 'b}}
rewrite unfold_sxor     : sxor{'a; 'b} <--> sor{sand{'a; snot{'b}}; sand{snot{'a}; 'b}}
rewrite unfold_sxand   : sxand{'a; 'b} <--> sor{sand{'a; 'b}; sand{snot{'a}; snot{'b}}}

topval fold_boolset  : conv
topval fold_strue    : conv
topval fold_sfalse   : conv
topval fold_snot     : conv
topval fold_sor      : conv
topval fold_sand     : conv
topval fold_sprop    : conv
topval fold_simplies : conv
topval fold_siff     : conv
topval fold_scand    : conv
topval fold_scor     : conv
topval fold_sxor     : conv
topval fold_sxand    : conv

topval sxorAssoc1T   : int -> tactic
topval sxandAssoc1T  : int -> tactic
