extends Itt_fun
extends Itt_nat

define unfold_compose : compose{'f;'g} <--> lambda{x.'f ('g 'x)}

declare fun_exp{'f;'n}
declare fun_exp{x.'f['x];'n}

declare id

