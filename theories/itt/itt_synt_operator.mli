extends Itt_nat
extends Itt_list2

declare BOperator
declare Operator
declare op_bdepth{'op}
declare shape{'op}
declare arity{'op}
declare is_same_op{'op_1;'op_2} (* Do not consider  op_bdepth *)
declare inject{'op; 'n} (* Op * Nat -> BOp *)
declare unbind{'op}
declare bind{'op}
declare bind{'op;'n}

iform unfold_arity : arity{'op} <--> length{shape{'op}}
