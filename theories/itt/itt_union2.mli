extends Itt_bool

define is_inl: is_inl{'t} <--> decide{'t; x.btrue; y.bfalse}
define is_inr: is_inr{'t} <--> decide{'t; y.bfalse; x.btrue}
