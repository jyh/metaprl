open Refiner.Refiner.TermType
open Tactic_type.Conversionals

declare rename[a:t, b:t]{'r}
declare rename_mul_add{'S}
declare rename_add_mul{'S}
declare as_additive{'S}

topval renameFieldC :  term -> conv
topval renameFieldT :  term -> tactic

topval foldAdditiveC : term -> conv
topval foldAdditiveT : term -> tactic
topval unfoldAdditiveC : term -> conv
topval unfoldAdditiveT : term -> tactic
topval useAdditiveWithT : term -> tactic -> tactic
topval useAdditiveWithAutoT : term -> tactic

topval test : term -> term

topval reverseOrderC : term -> conv
topval reverseOrderT : term -> tactic


