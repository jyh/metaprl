open Refiner.Refiner.Term
open Tactic_type.Conversionals

topval renameFieldC :  term -> conv
topval renameFieldT :  term -> tactic

topval foldAdditiveC : term -> conv
topval foldAdditiveT : term -> tactic
topval unfoldAdditiveC : term -> conv
topval unfoldAdditiveT : term -> tactic
topval useAdditiveWithT : term -> tactic -> tactic
topval useAdditiveWithAutoT : term -> tactic
