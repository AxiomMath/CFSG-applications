import CFSG.ClassicalInvolution.Orders.Ree
import CFSGOutside.Corpus.CardOfReeTitsModelTwistedG2
import CFSGOutsideClean.Corpus.Defs.J1Models
import CFSGOutsideClean.Corpus.Defs.ReeModel

/-! The corpus proves the statement that `CFSGOutside.Corpus.CardOfReeTitsModelTwistedG2` assumes. -/

instance CFSGOutsideClean.Corpus.cardOfReeTitsModelTwistedG2 :
    CFSGOutside.Corpus.CardOfReeTitsModelTwistedG2 :=
  ⟨fun {_ _ p f} h =>
    CFSG.ClassicalInvolution.card_of_reeTitsModel_twistedG2
      ((CFSGOutsideClean.Corpus.reeTitsModel_twistedG2_iff p f).1 h)⟩
