import CFSG.Walter.J1Props.Elt
import CFSGOutside.Corpus.CardWalterJ1
import CFSGOutsideClean.Corpus.Defs.J1Models

/-! The corpus proves the statement that `CFSGOutside.Corpus.CardWalterJ1` assumes. -/

instance CFSGOutsideClean.Corpus.cardWalterJ1 : CFSGOutside.Corpus.CardWalterJ1 :=
  ⟨by rw [CFSGOutsideClean.Corpus.walterJ1_eq]; exact CFSG.Walter.J1Props.card_walterJ1⟩
