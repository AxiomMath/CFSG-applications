import CFSG.FeitThompson.OddOrderTheorem
import CFSGOutside.Corpus.OddOrder

/-! The corpus proves the statement that `CFSGOutside.Corpus.OddOrder` assumes. -/

universe u

instance CFSGOutsideClean.Corpus.oddOrder : CFSGOutside.Corpus.OddOrder.{u} :=
  ⟨fun G _ _ hG => CFSG.FeitThompson.isSolvable_of_odd_natCard G hG⟩
