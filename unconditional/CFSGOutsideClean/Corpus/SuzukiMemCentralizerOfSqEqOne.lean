import CFSG.RankThree.S4Free.Stellmacher24Sz
import CFSGOutside.Corpus.SuzukiMemCentralizerOfSqEqOne

/-! The corpus proves the statement that `CFSGOutside.Corpus.SuzukiMemCentralizerOfSqEqOne` assumes. -/

universe u

instance CFSGOutsideClean.Corpus.suzukiMemCentralizerOfSqEqOne :
    CFSGOutside.Corpus.SuzukiMemCentralizerOfSqEqOne.{u} :=
  ⟨by
    intro a K _ _ X _ hK e S z hzS hz
    exact CFSG.RankThree.S4Free.Suzuki.mem_centralizer_of_sq_eq_one hK e S hzS hz⟩
