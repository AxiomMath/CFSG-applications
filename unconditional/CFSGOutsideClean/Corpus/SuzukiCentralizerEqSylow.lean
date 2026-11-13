import CFSG.RankThree.SteinbergR3ESuzukiInvolutionCentralizers
import CFSGOutside.Corpus.SuzukiCentralizerEqSylow

/-! The corpus proves the statement that `CFSGOutside.Corpus.SuzukiCentralizerEqSylow` assumes. -/

instance CFSGOutsideClean.Corpus.suzukiCentralizerEqSylow :
    CFSGOutside.Corpus.SuzukiCentralizerEqSylow :=
  ⟨by
    intro a K _ _ hK z hz Q hzQ
    exact CFSG.RankThree.centralizer_eq_sylow hK hz Q hzQ⟩
