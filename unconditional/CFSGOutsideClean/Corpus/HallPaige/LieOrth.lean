import CFSG.RankThree.PartTwo.Census.Carrier.SpinBOdd
import CFSG.RankThree.PartTwo.Census.Carrier.SpinDOdd
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd
import CFSGOutside.Corpus.HallPaige.LieOrth

/-! The corpus proves the statements that `CFSGOutside.Corpus.HallPaige.LieOrth` assumes. -/

instance CFSGOutsideClean.Corpus.hpLieOrthOrthEquivs : CFSGOutside.Corpus.Lie.OrthEquivs :=
  ⟨fun r q hv hp hr => ⟨CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj_odd r q hv hp hr⟩,
    fun r q hv => ⟨CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid r q hv⟩, CFSG.RankThree.PartTwo.Census.Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid⟩
