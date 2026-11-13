import CFSG.LieType.Ree.SuzukiOvoidAction
import CFSG.RankThree.PartTwo.Sec4.Census.BridgeSuzuki
import CFSGOutside.Corpus.HallPaige.LieSuzuki

/-! The corpus proves the statements that `CFSGOutside.Corpus.HallPaige.LieSuzuki` assumes. -/

instance CFSGOutsideClean.Corpus.hpLieSuzukiSuzukiOmega : CFSGOutside.Corpus.Lie.SuzukiOmega :=
  ⟨CFSG.LieType.Ree.suzuki_smul_mem_suzukiOmega⟩

instance CFSGOutsideClean.Corpus.hpLieSuzukiSuzukiOvoid : CFSGOutside.Corpus.Lie.SuzukiOvoid :=
  ⟨CFSG.LieType.Ree.suzuki_ovoid_double_transitivity, CFSG.RankThree.PartTwo.Sec4.Census.suzukiModel_of_index⟩
