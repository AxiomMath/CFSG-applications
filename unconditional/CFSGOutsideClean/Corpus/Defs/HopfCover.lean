import CFSG.RankThree.PerfectCover.HopfCover
import CFSGOutside.Corpus.Defs.HopfCover

/-! The definitions copied into `CFSGOutside.Corpus.Defs.HopfCover` are the corpus definitions. -/

universe u

namespace CFSGOutsideClean.Corpus

theorem hopfCover_eq (S : Type u) [Group S] :
    CFSGOutside.Corpus.RankThree.PerfectCover.HopfCover S = CFSG.RankThree.PerfectCover.HopfCover S :=
  rfl

theorem hopfCoverMap_eq (S : Type u) [Group S] :
    (CFSGOutside.Corpus.RankThree.PerfectCover.hopfCoverMap S :
        CFSG.RankThree.PerfectCover.HopfCover S →* S) =
      CFSG.RankThree.PerfectCover.hopfCoverMap S :=
  rfl

theorem hopfMultiplier_eq (S : Type u) [Group S] :
    (CFSGOutside.Corpus.RankThree.PerfectCover.hopfMultiplier S :
        Subgroup (CFSG.RankThree.PerfectCover.HopfCover S)) =
      CFSG.RankThree.PerfectCover.hopfMultiplier S :=
  rfl

end CFSGOutsideClean.Corpus
