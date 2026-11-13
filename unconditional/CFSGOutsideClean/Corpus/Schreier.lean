import CFSG.RankThree.PartOne.TCB.SchreierFinal
import CFSGOutside.Corpus.Schreier
import CFSGOutsideClean.Corpus.Defs.OuterAutomorphisms

/-! The corpus proves the statement that `CFSGOutside.Corpus.Schreier` assumes. -/

instance CFSGOutsideClean.Corpus.schreier : CFSGOutside.Corpus.Schreier :=
  ⟨fun X _ _ _ hnab hcat =>
    (CFSGOutsideClean.Corpus.ComponentClassification.OuterAutomorphisms.isSolvable_outer_iff X).2
      (CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds X hnab hcat)⟩
