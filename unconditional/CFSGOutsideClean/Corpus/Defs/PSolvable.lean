import CFSG.GroupTheory.HallHigmanPiCore
import CFSGOutside.Corpus.Defs.PSolvable

/-! The definition copied into `CFSGOutside.Corpus.Defs.PSolvable` is the corpus definition. -/

namespace CFSGOutsideClean.Corpus

theorem isPSolvable_eq (p : ℕ) (X : Type*) [Group X] :
    CFSGOutside.Corpus.IsPSolvable p X = CFSG.HallHigman.IsPSolvable p X :=
  rfl

end CFSGOutsideClean.Corpus
