import CFSG.Milestones.LR_semidihedral_simple_recognition
import CFSGOutside.Corpus.LrSemidihedralSimpleRecognition
import CFSGOutsideClean.Corpus.Defs.LowTwoRankCatalog
import CFSGOutsideClean.Corpus.Defs.TwoGroupShapes

/-! The corpus proves the statement that `CFSGOutside.Corpus.LrSemidihedralSimpleRecognition` assumes
(Alperin–Brauer–Gorenstein). The copied `SemidihedralGroup`, `PSU3` and `M11` are the corpus ones by `rfl`. -/

instance CFSGOutsideClean.Corpus.lrSemidihedralSimpleRecognition :
    CFSGOutside.Corpus.LrSemidihedralSimpleRecognition :=
  ⟨fun G _ _ _ hnonab P hsd => CFSG.Milestones.lr_semidihedral_simple_recognition_2 G hnonab P hsd⟩
