import CFSG.Open.Catalog
import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitTwoGroupShapes
import CFSGOutside.Corpus.Defs.TwoGroupShapes

/-! The definitions copied into `CFSGOutside.Corpus.Defs.TwoGroupShapes` are the corpus definitions. -/

namespace CFSGOutsideClean.Corpus

theorem semidihedralRels_eq (n : ℕ) :
    CFSGOutside.Corpus.Open.semidihedralRels n = CFSG.Open.semidihedralRels n :=
  rfl

theorem semidihedralGroup_eq (n : ℕ) :
    CFSGOutside.Corpus.Open.SemidihedralGroup n = CFSG.Open.SemidihedralGroup n :=
  rfl

theorem wreathedTwoGroup_eq (n : ℕ) :
    CFSGOutside.Corpus.Open.WreathedTwoGroup n = CFSG.Open.WreathedTwoGroup n :=
  rfl

theorem atMostOneInvolution_iff (P : Type*) [Group P] :
    CFSGOutside.Corpus.AtMostOneInvolution P ↔
      CFSG.ComponentClassification.AschbacherToolkit.AtMostOneInvolution P :=
  Iff.rfl

end CFSGOutsideClean.Corpus
