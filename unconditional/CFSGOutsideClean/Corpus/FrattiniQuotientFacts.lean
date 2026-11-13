import CFSG.GroupTheory.FrattiniQuotient
import CFSGOutside.Corpus.FrattiniQuotientFacts
import CFSGOutsideClean.Corpus.Defs.ElementaryAbelian
import CFSGOutsideClean.Corpus.Defs.FrobeniusFrattini

/-! The corpus proves the statements that `CFSGOutside.Corpus.FrattiniElementaryQuotient` and
`CFSGOutside.Corpus.FrattiniAutomorphismKernel` assume. The copied `IsElementaryAbelian` is matched to the corpus
class by `CFSGOutsideClean.Corpus.isElementaryAbelian_iff`; `quotientAutomorphism` is the corpus definition by
`rfl`. -/

universe u

namespace CFSGOutsideClean.Corpus

instance frattiniElementaryQuotient : CFSGOutside.Corpus.FrattiniElementaryQuotient.{u} :=
  ⟨fun hP => by
    simp_rw [isElementaryAbelian_iff]
    exact CFSG.GroupTheory.frattini_elementary_quotient hP⟩

instance frattiniAutomorphismKernel : CFSGOutside.Corpus.FrattiniAutomorphismKernel.{u} :=
  ⟨fun hP => CFSG.GroupTheory.frattini_automorphism_kernel hP⟩

end CFSGOutsideClean.Corpus
