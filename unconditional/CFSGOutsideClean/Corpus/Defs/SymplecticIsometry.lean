import CFSG.LocalAnalysis.ComponentInitial.LinearIsometry
import CFSG.ClassicalGroups.Alternating.Transvections
import CFSGOutside.Corpus.Defs.SymplecticIsometry

/-! The definitions copied into `CFSGOutside.Corpus.Defs.SymplecticIsometry` are the corpus definitions. -/

namespace CFSGOutsideClean.Corpus

theorem bilinIsometryGroup_eq {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    (B : LinearMap.BilinForm R M) :
    CFSGOutside.Corpus.LocalAnalysis.ComponentInitial.bilinIsometryGroup B =
      CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup B :=
  rfl

theorem symplecticTransvection_eq {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (hB : B.IsAlt) (a : V) (c : K) :
    CFSGOutside.Corpus.ClassicalGroups.Alternating.symplecticTransvection B hB a c =
      CFSG.ClassicalGroups.Alternating.symplecticTransvection B hB a c :=
  rfl

end CFSGOutsideClean.Corpus
