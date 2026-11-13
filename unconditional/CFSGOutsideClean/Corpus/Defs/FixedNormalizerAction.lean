import CFSG.Permutation.FiveTransitive.FixedNormalizerAction
import CFSGOutside.Corpus.Defs.FixedNormalizerAction

/-! The definitions copied into `CFSGOutside.Corpus.Defs.FixedNormalizerAction` are the corpus definitions. -/

namespace CFSGOutsideClean.Corpus.FiveTransitive.FixedNormalizerAction

theorem normalizer_eq {G : Type*} [Group G] (Q : Subgroup G) :
    CFSGOutside.Corpus.FiveTransitive.FixedNormalizerAction.Normalizer Q =
      CFSG.FiveTransitive.FixedNormalizerAction.Normalizer Q :=
  rfl

theorem inside_eq {G : Type*} [Group G] (Q : Subgroup G) :
    CFSGOutside.Corpus.FiveTransitive.FixedNormalizerAction.Inside Q =
      CFSG.FiveTransitive.FixedNormalizerAction.Inside Q :=
  rfl

theorem fixed_eq {G X : Type*} [Group G] [MulAction G X] (Q : Subgroup G) :
    CFSGOutside.Corpus.FiveTransitive.FixedNormalizerAction.Fixed (X := X) Q =
      CFSG.FiveTransitive.FixedNormalizerAction.Fixed (X := X) Q :=
  rfl

end CFSGOutsideClean.Corpus.FiveTransitive.FixedNormalizerAction
