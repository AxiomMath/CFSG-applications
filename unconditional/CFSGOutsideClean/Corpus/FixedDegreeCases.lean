import CFSG.Permutation.FiveTransitive.FullFixerSharpFive
import CFSGOutside.Corpus.FixedDegreeCases
import CFSGOutsideClean.Corpus.Defs.FixedNormalizerAction

/-! The corpus proves the statement that `CFSGOutside.Corpus.FixedDegreeCases` assumes. -/

instance CFSGOutsideClean.Corpus.fixedDegreeCases : CFSGOutside.Corpus.FixedDegreeCases :=
  ⟨CFSG.FiveTransitive.FullFixerSharpFive.fixed_degree_cases⟩
