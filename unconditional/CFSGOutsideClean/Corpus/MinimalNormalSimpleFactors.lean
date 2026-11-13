import CFSG.GroupTheory.LocalCores.MinimalNormal
import CFSGOutside.Corpus.MinimalNormalSimpleFactors
import CFSGOutsideClean.Corpus.Defs.Conjugate

/-! The corpus proves the statement that `CFSGOutside.Corpus.MinimalNormalSimpleFactors` assumes. The copied
`conjugate` is the corpus definition by `rfl` (`CFSGOutsideClean.Corpus.conjugate_eq`). -/

universe u

instance CFSGOutsideClean.Corpus.minimalNormalSimpleFactors :
    CFSGOutside.Corpus.MinimalNormalSimpleFactors.{u} :=
  ⟨@CFSG.LocalCores.minimal_normal_simple_factors⟩
