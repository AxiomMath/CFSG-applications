import CFSG.GroupTheory.FrobeniusNormalComplement
import CFSGOutside.Corpus.FrobeniusNormalPComplement
import CFSGOutsideClean.Corpus.Defs.FrobeniusFrattini

/-! The corpus proves the statement that `CFSGOutside.Corpus.FrobeniusNormalPComplement` assumes. The copied
`IsNormalPComplement` is the corpus definition by `Iff.rfl`. -/

universe u

instance CFSGOutsideClean.Corpus.frobeniusNormalPComplement : CFSGOutside.Corpus.FrobeniusNormalPComplement.{u} :=
  ⟨fun p _ => CFSG.GroupTheory.frobenius_normal_p_complement p⟩
