import CFSG.ClassicalInvolution.QuaternionStructure
import CFSGOutside.Corpus.QuaternionSylowStructure
import CFSGOutsideClean.Corpus.Defs.OddCore
import CFSGOutsideClean.Corpus.Defs.OddCoreDihedral

/-! The corpus proves the statement that `CFSGOutside.Corpus.QuaternionSylowStructure` assumes. The copied
`oddCore` and `Open.IsQuasisimple` are the corpus definitions by `rfl`. -/

universe u

instance CFSGOutsideClean.Corpus.quaternionSylowStructure : CFSGOutside.Corpus.QuaternionSylowStructure.{u} :=
  ⟨fun S hS => CFSG.ClassicalInvolution.quaternion_sylow_structure S hS⟩
