import CFSG.ClassicalInvolution.Q3.Q3NMM11
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.M11Final
import CFSGOutside.Corpus.M11AutInner
import CFSGOutsideClean.Corpus.Defs.NativeM11
import CFSGOutsideClean.Corpus.Defs.LowTwoRankCatalog

/-! The corpus proves the statements that `CFSGOutside.Corpus.M11AutInner` and
`CFSGOutside.Corpus.NativeM11EquivOpen` assume. The copied models of `M₁₁` are the corpus ones by `rfl`. -/

instance CFSGOutsideClean.Corpus.m11AutInner : CFSGOutside.Corpus.M11AutInner :=
  ⟨fun φ => CFSG.ClassicalInvolution.Q3.Q3NM.m11_aut_inner φ⟩

instance CFSGOutsideClean.Corpus.nativeM11EquivOpen : CFSGOutside.Corpus.NativeM11EquivOpen :=
  ⟨⟨CFSG.EvenSporadicStandard.HNRecog.Section3Model.nativeEquivOpen⟩⟩
