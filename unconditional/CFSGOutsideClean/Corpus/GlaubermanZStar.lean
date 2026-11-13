import CFSG.LocalAnalysis.ZStar
import CFSGOutside.Corpus.GlaubermanZStar

/-! The corpus proves the statement that `CFSGOutside.Corpus.GlaubermanZStar` assumes. -/

instance CFSGOutsideClean.Corpus.glaubermanZStar : CFSGOutside.Corpus.GlaubermanZStar :=
  ⟨fun G _ _ t ht1 ht2 hiso => CFSG.ZStar.glauberman_zStar G t ht1 ht2 hiso⟩
