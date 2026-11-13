import CFSG.LocalAnalysis.AGLEmbedding.LinTwoAutCard
import CFSGOutside.Corpus.CardMulAutPsl2GF
import CFSGOutsideClean.Corpus.Defs.OddCoreDihedral

/-! The corpus proves the statement that `CFSGOutside.Corpus.CardMulAutPsl2GF` assumes. -/

instance CFSGOutsideClean.Corpus.cardMulAutPsl2GF : CFSGOutside.Corpus.CardMulAutPsl2GF :=
  ⟨CFSG.AGLEmbedding.card_mulAut_psl2GF⟩
