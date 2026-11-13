import CFSG.Goldschmidt75.TheoremA
import CFSGOutside.Corpus.GoldschmidtTheoremA

/-! The corpus proves the statement that `CFSGOutside.Corpus.GoldschmidtTheoremA` assumes. -/

instance CFSGOutsideClean.Corpus.goldschmidtTheoremA : CFSGOutside.Corpus.GoldschmidtTheoremA :=
  ⟨fun T₁ T₂ h₁ h₂ hS₁ hS₂ hcomm hdisj =>
    CFSG.Goldschmidt75.theoremA T₁ T₂ h₁ h₂ hS₁ hS₂ hcomm hdisj⟩
