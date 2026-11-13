import CFSG.Quasithin.Vol2.Ch3Sec3InspWalterHolds
import CFSGOutside.Corpus.WalterSplit
import CFSGOutsideClean.Corpus.Defs.J1Models
import CFSGOutsideClean.Corpus.Defs.ReeModel

/-! The corpus proves the statement that `CFSGOutside.Corpus.WalterSplit` assumes. -/

instance CFSGOutsideClean.Corpus.walterSplit : CFSGOutside.Corpus.WalterSplit :=
  ⟨fun G _ _ _ hnonab P hP => by
    rcases CFSG.Quasithin.H13.S3320.walter_split G hnonab P hP with h | h | ⟨f, hf, hf3, hR⟩ | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl ⟨f, hf, hf3,
        (CFSGOutsideClean.Corpus.reeTitsModel_twistedG2_iff 3 f).2 hR⟩))
    · exact Or.inr (Or.inr (Or.inr h))⟩
