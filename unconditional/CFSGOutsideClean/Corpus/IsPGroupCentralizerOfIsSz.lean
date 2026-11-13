import CFSG.LieType.SuzukiSubgroups.Facts
import CFSGOutside.Corpus.IsPGroupCentralizerOfIsSz

/-! The corpus proves the statement that `CFSGOutside.Corpus.IsPGroupCentralizerOfIsSz` assumes. -/

instance CFSGOutsideClean.Corpus.isPGroupCentralizerOfIsSz :
    CFSGOutside.Corpus.IsPGroupCentralizerOfIsSz :=
  ⟨by
    intro n H _ hH x hx
    exact CFSG.LieType.SuzukiSubgroups.isPGroup_centralizer_of_isSz hH hx⟩
