import CFSG.LieType.Steinberg.Classical.SpecialLinearSteinberg
import CFSGOutside.Corpus.ExistsSteinbergSLRelsEquiv
import CFSGOutsideClean.Corpus.Defs.SteinbergPresentation

/-! The corpus proves the statement that `CFSGOutside.Corpus.ExistsSteinbergSLRelsEquiv` assumes. -/

instance CFSGOutsideClean.Corpus.existsSteinbergSLRelsEquiv :
    CFSGOutside.Corpus.ExistsSteinbergSLRelsEquiv :=
  ⟨fun hm => CFSG.LieType.Steinberg.SL.exists_steinbergSLRels_equiv hm⟩
