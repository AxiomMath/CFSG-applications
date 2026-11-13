import CFSG.LieType.SuzukiSubgroups.Torus
import CFSGOutside.Corpus.EqTopOrLeNormalizerTorus

/-! The corpus proves the statement that `CFSGOutside.Corpus.EqTopOrLeNormalizerTorus` assumes. -/

instance CFSGOutsideClean.Corpus.eqTopOrLeNormalizerTorus :
    CFSGOutside.Corpus.EqTopOrLeNormalizerTorus :=
  ⟨by
    intro n H _ _ hH Q₁ Q₂ hne Y hK y hy hyQ
    exact CFSG.LieType.SuzukiSubgroups.eq_top_or_le_normalizer_torus hH hne hK hy hyQ⟩
