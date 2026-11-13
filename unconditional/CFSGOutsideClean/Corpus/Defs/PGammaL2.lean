import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2
import CFSGOutside.Corpus.Defs.PGammaL2

/-! The definitions copied into `CFSGOutside.Corpus.Defs.PGammaL2` are the corpus definitions. -/

universe u

namespace CFSGOutsideClean.Corpus

theorem pgl2RingEquiv_eq {R : Type u} [CommRing R] (e : R ≃+* R) :
    CFSGOutside.Corpus.GorensteinWalter.pgl2RingEquiv e = CFSG.GorensteinWalter.pgl2RingEquiv e :=
  rfl

theorem pgl2FieldAut_eq (K : Type u) [CommRing K] :
    CFSGOutside.Corpus.GorensteinWalter.pgl2FieldAut K = CFSG.GorensteinWalter.pgl2FieldAut K :=
  rfl

theorem pGammaL2_eq (K : Type u) [CommRing K] :
    CFSGOutside.Corpus.GorensteinWalter.PGammaL2 K = CFSG.GorensteinWalter.PGammaL2 K :=
  rfl

end CFSGOutsideClean.Corpus
