import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Defs
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
import CFSGOutside.Corpus.Defs.DGroup

/-! The definitions copied into `CFSGOutside.Corpus.PPrimeCore` and `CFSGOutside.Corpus.Defs.DGroup` are the
corpus definitions. `IsDGroup` is an inductive, so the copy is matched constructor by constructor. -/

universe u

namespace CFSGOutsideClean.Corpus

theorem pPrimeCore_eq (p : ℕ) (G : Type*) [Group G] :
    CFSGOutside.Corpus.pPrimeCore p G = CFSG.pPrimeCore p G :=
  rfl

theorem hasCyclicOrDihedralSylowTwo_iff (G : Type u) [Group G] :
    CFSGOutside.Corpus.GorensteinWalter.HasCyclicOrDihedralSylowTwo G ↔
      CFSG.GorensteinWalter.HasCyclicOrDihedralSylowTwo G :=
  Iff.rfl

theorem pgl2_eq (K : Type u) [CommRing K] :
    CFSGOutside.Corpus.GorensteinWalter.PGL2 K = CFSG.GorensteinWalter.PGL2 K :=
  rfl

theorem isDGroup_iff (G : Type u) [Group G] [Finite G] :
    CFSGOutside.Corpus.GorensteinWalter.IsDGroup G ↔ CFSG.GorensteinWalter.IsDGroup G := by
  constructor
  · intro h
    cases h with
    | quotientIsTwoGroup hS h => exact .quotientIsTwoGroup hS h
    | quotientIsASeven hS e => exact .quotientIsASeven hS e
    | quotientHasLinearNormalSubgroup hS K hK L hL hi hm =>
        exact .quotientHasLinearNormalSubgroup hS K hK L hL hi hm
  · intro h
    cases h with
    | quotientIsTwoGroup hS h => exact .quotientIsTwoGroup hS h
    | quotientIsASeven hS e => exact .quotientIsASeven hS e
    | quotientHasLinearNormalSubgroup hS K hK L hL hi hm =>
        exact .quotientHasLinearNormalSubgroup hS K hK L hL hi hm

end CFSGOutsideClean.Corpus
