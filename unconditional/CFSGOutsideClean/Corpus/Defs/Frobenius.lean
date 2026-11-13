import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Defs
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Defs
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction
import CFSGOutside.Corpus.Defs.Frobenius

/-! The definitions copied into `CFSGOutside.Corpus.Defs.Frobenius` are the corpus definitions. -/

namespace CFSGOutsideClean.Corpus

theorem conjBy_eq {G : Type*} [Group G] (H : Subgroup G) (g : G) :
    CFSGOutside.Corpus.Subgroup.conjBy H g = H.conjBy g :=
  rfl

theorem conjMulDistribMulActionOfLeNormalizer_eq {G : Type*} [Group G] (A K : Subgroup G)
    (hAK : A ≤ Subgroup.normalizer K) :
    CFSGOutside.Corpus.Subgroup.conjMulDistribMulActionOfLeNormalizer A K hAK =
      Subgroup.conjMulDistribMulActionOfLeNormalizer A K hAK :=
  rfl

theorem isFrobeniusGroupWithKernelComplement_iff {G : Type*} [Group G] (K R : Subgroup G) :
    CFSGOutside.Corpus.IsFrobeniusGroupWithKernelComplement K R ↔
      CFSG.IsFrobeniusGroupWithKernelComplement K R :=
  Iff.rfl

theorem fixedPointSubgroup_eq (A G : Type*) [Group A] [Group G] [MulDistribMulAction A G] :
    CFSGOutside.Corpus.fixedPointSubgroup A G = CFSG.fixedPointSubgroup A G :=
  rfl

theorem actsRegularly_iff (A G : Type*) [Group A] [Group G] [MulDistribMulAction A G] :
    CFSGOutside.Corpus.ActsRegularly A G ↔ CFSG.ActsRegularly A G :=
  Iff.rfl

end CFSGOutsideClean.Corpus
