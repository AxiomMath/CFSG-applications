import Mathlib

/-!
# Copied corpus definitions: Frobenius groups and regular actions

Definitions copied verbatim from AxiomMath/CFSG at commit 69cb972f587a3ecc035e092253167ff2e303c962, under
`CFSGOutside.Corpus` so that `clean/`, which imports the corpus too, sees no clash. The clean build proves
each copy equal to its corpus original in `clean/CFSGOutsideClean/Corpus/Defs/Frobenius.lean`.
-/

namespace CFSGOutside.Corpus

namespace Subgroup

/-- The conjugate of a subgroup by an element. Copy of `Subgroup.conjBy`,
`CFSG/ThirdParty/QiuzhenCFSG/FeitThompson/BGsection3/Defs.lean` line 55. -/
def conjBy {G : Type*} [Group G] (H : _root_.Subgroup G) (g : G) : _root_.Subgroup G :=
  H.map (MulAut.conj g).toMonoidHom

/-- If `A ≤ normalizer K`, then `↥A` acts on `↥K` by conjugation inside `G`. Copy of
`Subgroup.conjMulDistribMulActionOfLeNormalizer`,
`CFSG/ThirdParty/QiuzhenCFSG/FeitThompson/SubgroupConjAction.lean` line 32. -/
@[reducible]
def conjMulDistribMulActionOfLeNormalizer {G : Type*} [Group G] (A K : _root_.Subgroup G)
    (hAK : A ≤ _root_.Subgroup.normalizer K) :
    MulDistribMulAction (↥A) (↥K) :=
  let smulFun : (↥A) → (↥K) → (↥K) :=
    fun a k =>
      ⟨(a : G) * (k : G) * (a : G)⁻¹,
        (_root_.Subgroup.mem_normalizer_iff.mp (hAK a.property) (k : G)).1 k.property⟩
  { smul := smulFun
    one_smul := by
      intro k
      change smulFun (1 : (↥A)) k = k
      apply Subtype.ext
      simp [smulFun]
    mul_smul := by
      intro a b k
      change smulFun (a * b) k = smulFun a (smulFun b k)
      apply Subtype.ext
      simp [smulFun, mul_assoc]
    smul_mul := by
      intro a x y
      change smulFun a (x * y) = smulFun a x * smulFun a y
      apply Subtype.ext
      simp [smulFun, mul_assoc]
    smul_one := by
      intro a
      change smulFun a (1 : (↥K)) = 1
      apply Subtype.ext
      simp [smulFun] }

end Subgroup

/-- A Frobenius group with kernel `K` and complement `R`. Copy of
`CFSG.IsFrobeniusGroupWithKernelComplement`,
`CFSG/ThirdParty/QiuzhenCFSG/FeitThompson/BGsection3/Defs.lean` line 91. -/
def IsFrobeniusGroupWithKernelComplement {G : Type*} [Group G]
    (K R : _root_.Subgroup G) : Prop :=
  K.Normal ∧ K.IsComplement' R ∧
    (∀ g : G, g ∉ R → Disjoint R (Subgroup.conjBy R g)) ∧
      K ≠ ⊥ ∧ R ≠ ⊥

/-- Copy of `CFSG.IsFrobeniusGroupWithKernelComplement.normal`,
`CFSG/ThirdParty/QiuzhenCFSG/FeitThompson/BGsection3/Defs.lean` line 97. -/
theorem IsFrobeniusGroupWithKernelComplement.normal {G : Type*} [Group G]
    {K R : _root_.Subgroup G} (hfrob : IsFrobeniusGroupWithKernelComplement K R) :
    K.Normal :=
  hfrob.1

/-- `C_G(A)`: the subgroup of elements of `G` fixed by the `A`-action. Copy of
`CFSG.fixedPointSubgroup`, `CFSG/ThirdParty/QiuzhenCFSG/FeitThompson/GroupAction/Defs.lean` line 25. -/
abbrev fixedPointSubgroup (A : Type*) (G : Type*) [Group A] [Group G] [MulDistribMulAction A G] :
    _root_.Subgroup G :=
  FixedPoints.subgroup A G

/-- An action is regular if every nonidentity actor has trivial fixed-point subgroup. Copy of
`CFSG.ActsRegularly`, `CFSG/ThirdParty/QiuzhenCFSG/FeitThompson/BGsection3/Defs.lean` line 214. -/
def ActsRegularly (A G : Type*) [Group A] [Group G]
    [MulDistribMulAction A G] : Prop :=
  ∀ a : A, a ≠ 1 → fixedPointSubgroup (↥(_root_.Subgroup.zpowers a)) G = ⊥

end CFSGOutside.Corpus
