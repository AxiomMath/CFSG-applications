import CFSGOutside.Corpus.Defs.NativeM11
import CFSGOutside.Corpus.Defs.LowTwoRankCatalog

/-!
# Corpus input: `M₁₁` has only inner automorphisms

* `CFSG.ClassicalInvolution.Q3.Q3NM.m11_aut_inner`, copied verbatim from `CFSG/ClassicalInvolution/Q3/Q3NMM11.lean`
  (line 24) at AxiomMath/CFSG commit 69cb972f587a3ecc035e092253167ff2e303c962;
* the corpus isomorphism `CFSG.EvenSporadicStandard.HNRecog.Section3Model.nativeEquivOpen :
  ↥NativeSporadic.M11 ≃* ↥CFSG.Open.M11` (`CFSG/LocalAnalysis/EvenSporadicStandard/HNRecog/Section3Model/M11Final.lean`
  line 18), recorded as `Nonempty`.

`NativeSporadic.M11` and `Open.M11` are the copies in `CFSGOutside.Corpus.Defs`.
-/

namespace CFSGOutside.Corpus

/-- Every automorphism of the native `M₁₁` is inner. -/
class M11AutInner : Prop where
  m11_aut_inner : ∀ (φ : MulAut ↥Blueprint.NativeSporadic.M11),
    ∃ k : ↥Blueprint.NativeSporadic.M11, φ = MulAut.conj k

/-- The native and catalogue models of `M₁₁` are isomorphic. -/
class NativeM11EquivOpen : Prop where
  nativeEquivOpen : Nonempty (↥Blueprint.NativeSporadic.M11 ≃* ↥Open.M11)

end CFSGOutside.Corpus
