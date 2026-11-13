import CFSGOutside.Corpus.Defs.OuterAutomorphisms
import CFSGOutside.Corpus.Defs.Suzuki

/-!
# Corpus input: `Out(Sz(q))` has odd order

Statement of `CFSG.ProperTwoGeneratedCore.HighRankPair.suzuki_outer_automorphism_group_has_odd_order`, copied
verbatim from `CFSG/LocalAnalysis/ProperTwoGeneratedCore/SuzukiOuterOdd.lean` (line 118) at AxiomMath/CFSG
commit 69cb972f587a3ecc035e092253167ff2e303c962, with `Outer`, `inner` and `suzukiGroup` the copies in `CFSGOutside.Corpus`.
-/

namespace CFSGOutside.Corpus

open ComponentClassification.OuterAutomorphisms

/-- The outer automorphism group of `Sz(q)` has odd order, and every `2`-subgroup of `Aut(Sz(q))` consists of
inner automorphisms. -/
class SuzukiOuterAutomorphismGroupHasOddOrder : Prop where
  suzuki_outer_automorphism_group_has_odd_order : ∀ {a : ℕ} {K : Type} [Field K] (_ha : 1 ≤ a)
    (_hK : Nat.card K = 2 ^ (2 * a + 1)),
    Odd (Nat.card (Outer (suzukiGroup a K))) ∧
      ∀ P : Subgroup (MulAut (suzukiGroup a K)), IsPGroup 2 P → P ≤ inner (suzukiGroup a K)

end CFSGOutside.Corpus
