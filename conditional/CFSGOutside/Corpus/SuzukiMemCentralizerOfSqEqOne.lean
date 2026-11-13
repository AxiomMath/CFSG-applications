import CFSGOutside.Corpus.Defs.Suzuki

/-!
# Corpus input: involutions of a Sylow `2`-subgroup of `Sz(q)` are central in it

Statement of `CFSG.RankThree.S4Free.Suzuki.mem_centralizer_of_sq_eq_one`, copied verbatim from
`CFSG/RankThree/S4Free/Stellmacher24Sz.lean` (line 104) at AxiomMath/CFSG commit 69cb972f587a3ecc035e092253167ff2e303c962, with
`suzukiGroup` the copy in `CFSGOutside.Corpus`.

The corpus theorem is universe polymorphic in `X`, so the class takes the universe as a parameter.
-/

universe u

namespace CFSGOutside.Corpus

/-- In a group `X ≅ Sz(q)`, every element of square `1` of a Sylow `2`-subgroup `S` centralizes `S`. -/
class SuzukiMemCentralizerOfSqEqOne : Prop where
  mem_centralizer_of_sq_eq_one : ∀ {a : ℕ} {K : Type} [Field K] [Finite K] {X : Type u} [Group X]
    (_hK : Nat.card K = 2 ^ (2 * a + 1)) (_e : X ≃* suzukiGroup a K) (S : Sylow 2 X) {z : X}
    (_hzS : z ∈ (S : Subgroup X)) (_hz : z ^ 2 = 1),
    z ∈ Subgroup.centralizer ((S : Subgroup X) : Set X)

end CFSGOutside.Corpus
