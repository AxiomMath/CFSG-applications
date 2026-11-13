import CFSGOutside.Corpus.Defs.GoldschmidtOddCore

/-!
# Corpus input: Goldschmidt's Theorem A on strongly closed 2-subgroups

Statement of `CFSG.Goldschmidt75.theoremA` (`CFSG/Goldschmidt75/TheoremA.lean`, line 42, at
AxiomMath/CFSG commit 69cb972f587a3ecc035e092253167ff2e303c962), with `fusionStronglyClosed` and
`goldschmidtOddCore` the copies in `CFSGOutside.Corpus.Defs.GoldschmidtOddCore`.

If `S₁ ≤ T₁` and `S₂ ≤ T₂` are strongly closed in Sylow 2-subgroups `T₁, T₂` of a finite group `G`,
commute and meet trivially, then their normal closures commute modulo `O(G)`
(D. Goldschmidt, *Strongly closed 2-subgroups of finite groups*, Ann. of Math. 102 (1975), Theorem A).
-/

namespace CFSGOutside.Corpus

open Subgroup

/-- Goldschmidt's Theorem A, as `CFSG.Goldschmidt75.theoremA` states it. -/
class GoldschmidtTheoremA : Prop where
  theoremA : ∀ {G : Type} [Group G] [Finite G] {S₁ S₂ : Subgroup G} (T₁ T₂ : Sylow 2 G),
    S₁ ≤ T₁ → S₂ ≤ T₂ → fusionStronglyClosed (S₁ : Set G) T₁ →
    fusionStronglyClosed (S₂ : Set G) T₂ → ⁅S₁, S₂⁆ = ⊥ → S₁ ⊓ S₂ = ⊥ →
    ⁅normalClosure (S₁ : Set G), normalClosure (S₂ : Set G)⁆ ≤ goldschmidtOddCore G

end CFSGOutside.Corpus
