import CFSGOutside.Corpus.Defs.Suzuki

/-!
# Corpus input: subgroups of `Sz(q)` containing a torus and a swapping element

Statement of `CFSG.LieType.SuzukiSubgroups.eq_top_or_le_normalizer_torus`, copied verbatim from
`CFSG/LieType/SuzukiSubgroups/Torus.lean` (line 737) at AxiomMath/CFSG commit 69cb972f587a3ecc035e092253167ff2e303c962, with `IsSz` the copy
in `CFSGOutside.Corpus`.
-/

namespace CFSGOutside.Corpus

/-- A subgroup `Y` of `H ≅ Sz(q)` containing the torus `N(Q₁) ∩ N(Q₂)` and an element swapping `Q₁` into `Q₂`
is everything or lies in the normalizer of the torus. -/
class EqTopOrLeNormalizerTorus : Prop where
  eq_top_or_le_normalizer_torus : ∀ {n : ℕ} {H : Type} [Group H] [Finite H]
    (_hH : IsSz n H) {Q₁ Q₂ : Sylow 2 H} (_hne : Q₁ ≠ Q₂) {Y : Subgroup H}
    (_hK : Subgroup.normalizer ((Q₁ : Subgroup H) : Set H) ⊓
      Subgroup.normalizer ((Q₂ : Subgroup H) : Set H) ≤ Y)
    {y : H} (_hy : y ∈ Y) (_hyQ : y • Q₁ = Q₂),
    Y = ⊤ ∨ Y ≤ Subgroup.normalizer ((Subgroup.normalizer ((Q₁ : Subgroup H) : Set H) ⊓
      Subgroup.normalizer ((Q₂ : Subgroup H) : Set H) : Subgroup H) : Set H)

end CFSGOutside.Corpus
