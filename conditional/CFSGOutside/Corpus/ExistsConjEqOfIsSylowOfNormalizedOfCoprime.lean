import CFSGOutside.Corpus.Defs.ElemThompson

/-!
# Corpus input: invariant Sylow subgroups are conjugate under the centralizer of the acting group

Statement of `CFSG.ABGTheoremB.exists_conj_eq_of_isSylowOf_normalized_of_coprime`, copied verbatim from
`CFSG/LocalAnalysis/ABGTheoremB/IV1.lean` (line 126, with the section variables of lines 15 to 19) at
AxiomMath/CFSG commit 69cb972f587a3ecc035e092253167ff2e303c962. `IsSylowOf` is the copy
`CFSGOutside.Corpus.ABGLocalTools.IsSylowOf` in `CFSGOutside.Corpus.Defs`.

If a `p`-group `A` normalizes a subgroup `K` of order prime to `p`, two `A`-invariant Sylow `r`-subgroups of `K`
are conjugate by an element of `C_K(A)`. The corpus theorem is universe polymorphic, so the class takes the
universe of `G` as a parameter. The clean build provides every instance, in
`clean/CFSGOutsideClean/Corpus/ExistsConjEqOfIsSylowOfNormalizedOfCoprime.lean`.
-/

namespace CFSGOutside.Corpus

open ABGLocalTools

/-- Invariant Sylow subgroups are conjugate by an element of `C_K(A)`, as
`CFSG.ABGTheoremB.exists_conj_eq_of_isSylowOf_normalized_of_coprime` states it. -/
class ExistsConjEqOfIsSylowOfNormalizedOfCoprime.{u} : Prop where
  exists_conj_eq_of_isSylowOf_normalized_of_coprime : ∀ {G : Type u} [Group G] [Finite G]
    {p r : ℕ} (_hp : p.Prime) (_hr : r.Prime) {A K R₁ R₂ : Subgroup G} (_hA : IsPGroup p A)
    (_hAK : A ≤ Subgroup.normalizer (K : Set G)) (_hK : ¬ p ∣ Nat.card K)
    (_hR₁ : IsSylowOf r R₁ K) (_hR₂ : IsSylowOf r R₂ K)
    (_hAR₁ : A ≤ Subgroup.normalizer (R₁ : Set G)) (_hAR₂ : A ≤ Subgroup.normalizer (R₂ : Set G)),
    ∃ c ∈ K ⊓ Subgroup.centralizer (A : Set G), R₁.map (MulAut.conj c).toMonoidHom = R₂

end CFSGOutside.Corpus
