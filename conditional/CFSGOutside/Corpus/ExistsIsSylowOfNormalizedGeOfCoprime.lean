import CFSGOutside.Corpus.Defs.ElemThompson

/-!
# Corpus input: an invariant `r`-subgroup lies in an invariant Sylow subgroup

Statement of `CFSG.ABGTheoremB.exists_isSylowOf_normalized_ge_of_coprime`, copied verbatim from
`CFSG/LocalAnalysis/ABGTheoremB/IV1.lean` (line 108, with the section variables of lines 15 to 19) at
AxiomMath/CFSG commit 69cb972f587a3ecc035e092253167ff2e303c962. `IsSylowOf` is the copy
`CFSGOutside.Corpus.ABGLocalTools.IsSylowOf` in `CFSGOutside.Corpus.Defs`.

If a `p`-group `A` normalizes a subgroup `K` of order prime to `p` and an `A`-invariant `r`-subgroup `P` of `K`,
then `P` lies in an `A`-invariant Sylow `r`-subgroup of `K`. The corpus theorem is universe polymorphic, so the
class takes the universe of `G` as a parameter. The clean build provides every instance, in
`clean/CFSGOutsideClean/Corpus/ExistsIsSylowOfNormalizedGeOfCoprime.lean`.
-/

namespace CFSGOutside.Corpus

open ABGLocalTools

/-- An invariant `r`-subgroup lies in an invariant Sylow `r`-subgroup, as
`CFSG.ABGTheoremB.exists_isSylowOf_normalized_ge_of_coprime` states it. -/
class ExistsIsSylowOfNormalizedGeOfCoprime.{u} : Prop where
  exists_isSylowOf_normalized_ge_of_coprime : ∀ {G : Type u} [Group G] [Finite G] {p r : ℕ}
    (_hp : p.Prime) (_hr : r.Prime) {A K P : Subgroup G} (_hA : IsPGroup p A)
    (_hAK : A ≤ Subgroup.normalizer (K : Set G)) (_hK : ¬ p ∣ Nat.card K) (_hPK : P ≤ K)
    (_hP : IsPGroup r P) (_hAP : A ≤ Subgroup.normalizer (P : Set G)),
    ∃ R : Subgroup G, IsSylowOf r R K ∧ P ≤ R ∧ A ≤ Subgroup.normalizer (R : Set G)

end CFSGOutside.Corpus
