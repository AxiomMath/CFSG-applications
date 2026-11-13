import CFSGOutside.Corpus.Defs.OpenVocabulary

/-!
# Copied corpus definition: the 2-rank

Copied verbatim from AxiomMath/CFSG at commit 69cb972f587a3ecc035e092253167ff2e303c962, under
`CFSGOutside.Corpus`. The clean build proves the copy equal to the corpus original in
`clean/CFSGOutsideClean/Corpus/Defs/TwoRank.lean`.
-/

namespace CFSGOutside.Corpus.Open

/-- The 2-rank of a finite group: the largest `k` such that it has an elementary abelian 2-subgroup of order
`2 ^ k`. Copy of `CFSG.Open.twoRank`, `CFSG/Open/LocalVocabulary.lean` line 18. -/
noncomputable def twoRank (G : Type*) [Group G] [Finite G] : ℕ := pRank 2 (⊤ : Subgroup G)

end CFSGOutside.Corpus.Open
