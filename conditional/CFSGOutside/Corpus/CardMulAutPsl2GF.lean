import CFSGOutside.Corpus.Defs.OddCoreDihedral

/-!
# Corpus input: the order of `Aut(PSL(2, p^n))`

Statement of `CFSG.AGLEmbedding.card_mulAut_psl2GF` (`CFSG/LocalAnalysis/AGLEmbedding/LinTwoAutCard.lean`,
line 13, at AxiomMath/CFSG commit 69cb972f587a3ecc035e092253167ff2e303c962), copied verbatim, with `PSL2GF` the
copy in `CFSGOutside.Corpus.Defs.OddCoreDihedral`.
-/

namespace CFSGOutside.Corpus

open AGLEmbedding

/-- `card_mulAut_psl2GF`. -/
class CardMulAutPsl2GF : Prop where
  card_mulAut_psl2GF : ∀ (p n : ℕ) [Fact p.Prime] (_hn : 1 ≤ n),
    Nat.card (MulAut (PSL2GF p n)) = p ^ n * ((p ^ n) ^ 2 - 1) * n

end CFSGOutside.Corpus
