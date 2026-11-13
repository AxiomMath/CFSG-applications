import CFSGOutside.Corpus.Defs.LieOrder

/-!
# Corpus input: Artin's estimate for the order of a group of Lie type in odd characteristic

Statement of `CFSG.ComponentClassification.GS82PumpInputs.OddChar.ordProj_le_of_mul_eq`
(`CFSG/LocalAnalysis/ComponentClassification/GS82PumpOddChar.lean`, line 29, at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962), copied verbatim. `StatedLieTag`, `StatedLieAdmissible`,
`lieOrderDivisor`, `lieOrderNumerator` and `lieSylowExponent` are the copies in
`CFSGOutside.Corpus.Defs.ReeModel` and `CFSGOutside.Corpus.Defs.LieOrder`.
-/

namespace CFSGOutside.Corpus

open Open ComponentClassification.CatLeaf

/-- If `M · D = q ^ N · C` is the order formula of an admissible tuple `(t, n, p, f)` with `p` odd and
`q = p ^ f`, then for every odd prime `s ≠ p` the `s`-part of `M` is at most `q ^ N`. -/
class OrdProjLeOfMulEq : Prop where
  ordProj_le_of_mul_eq : ∀ {t : StatedLieTag} {n p f M : ℕ}
    (_hadm : StatedLieAdmissible t n p f) (_hp2 : p ≠ 2)
    (_hM : M * lieOrderDivisor t n (p ^ f) = lieOrderNumerator t n (p ^ f)) {s : ℕ}
    (_hs : s.Prime) (_hs2 : s ≠ 2) (_hsp : s ≠ p),
    ordProj[s] M ≤ (p ^ f) ^ lieSylowExponent t n

end CFSGOutside.Corpus
