import CFSGOutside.Corpus.Defs.OpenVocabulary

/-!
# Corpus input: coprime automorphisms of simple catalogue groups have `p`-rank at most one

Statement of `CFSG.HardMathSupport.Solomon.Coordinator.i_7_13_1_pPrime_holds`, copied verbatim from
`CFSG/HardMathSupport/Solomon/Coordinator/I713.lean` (line 41) at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962. `I_7_13_1_pPrime` is the copy in `CFSGOutside.Corpus.Defs`.

For an odd prime `p` not dividing the order of a nonabelian simple catalogue group `K`, the `p`-rank of
`Aut K` is at most one. The clean build provides the instance, in
`clean/CFSGOutsideClean/Corpus/I713PPrimeHolds.lean`.
-/

namespace CFSGOutside.Corpus

/-- `m_p(Aut K) ≤ 1` for coprime odd `p`, as `i_7_13_1_pPrime_holds` states it. -/
class I713PPrimeHolds : Prop where
  i_7_13_1_pPrime_holds : I_7_13_1_pPrime

end CFSGOutside.Corpus
