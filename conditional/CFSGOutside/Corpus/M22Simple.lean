import CFSGOutside.Corpus.Defs.WittDesign

/-!
# Corpus input: `M22` is finite, nontrivial and simple

Statement of `CFSG.Sporadic.Mathieu.fam_m22_simplicity`, copied verbatim from `CFSG/Sporadic/Mathieu/M22.lean`
(line 44) at AxiomMath/CFSG commit 69cb972f587a3ecc035e092253167ff2e303c962, with `NativeSporadic.M22` the copy in
`CFSGOutside.Corpus.Defs.WittDesign`. The clean build provides the instance, in
`results_unconditional/CFSGOutsideClean/Corpus/M22Simple.lean`.
-/

namespace CFSGOutside.Corpus

/-- `M22` is finite, nontrivial and simple, as `fam_m22_simplicity` states it. -/
class M22Simple : Prop where
  fam_m22_simplicity :
    Finite NativeSporadic.M22 ∧ Nontrivial NativeSporadic.M22 ∧ IsSimpleGroup NativeSporadic.M22

end CFSGOutside.Corpus
