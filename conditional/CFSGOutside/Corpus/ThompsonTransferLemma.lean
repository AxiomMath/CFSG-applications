import CFSGOutside.Corpus.Defs.PResidual

/-!
# Corpus input: Thompson's transfer lemma

Statement of `CFSG.Quasithin.thompson_transfer_lemma`, copied verbatim from
`CFSG/Quasithin/Background/A1cTransfer.lean` (line 250) at AxiomMath/CFSG commit 69cb972f587a3ecc035e092253167ff2e303c962. `pResidual` is the copy in
`CFSGOutside.Corpus.Defs.PResidual`. The class takes the universe as a parameter.
-/

namespace CFSGOutside.Corpus

/-- Thompson transfer: an involution not conjugate into an index-2 subgroup of a Sylow 2-subgroup lies outside the
2-residual. -/
class ThompsonTransferLemma.{u} : Prop where
  thompson_transfer_lemma : ∀ {X : Type u} [Group X] [Finite X] (P : Sylow 2 X) {Q : Subgroup X}
    (_hQP : Q ≤ P) (_hindex : Q.relIndex (P : Subgroup X) = 2) {u : X} (_hu : orderOf u = 2)
    (_hQu : ∀ x : X, x⁻¹ * u * x ∉ Q), u ∉ Quasithin.pResidual 2 X

end CFSGOutside.Corpus
