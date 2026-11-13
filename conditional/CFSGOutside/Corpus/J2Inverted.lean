import CFSGOutside.Corpus.Defs.Walter

/-!
# Corpus input: odd Sylow subgroups of `J₁` are inverted by involutions

Statement of `CFSG.Walter.J1Props.J2_inverted`, copied verbatim from `CFSG/Walter/J1Props/Facts.lean` (line 129)
at AxiomMath/CFSG commit 69cb972f587a3ecc035e092253167ff2e303c962. `walterJ1` is the copy
`CFSGOutside.Corpus.Open.walterJ1`.
-/

namespace CFSGOutside.Corpus

/-- Every Sylow `p`-subgroup of `J₁`, `p` odd, is inverted by an involution, as
`CFSG.Walter.J1Props.J2_inverted` states it. -/
class J2Inverted : Prop where
  J2_inverted : ∀ {p : ℕ} [Fact p.Prime] (_hp2 : p ≠ 2) (P : Sylow p Open.walterJ1),
    ∃ x : Open.walterJ1, orderOf x = 2 ∧ ∀ z ∈ (P : Subgroup Open.walterJ1), x * z * x⁻¹ = z⁻¹

end CFSGOutside.Corpus
