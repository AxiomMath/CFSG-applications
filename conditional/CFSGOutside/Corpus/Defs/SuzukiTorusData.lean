import Mathlib

/-!
# Copied corpus definition: the Suzuki point and torus axioms

`CFSGOutside.Corpus.SuzukiTorusData` is `CFSG.GroupTheory.SuzukiTorusData`, copied verbatim from
`CFSG/GroupTheory/SuzukiPointTorus/Basic.lean` (line 14) at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962. `clean/CFSGOutsideClean/Corpus/Defs/SuzukiTorusData.lean`
shows it is equivalent to the corpus structure.
-/

namespace CFSGOutside.Corpus

/-- The Suzuki point/torus axioms Z1–Z4 for a finite group `X` and `q`, `CFSG.GroupTheory.SuzukiTorusData`. -/
structure SuzukiTorusData (X : Type*) [Group X] [Finite X] (q : ℕ) : Prop where
  faithful : FaithfulSMul X (Sylow 2 X)
  card_points : Nat.card (Sylow 2 X) = q ^ 2 + 1
  fixes_le_two : ∀ g : X, g ≠ 1 → Nat.card {P : Sylow 2 X // g • P = P} ≤ 2
  card_sylow : ∀ U : Sylow 2 X, Nat.card U = q ^ 2
  regular : ∀ U V W : Sylow 2 X, V ≠ U → W ≠ U →
    ∃! u : U, (u : X) • V = W
  inf_normalizer_isCyclic : ∀ U U' : Sylow 2 X, U ≠ U' → IsCyclic
    ↥(Subgroup.normalizer ((U : Subgroup X) : Set X) ⊓
      Subgroup.normalizer ((U' : Subgroup X) : Set X))
  inf_normalizer_card : ∀ U U' : Sylow 2 X, U ≠ U' →
    Nat.card ↥(Subgroup.normalizer ((U : Subgroup X) : Set X) ⊓
      Subgroup.normalizer ((U' : Subgroup X) : Set X)) = q - 1
  inf_normalizer_free : ∀ (U U' : Sylow 2 X), U ≠ U' →
    ∀ h ∈ Subgroup.normalizer ((U : Subgroup X) : Set X) ⊓
        Subgroup.normalizer ((U' : Subgroup X) : Set X),
      h ≠ 1 → ∀ u : U, (h : X) * (u : X) * (h : X)⁻¹ = (u : X) → u = 1
  card_frattini : ∀ U : Sylow 2 X, Nat.card (↥U ⧸ frattini ↥U) = q

end CFSGOutside.Corpus
