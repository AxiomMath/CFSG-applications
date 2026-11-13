import Mathlib

/-!
# Copied corpus definitions: semidihedral and wreathed 2-groups, at most one involution

Copied verbatim from AxiomMath/CFSG commit 69cb972f587a3ecc035e092253167ff2e303c962, under `CFSGOutside.Corpus`:
`Open.semidihedralRels`, `Open.SemidihedralGroup`, `Open.WreathedTwoGroup` from `CFSG/Open/Catalog.lean`, and
`AtMostOneInvolution` from `CFSG/LocalAnalysis/ComponentClassification/AschbacherToolkitTwoGroupShapes.lean`.
-/

namespace CFSGOutside.Corpus

namespace Open

/-- Copy of `CFSG.Open.semidihedralRels`, `CFSG/Open/Catalog.lean` line 41. -/
def semidihedralRels (n : ℕ) : Set (FreeGroup (Fin 2)) :=
  {FreeGroup.of 0 ^ (2 ^ (n - 1)), FreeGroup.of 1 ^ 2,
    FreeGroup.of 1 * FreeGroup.of 0 * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0 ^ (2 ^ (n - 2) - 1))⁻¹}

/-- Copy of `CFSG.Open.SemidihedralGroup`, `CFSG/Open/Catalog.lean` line 45. -/
abbrev SemidihedralGroup (n : ℕ) : Type := PresentedGroup (semidihedralRels n)

/-- Copy of `CFSG.Open.WreathedTwoGroup`, `CFSG/Open/Catalog.lean` line 47. -/
abbrev WreathedTwoGroup (n : ℕ) : Type :=
  Multiplicative (ZMod (2 ^ n)) ≀ᵣ Multiplicative (ZMod 2)

end Open

/-- Copy of `CFSG.ComponentClassification.AschbacherToolkit.AtMostOneInvolution`,
`CFSG/LocalAnalysis/ComponentClassification/AschbacherToolkitTwoGroupShapes.lean` line 15. -/
def AtMostOneInvolution (P : Type*) [Group P] : Prop :=
  ∀ s t : P, orderOf s = 2 → orderOf t = 2 → s = t

end CFSGOutside.Corpus
