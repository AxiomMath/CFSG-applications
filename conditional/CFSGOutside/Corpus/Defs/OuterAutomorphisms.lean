import Mathlib

/-!
# Copied corpus definitions: outer automorphism groups

Verbatim copies, under `CFSGOutside.Corpus`, of definitions in
`CFSG/LocalAnalysis/ComponentClassification/OuterAutomorphisms.lean` (lines 14–30) at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962. `clean/CFSGOutsideClean/Corpus/Defs/OuterAutomorphisms.lean` shows
each copy equals its original.
-/

namespace CFSGOutside.Corpus.ComponentClassification.OuterAutomorphisms

/-- Inner automorphisms, `CFSG.ComponentClassification.OuterAutomorphisms.inner`. -/
noncomputable def inner (G : Type*) [Group G] : Subgroup (MulAut G) :=
  (MulAut.conj : G →* MulAut G).range

theorem inner_normal (G : Type*) [Group G] : (inner G).Normal := by
  constructor
  intro automorphism hautomorphism conjugator
  obtain ⟨element, rfl⟩ := hautomorphism
  refine ⟨conjugator element, ?_⟩
  apply MulEquiv.ext
  intro member
  change conjugator element * member * (conjugator element)⁻¹ =
    conjugator (element * conjugator.symm member * element⁻¹)
  rw [map_mul, map_mul, map_inv, conjugator.apply_symm_apply]

noncomputable instance innerNormal (G : Type*) [Group G] : (inner G).Normal :=
  inner_normal G

/-- The outer automorphism group, `CFSG.ComponentClassification.OuterAutomorphisms.Outer`. -/
noncomputable abbrev Outer (G : Type*) [Group G] := MulAut G ⧸ inner G

end CFSGOutside.Corpus.ComponentClassification.OuterAutomorphisms
