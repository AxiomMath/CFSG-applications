import CFSGOutside.Corpus.Defs.OuterAutomorphisms

/-!
# Perfect groups act on groups with solvable outer automorphism group by inner automorphisms

Mathlib-only proofs of two short corpus lemmas, with their statements copied:
`CFSG.ComponentClassification.SolvableKernelContainment.hom_eq_one`
(`CFSG/LocalAnalysis/ComponentClassification/SolvableKernelContainment.lean`, line 61) and
`CFSG.ComponentClassification.OuterAutomorphisms.perfect_action_inner`
(`CFSG/LocalAnalysis/ComponentClassification/OuterAutomorphisms.lean`, line 125), at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962. `Outer` is the copy in `CFSGOutside.Corpus`.
-/

namespace CFSGOutside.Robinson

open CFSGOutside.Corpus.ComponentClassification.OuterAutomorphisms

theorem perfect_solvable_subsingleton {G : Type*} [Group G]
    [Group.IsPerfect G] [Group.IsSolvable G] : Subsingleton G := by
  rcases subsingleton_or_nontrivial G with hsubsingleton | hnontrivial
  · exact hsubsingleton
  · exact (Group.IsPerfect.not_isSolvable G inferInstance).elim

/-- A homomorphism from a perfect group to a solvable group is trivial. -/
theorem hom_eq_one {G H : Type*} [Group G] [Group H]
    [Group.IsPerfect G] [Group.IsSolvable H] (homomorphism : G →* H) : homomorphism = 1 := by
  let : Group.IsPerfect homomorphism.range := Group.IsPerfect.range homomorphism
  have hsubsingleton : Subsingleton homomorphism.range := perfect_solvable_subsingleton
  apply MonoidHom.ext
  intro element
  exact congrArg Subtype.val
    (hsubsingleton.elim (⟨homomorphism element, ⟨element, rfl⟩⟩ : homomorphism.range) 1)

/-- A perfect group acting on a group with solvable outer automorphism group acts by inner
automorphisms. -/
theorem perfect_action_inner {A G : Type*} [Group A] [Group.IsPerfect A] [Group G]
    [Group.IsSolvable (Outer G)] (action : A →* MulAut G) (actor : A) :
    ∃ element : G, action actor = MulAut.conj element := by
  have htrivial := hom_eq_one ((QuotientGroup.mk' (inner G)).comp action)
  have hone := congrArg (fun homomorphism : A →* Outer G => homomorphism actor) htrivial
  have hinner : action actor ∈ inner G := (QuotientGroup.eq_one_iff _).mp hone
  obtain ⟨element, heq⟩ := hinner
  exact ⟨element, heq.symm⟩

end CFSGOutside.Robinson
