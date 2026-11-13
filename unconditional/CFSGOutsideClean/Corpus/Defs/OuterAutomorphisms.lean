import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSGOutside.Corpus.Defs.OuterAutomorphisms

/-! The copied outer automorphism definitions are the corpus definitions. -/

namespace CFSGOutsideClean.Corpus.ComponentClassification.OuterAutomorphisms

theorem inner_eq (G : Type*) [Group G] :
    CFSGOutside.Corpus.ComponentClassification.OuterAutomorphisms.inner G =
      CFSG.ComponentClassification.OuterAutomorphisms.inner G :=
  rfl

/-- Solvability of the copied outer automorphism group is solvability of the corpus one. -/
theorem isSolvable_outer_iff (G : Type*) [Group G] :
    Group.IsSolvable (CFSGOutside.Corpus.ComponentClassification.OuterAutomorphisms.Outer G) ↔
      Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer G) :=
  Iff.rfl

end CFSGOutsideClean.Corpus.ComponentClassification.OuterAutomorphisms
