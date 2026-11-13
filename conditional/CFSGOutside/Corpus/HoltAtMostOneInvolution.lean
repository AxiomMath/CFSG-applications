import CFSGOutside.Corpus.Defs.TwoGroupShapes

/-!
# Corpus input: 2-groups with at most one involution

Statement of `CFSG.Holt.isCyclic_or_quaternion_of_atMostOneInvolution`
(`CFSG/Holt/TwoGroups.lean`, line 59, at AxiomMath/CFSG commit 69cb972f587a3ecc035e092253167ff2e303c962), in
the section with `variable {P : Type*} [Group P] [Finite P]`. The corpus theorem is universe polymorphic, so the
class takes the universe as a parameter. `AtMostOneInvolution` is the copy in
`CFSGOutside.Corpus.Defs.TwoGroupShapes`.
-/

universe u

namespace CFSGOutside.Corpus

/-- A finite 2-group with at most one involution is cyclic or generalized quaternion. -/
class HoltAtMostOneInvolution : Prop where
  isCyclic_or_quaternion_of_atMostOneInvolution : ∀ {P : Type u} [Group P] [Finite P]
    (_hP : IsPGroup 2 P) (_h : AtMostOneInvolution P),
    IsCyclic P ∨ ∃ n : ℕ, 3 ≤ n ∧ Nonempty (P ≃* QuaternionGroup (2 ^ (n - 2)))

end CFSGOutside.Corpus
