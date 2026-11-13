import Mathlib

/-!
# Copied corpus definitions: normal `p`-complements, automorphisms of quotients

Copied verbatim from AxiomMath/CFSG at commit 69cb972f587a3ecc035e092253167ff2e303c962, under
`CFSGOutside.Corpus`:

* `CFSG.GroupTheory.IsNormalPComplement` (`CFSG/GroupTheory/FrobeniusNormalComplement.lean`, line 14);
* `CFSG.OrderReductions.FrattiniAutomorphisms.quotientEquivalence` and `.quotientAutomorphism`
  (`CFSG/Assembly/OrderReductions/FrattiniAutomorphisms.lean`, lines 31 and 45; the short proofs are the corpus
  ones).
-/

namespace CFSGOutside.Corpus

namespace GroupTheory

variable {G : Type*} [Group G]

/-- `N` is a normal `p`-complement: normal, of order prime to `p`, of `p`-power index. Copy of
`CFSG.GroupTheory.IsNormalPComplement`. -/
def IsNormalPComplement (p : ℕ) (N : Subgroup G) : Prop :=
  N.Normal ∧ Nat.Coprime (Nat.card N) p ∧ ∃ k : ℕ, N.index = p ^ k

end GroupTheory

namespace OrderReductions.FrattiniAutomorphisms

/-- The automorphism of `group ⧸ subgroup` induced by an automorphism of `group`. Copy of
`CFSG.OrderReductions.FrattiniAutomorphisms.quotientEquivalence`. -/
def quotientEquivalence {group : Type*} [Group group]
    (subgroup : Subgroup group) [subgroup.Characteristic] (automorphism : MulAut group) :
    MulAut (group ⧸ subgroup) :=
  QuotientGroup.congr subgroup subgroup automorphism
    (Subgroup.characteristic_iff_map_eq.mp inferInstance automorphism)

theorem quotientEquivalence_apply {group : Type*} [Group group]
    (subgroup : Subgroup group) [subgroup.Characteristic]
    (automorphism : MulAut group) (element : group) :
    quotientEquivalence subgroup automorphism (QuotientGroup.mk' subgroup element) =
      QuotientGroup.mk' subgroup (automorphism element) :=
  QuotientGroup.congr_mk' subgroup subgroup automorphism
    (Subgroup.characteristic_iff_map_eq.mp inferInstance automorphism) element

/-- `Aut(group) → Aut(group ⧸ subgroup)` for a characteristic subgroup. Copy of
`CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism`. -/
def quotientAutomorphism {group : Type*} [Group group]
    (subgroup : Subgroup group) [subgroup.Characteristic] :
    MulAut group →* MulAut (group ⧸ subgroup) where
  toFun := quotientEquivalence subgroup
  map_one' := by
    ext element
    obtain ⟨original, rfl⟩ := QuotientGroup.mk'_surjective subgroup element
    change quotientEquivalence subgroup (1 : MulAut group)
      (QuotientGroup.mk' subgroup original) = QuotientGroup.mk' subgroup original
    rw [quotientEquivalence_apply]
    rfl
  map_mul' first second := by
    ext element
    obtain ⟨original, rfl⟩ := QuotientGroup.mk'_surjective subgroup element
    change quotientEquivalence subgroup (first * second)
        (QuotientGroup.mk' subgroup original) =
      quotientEquivalence subgroup first
        (quotientEquivalence subgroup second (QuotientGroup.mk' subgroup original))
    rw [quotientEquivalence_apply, quotientEquivalence_apply, quotientEquivalence_apply]
    rfl

end OrderReductions.FrattiniAutomorphisms

end CFSGOutside.Corpus
