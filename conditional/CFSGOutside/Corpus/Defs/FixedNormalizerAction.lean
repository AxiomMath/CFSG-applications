import Mathlib

/-!
# Copied corpus definitions: the fixed set of a subgroup, as its normaliser sees it

Verbatim copies, under `CFSGOutside.Corpus`, of `Normalizer`, `Inside` and `Fixed` in
`CFSG/Permutation/FiveTransitive/FixedNormalizerAction.lean` (lines 15–17) at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962. `clean/CFSGOutsideClean/Corpus/Defs/FixedNormalizerAction.lean` shows
each copy equals its original. `fixed_eq` (line 21 there) is proved here.
-/

namespace CFSGOutside.Corpus.FiveTransitive.FixedNormalizerAction

open MulAction

/-- `CFSG.FiveTransitive.FixedNormalizerAction.Normalizer`. -/
abbrev Normalizer {G:Type*} [Group G] (Q:Subgroup G) := Subgroup.normalizer (Q:Set G)
/-- `CFSG.FiveTransitive.FixedNormalizerAction.Inside`. -/
abbrev Inside {G:Type*} [Group G] (Q:Subgroup G) := Q.subgroupOf (Normalizer Q)
/-- `CFSG.FiveTransitive.FixedNormalizerAction.Fixed`. -/
abbrev Fixed {G X:Type*} [Group G] [MulAction G X] (Q:Subgroup G) := fixedPoints (Inside Q) X

theorem fixed_eq {G X:Type*} [Group G] [MulAction G X] (Q:Subgroup G) :
    (Fixed (X:=X) Q : Set X)=fixedPoints Q X := by
  ext x
  constructor
  · intro hx q
    exact hx ⟨⟨q, Q.le_normalizer q.2⟩, q.2⟩
  · intro hx q
    exact hx ⟨q.1.1, q.2⟩

end CFSGOutside.Corpus.FiveTransitive.FixedNormalizerAction
