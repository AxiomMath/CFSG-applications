import Mathlib

/-!
# Corpus input: a 5-transitive group with a small nontrivial support contains `Alt`

Statement of `CFSG.FiveTransitive.SmallSupportGeneric.alternatingGroup_le_of_nontrivial_support_le_six`,
copied verbatim from `CFSG/Permutation/FiveTransitive/SmallSupportGeneric.lean` (line 689) at AxiomMath/CFSG
commit 69cb972f587a3ecc035e092253167ff2e303c962. The clean build provides the instance from the corpus theorem,
in `clean/CFSGOutsideClean/Corpus/AlternatingGroupLeOfNontrivialSupportLeSix.lean`.
-/

namespace CFSGOutside.Corpus

/-- A 5-transitive permutation group of degree at least 8 containing a nontrivial element of support at most 6
contains the alternating group. -/
class AlternatingGroupLeOfNontrivialSupportLeSix : Prop where
  alternatingGroup_le_of_nontrivial_support_le_six : ∀
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (_hcard : 8 ≤ Fintype.card X)
    (_h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    {g : Equiv.Perm X} (_hg : g ∈ P)
    (_hgNe : g ≠ 1) (_hgsupport : g.support.card ≤ 6),
    alternatingGroup X ≤ P

end CFSGOutside.Corpus
