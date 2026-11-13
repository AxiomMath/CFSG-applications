import CFSGOutside.Corpus.Defs.FixedNormalizerAction

/-!
# Corpus input: the fixed degree of a 5-point stabiliser (Witt and Jordan)

Statement of `CFSG.FiveTransitive.FullFixerSharpFive.fixed_degree_cases`, copied verbatim from
`CFSG/Permutation/FiveTransitive/FullFixerSharpFive.lean` (line 58) at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962, with `Fixed` the copy in `CFSGOutside.Corpus.Defs`. The clean build
provides the instance from the corpus theorem, in `clean/CFSGOutsideClean/Corpus/FixedDegreeCases.lean`.
-/

namespace CFSGOutside.Corpus

open MulAction FiveTransitive.FixedNormalizerAction

/-- In a 5-transitive group, the pointwise stabiliser of a 5-set fixes 5, 6, 7 or 12 points. -/
class FixedDegreeCases : Prop where
  fixed_degree_cases : ∀
    {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X]
    (_h5 : IsMultiplyPretransitive G X 5) (s : Set X) (_hs : s.ncard = 5),
    let m := Nat.card (Fixed (X := X) (fixingSubgroup G s))
    m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 12

end CFSGOutside.Corpus
