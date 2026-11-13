import Comparator.Solution
import CFSGOutside.Baddeley.Paper
import CFSGOutsideClean.Corpus.Schreier
import CFSGOutsideClean.Corpus.OddOrder
import CFSGOutsideClean.Corpus.GlaubermanZStar

/-! Baddeley, Lemmas 6.1 and 6.2, with the classification statement supplied by the corpus,
`CFSGComparator.classification`, and the Schreier conjecture for the catalogue, the Odd Order Theorem and
Glauberman's Z*-theorem supplied by the corpus. -/

namespace CFSGOutsideClean.Baddeley

open CFSGOutside.Baddeley

variable {V : Type} [Finite V] {Γ : SimpleGraph V}

/-- **2-arc-transitive graphs.** Let Γ be a finite simple graph, and call a group G of automorphisms of Γ special if Γ
is connected, G is transitive on 2-arcs, and G has a nonabelian minimal normal subgroup that is regular on the
vertices. If G is special, it has exactly one such subgroup M, and if H ≤ G is also special then M ≤ H and M is a
minimal normal subgroup of H.

Source: R. W. Baddeley, Two-arc transitive graphs and twisted wreath products, J. Algebraic Combin. 2 (1993),
215–237, Lemmas 6.1 and 6.2. https://doi.org/10.1023/A:1022447514654 -/
theorem lemma_6_2 {G H M : Subgroup (Equiv.Perm V)} (hG : IsSpecialPair Γ G)
    (hM : IsMinimalNormalIn M G) (hMna : IsNonabelian M) (hMreg : IsRegular V M) (hHG : H ≤ G)
    (hH : IsSpecialPair Γ H) : M ≤ H ∧ IsMinimalNormalIn M H :=
  CFSGOutside.Baddeley.lemma_6_2 CFSGComparator.classification.{0} hG hM hMna hMreg hHG hH

/-- **Baddeley 1993, Lemma 6.2, strong form.** Every regular nonabelian minimal normal subgroup of `H` equals
`M`. -/
theorem eq_of_isSpecialPair {G H M M' : Subgroup (Equiv.Perm V)} (hG : IsSpecialPair Γ G)
    (hM : IsMinimalNormalIn M G) (hMna : IsNonabelian M) (hMreg : IsRegular V M) (hHG : H ≤ G)
    (hM' : IsMinimalNormalIn M' H) (hM'na : IsNonabelian M') (hM'reg : IsRegular V M') : M' = M :=
  CFSGOutside.Baddeley.eq_of_isSpecialPair CFSGComparator.classification.{0} hG hM hMna hMreg hHG hM' hM'na
    hM'reg

/-- **Baddeley 1993, Lemma 6.1.** A special pair has a unique regular, nonabelian, minimal normal subgroup. -/
theorem lemma_6_1 {G : Subgroup (Equiv.Perm V)} (hG : IsSpecialPair Γ G) :
    ∃! M : Subgroup (Equiv.Perm V), IsMinimalNormalIn M G ∧ IsNonabelian M ∧ IsRegular V M :=
  CFSGOutside.Baddeley.lemma_6_1 CFSGComparator.classification.{0} hG

end CFSGOutsideClean.Baddeley
