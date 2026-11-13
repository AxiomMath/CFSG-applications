import CFSGOutside.Baddeley.Definitions
import CFSGOutside.Corpus.Schreier
import CFSGOutside.Corpus.OddOrder
import CFSGOutside.Corpus.GlaubermanZStar

/-!
# Baddeley, Lemmas 6.1 and 6.2 (fast path)

R. W. Baddeley, *Two-arc transitive graphs and twisted wreath products*, J. Algebraic Combin. 2 (1993), 215–237,
DOI 10.1023/A:1022447514654. Lemmas 6.2 (p. 232) and 6.1 (p. 229) on special pairs, under the classification
statement. Conditional on the Schreier conjecture for the catalogue, the Odd Order Theorem and Glauberman's
Z*-theorem, stated in `CFSGOutside.Corpus`.
-/

namespace CFSGOutside.Baddeley

open CFSGOutside.Corpus

variable {V : Type} [Finite V] {Γ : SimpleGraph V}

theorem eq_of_isSpecialPair [Schreier] [OddOrder.{0}] [GlaubermanZStar]
    (hCFSG : TauCeti.ClassificationStatement.{0}) {G H M M' : Subgroup (Equiv.Perm V)}
    (hG : IsSpecialPair Γ G) (hM : IsMinimalNormalIn M G) (hMna : IsNonabelian M)
    (hMreg : IsRegular V M) (hHG : H ≤ G) (hM' : IsMinimalNormalIn M' H) (hM'na : IsNonabelian M')
    (hM'reg : IsRegular V M') : M' = M := sorry

theorem lemma_6_2 [Schreier] [OddOrder.{0}] [GlaubermanZStar]
    (hCFSG : TauCeti.ClassificationStatement.{0}) {G H M : Subgroup (Equiv.Perm V)}
    (hG : IsSpecialPair Γ G) (hM : IsMinimalNormalIn M G) (hMna : IsNonabelian M)
    (hMreg : IsRegular V M) (hHG : H ≤ G) (hH : IsSpecialPair Γ H) :
    M ≤ H ∧ IsMinimalNormalIn M H := sorry

theorem lemma_6_1 [Schreier] [OddOrder.{0}] [GlaubermanZStar]
    (hCFSG : TauCeti.ClassificationStatement.{0}) {G : Subgroup (Equiv.Perm V)}
    (hG : IsSpecialPair Γ G) :
    ∃! M : Subgroup (Equiv.Perm V), IsMinimalNormalIn M G ∧ IsNonabelian M ∧ IsRegular V M := sorry

end CFSGOutside.Baddeley
