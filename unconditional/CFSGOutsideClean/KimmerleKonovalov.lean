import Comparator.Solution
import CFSGOutside.KimmerleKonovalov.Paper
import CFSGOutsideClean.Corpus.Schreier

/-! Kimmerle–Konovalov, Corollary 2.6, with the classification statement supplied by the corpus,
`CFSGComparator.classification`, and Schreier's conjecture for the catalogue supplied by the corpus.
`CFSGOutside.Corpus.ComponentClassification.OuterAutomorphisms.inner` is the corpus definition
`CFSG.ComponentClassification.OuterAutomorphisms.inner`, by
`CFSGOutsideClean.Corpus.ComponentClassification.OuterAutomorphisms.inner_eq`. -/

open KimmerleKonovalov

/-- **Prime graphs of integral group rings.** Let S be a finite nonabelian simple group, G a subgroup of Aut(S)
containing Inn(S), q a prime dividing |G| but not |S|, and p a prime dividing |S|. Then the group V(ℤG) of units of
augmentation 1 in the integral group ring ℤG has an element of order pq if and only if G has one.

Source: W. Kimmerle and A. Konovalov, On the Gruenberg–Kegel graph of integral group rings of finite groups,
Internat. J. Algebra Comput. 27 (2017), 619–631, Corollary 2.6. https://doi.org/10.1142/S0218196717500308 -/
theorem CFSGOutsideClean.KimmerleKonovalov.cor26
    {S : Type} [Group S] [Finite S]
    [IsSimpleGroup S] (hS : ∃ a b : S, a * b ≠ b * a) (G : Subgroup (MulAut S))
    (hG : CFSGOutside.Corpus.ComponentClassification.OuterAutomorphisms.inner S ≤ G) {q : ℕ}
    (hq : q.Prime)
    (hqG : q ∣ Nat.card G) (hqS : ¬ q ∣ Nat.card S) {p : ℕ} (hp : p.Prime)
    (hpS : p ∣ Nat.card S) :
    IsAdj (V G) p q ↔ IsAdj G p q :=
  _root_.KimmerleKonovalov.cor26 CFSGComparator.classification.{0} hS G hG hq hqG hqS hp hpS

/-- The same theorem, stated with the corpus definition of the inner automorphism group. -/
theorem CFSGOutsideClean.KimmerleKonovalov.cor26_corpus
    {S : Type} [Group S] [Finite S]
    [IsSimpleGroup S] (hS : ∃ a b : S, a * b ≠ b * a) (G : Subgroup (MulAut S))
    (hG : CFSG.ComponentClassification.OuterAutomorphisms.inner S ≤ G) {q : ℕ} (hq : q.Prime)
    (hqG : q ∣ Nat.card G) (hqS : ¬ q ∣ Nat.card S) {p : ℕ} (hp : p.Prime)
    (hpS : p ∣ Nat.card S) :
    IsAdj (V G) p q ↔ IsAdj G p q :=
  CFSGOutsideClean.KimmerleKonovalov.cor26 hS G
    ((CFSGOutsideClean.Corpus.ComponentClassification.OuterAutomorphisms.inner_eq S).trans_le hG)
    hq hqG hqS hp hpS

/-- **Corollary 2.6, abstract form.** The same statement for a finite group `G` with a nonabelian
simple normal subgroup `S` whose centralizer is trivial (equivalently, `S ≤ G ≲ Aut(S)` via
conjugation). -/
theorem CFSGOutsideClean.KimmerleKonovalov.cor26_abstract
    {G : Type} [Group G]
    [Finite G] (S : Subgroup G) [S.Normal] [IsSimpleGroup S] (hS : ∃ a b : S, a * b ≠ b * a)
    (hC : Subgroup.centralizer (S : Set G) = ⊥) {q : ℕ} (hq : q.Prime) (hqG : q ∣ Nat.card G)
    (hqS : ¬ q ∣ Nat.card S) {p : ℕ} (hp : p.Prime) (hpS : p ∣ Nat.card S) :
    IsAdj (V G) p q ↔ IsAdj G p q :=
  _root_.KimmerleKonovalov.cor26_abstract CFSGComparator.classification.{0} S hS hC hq hqG hqS hp hpS
