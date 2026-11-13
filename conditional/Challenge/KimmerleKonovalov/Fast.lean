import CFSGOutside.KimmerleKonovalov.Definitions
import CFSGOutside.Corpus.Schreier

/-!
# Kimmerle–Konovalov, Corollary 2.6 (fast path)

W. Kimmerle and A. Konovalov, *On the Gruenberg–Kegel graph of integral group rings of finite groups*, Internat.
J. Algebra Comput. 27 (2017), 619–631, DOI 10.1142/S0218196717500308. For an almost simple group `G` of type `S`
and a prime `q` dividing `|G|` but not `|S|`, the primes `p ∈ π(S)` and `q` are adjacent in the prime graph of
`V(ℤG)` exactly when they are adjacent in the prime graph of `G`. Conditional on Schreier's conjecture for the
catalogue, stated in `CFSGOutside.Corpus`.
-/

theorem KimmerleKonovalov.cor26 [CFSGOutside.Corpus.Schreier]
    (hCFSG : TauCeti.ClassificationStatement.{0}) {S : Type} [Group S] [Finite S]
    [IsSimpleGroup S] (hS : ∃ a b : S, a * b ≠ b * a) (G : Subgroup (MulAut S))
    (hG : CFSGOutside.Corpus.ComponentClassification.OuterAutomorphisms.inner S ≤ G) {q : ℕ}
    (hq : q.Prime)
    (hqG : q ∣ Nat.card G) (hqS : ¬ q ∣ Nat.card S) {p : ℕ} (hp : p.Prime)
    (hpS : p ∣ Nat.card S) :
    IsAdj (V G) p q ↔ IsAdj G p q := sorry

theorem KimmerleKonovalov.cor26_abstract [CFSGOutside.Corpus.Schreier]
    (hCFSG : TauCeti.ClassificationStatement.{0}) {G : Type} [Group G]
    [Finite G] (S : Subgroup G) [S.Normal] [IsSimpleGroup S] (hS : ∃ a b : S, a * b ≠ b * a)
    (hC : Subgroup.centralizer (S : Set G) = ⊥) {q : ℕ} (hq : q.Prime) (hqG : q ∣ Nat.card G)
    (hqS : ¬ q ∣ Nat.card S) {p : ℕ} (hp : p.Prime) (hpS : p ∣ Nat.card S) :
    IsAdj (V G) p q ↔ IsAdj G p q := sorry
