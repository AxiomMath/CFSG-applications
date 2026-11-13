import Mathlib

/-!
# Loeffler (2017): nonabelian simple sections of `PSL₂(𝔽_q)`

D. Loeffler, Glasgow Math. J. 59 (2017), 11–25, Lemma 1.1.2. Dickson's classification and Burnside's `p^a q^b` theorem
are supplied by the corpus.
-/

/-- **Loeffler, Lemma 1.1.2.** Let `F` be a finite field with `p ^ f` elements. A nonabelian simple section `Y / N`
of `PSL₂(F)` is isomorphic to `A₅` or to `PSL₂(𝔽_{p^m})` for some `m` dividing `f` with `p ^ m ≥ 4`.

Source: D. Loeffler, Images of adelic Galois representations for modular forms, Glasgow Math. J. 59 (2017), 11–25,
Lemma 1.1.2. The published lemma gives a field of characteristic `p`; here it is a subfield of `F`. -/
theorem CFSGOutsideClean.LoefflerPsl2Sections.loeffler_simple_section {F : Type} [Field F] [Finite F]
    {p f : ℕ} [Fact p.Prime] (hF : Nat.card F = p ^ f)
    (Y : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) (N : Subgroup Y) [N.Normal]
    [IsSimpleGroup (Y ⧸ N)] (hnonab : ∃ a b : Y ⧸ N, a * b ≠ b * a) :
    Nonempty (Y ⧸ N ≃* alternatingGroup (Fin 5)) ∨
      ∃ m : ℕ, m ≠ 0 ∧ m ∣ f ∧ 4 ≤ p ^ m ∧
        Nonempty (Y ⧸ N ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p m)) :=
  sorry
