import Mathlib

/-!
# Galois (1832): the minimal degree of `PSL₂(q)`

É. Galois, letter to Auguste Chevalier of 29 May 1832. Dickson's classification of the subgroups of `PSL₂(q)` is
supplied by the corpus.
-/

/-- **Galois's theorem.** Let `F` be a finite field. The group `PSL₂(F)` has a proper subgroup of index less than
`|F| + 1` if and only if `|F|` is one of `2, 3, 5, 7, 9, 11`.

Source: É. Galois, letter to Auguste Chevalier, 29 May 1832, for prime `|F|`. The statement for prime powers is the
one proved here. -/
theorem CFSGOutsideClean.GaloisMinimalDegree.galois_iff_primePower {F : Type} [Field F] [Finite F] {p f : ℕ}
    [Fact p.Prime] (hF : Nat.card F = p ^ f) :
    (∃ H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F),
        H ≠ ⊤ ∧ H.index < Nat.card F + 1) ↔
      Nat.card F = 2 ∨ Nat.card F = 3 ∨ Nat.card F = 5 ∨ Nat.card F = 7 ∨
        Nat.card F = 9 ∨ Nat.card F = 11 :=
  sorry

/-- **Galois's last letter.** Let `F` be a finite field with `p` elements, where `p ∈ {5, 7, 11}`. Every proper
subgroup of `PSL₂(F)` has index at least `p`, and some proper subgroup has index exactly `p`.

Source: É. Galois, letter to Auguste Chevalier, 29 May 1832. -/
theorem CFSGOutsideClean.GaloisMinimalDegree.galois_exact_index {F : Type} [Field F] [Finite F] {p : ℕ}
    [Fact p.Prime] (hF : Nat.card F = p) (hp : p = 5 ∨ p = 7 ∨ p = 11) :
    (∃ H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F), H ≠ ⊤ ∧ H.index = p) ∧
      ∀ H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F), H ≠ ⊤ → p ≤ H.index :=
  sorry
