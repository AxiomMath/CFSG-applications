import CFSGOutside.GaloisMinimalDegree.Field9Transfer
import CFSGOutside.GaloisMinimalDegree.Iff

/-!
# Galois: the minimal degree of `PSL(2, q)`

Galois (letter to Chevalier, 1832): `PSL(2, q)` has a proper subgroup of index less than `q + 1` if and only if
`q ∈ {2, 3, 5, 7, 9, 11}`. For `q = p` prime and `p ∈ {5, 7, 11}` the minimal index is exactly `p`. The proof
uses Dickson's classification of the subgroups of `PSL(2, q)`, stated as a class in `CFSGOutside.Corpus`.
-/

open scoped MatrixGroups

namespace CFSGOutside.GaloisMinimalDegree

open CFSGOutside.Corpus CFSGOutside.Psl2Basic

/-- **Galois, 1832.** `PSL(2, q)` has a proper subgroup of index `< q + 1` iff `q ∈ {2, 3, 5, 7, 9, 11}`.
Galois states it for prime `q`; the statement for prime powers is the one proved here. -/
theorem galois_iff_primePower [DicksonPsl2SubgroupClassification.{0}] {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hF : Nat.card F = p ^ f) :
    (∃ H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F),
        H ≠ ⊤ ∧ H.index < Nat.card F + 1) ↔
      Nat.card F = 2 ∨ Nat.card F = 3 ∨ Nat.card F = 5 ∨ Nat.card F = 7 ∨
        Nat.card F = 9 ∨ Nat.card F = 11 := by
  constructor
  · rintro ⟨H, hne, hidx⟩
    exact galois_minimal_degree hF H hne (by omega)
  · intro h
    by_cases h9 : Nat.card F = 9
    · obtain ⟨H, hne, hidx⟩ := exists_index_six h9
      exact ⟨H, hne, by omega⟩
    · have hprime : (Nat.card F).Prime := by
        rcases h with h | h | h | h | h | h <;> rw [h] <;> first | omega | norm_num
      haveI : Fact (Nat.card F).Prime := ⟨hprime⟩
      exact (galois_iff (p := Nat.card F) rfl).2 (by omega)


/-- For `q = p ∈ {5, 7, 11}` the minimal index of a proper subgroup of `PSL(2, p)` is exactly `p`. -/
theorem galois_exact_index [DicksonPsl2SubgroupClassification.{0}] {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (hF : Nat.card F = p) (hp : p = 5 ∨ p = 7 ∨ p = 11) :
    (∃ H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F), H ≠ ⊤ ∧ H.index = p) ∧
      ∀ H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F), H ≠ ⊤ → p ≤ H.index := by
  refine ⟨exists_index_eq_of_mem hF (by omega), fun H hne => ?_⟩
  by_contra h
  exact no_smaller_index hF hp H hne (by omega)

end CFSGOutside.GaloisMinimalDegree
