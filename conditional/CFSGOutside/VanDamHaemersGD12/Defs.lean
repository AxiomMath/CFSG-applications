import Mathlib

/-!
# The Tutte 12-cage

The Tutte 12-cage is the cubic graph on `ℤ/126` with LCF notation
`[17, 27, -13, -59, -35, 35, -11, 13, -53, 53, -27, 21, 57, 11, -21, -57, 59, -17]^7`: vertex `i` is adjacent
to `i ± 1` and to `i + L (i mod 18)`. It is the incidence graph of the generalized hexagon of order `2`, i.e.
the collinearity graph of the generalized dodecagon `GD(1,2)`.
-/

namespace CFSGOutside.VanDamHaemersGD12

open Finset

/-- The LCF offsets, reduced mod `126`. -/
def lcf : List ℕ := [17, 27, 113, 67, 91, 35, 115, 13, 73, 53, 99, 21, 57, 11, 105, 69, 59, 109]

/-- The chord at vertex `i`. -/
def chord (i : ℕ) : ℕ := (i + lcf.getD (i % 18) 0) % 126

/-- The next vertex on the Hamiltonian cycle. -/
def nxt (i : ℕ) : ℕ := (i + 1) % 126

/-- The previous vertex on the Hamiltonian cycle. -/
def prv (i : ℕ) : ℕ := (i + 125) % 126

lemma lt_nxt (i : ℕ) : nxt i < 126 := Nat.mod_lt _ (by norm_num)
lemma lt_prv (i : ℕ) : prv i < 126 := Nat.mod_lt _ (by norm_num)
lemma lt_chord (i : ℕ) : chord i < 126 := Nat.mod_lt _ (by norm_num)

lemma prv_nxt (i : ℕ) (hi : i < 126) : prv (nxt i) = i := by unfold prv nxt; omega
lemma nxt_prv (i : ℕ) (hi : i < 126) : nxt (prv i) = i := by unfold prv nxt; omega

lemma chord_chord : ∀ i : Fin 126, chord (chord i) = i := by decide

lemma distinct : ∀ i : Fin 126, i.val ≠ nxt i ∧ i.val ≠ prv i ∧ i.val ≠ chord i ∧ nxt i ≠ prv i ∧
    nxt i ≠ chord i ∧ prv i ≠ chord i := by decide

/-- The adjacency relation of the Tutte 12-cage: `i` is adjacent to `i ± 1` and to its chord. -/
def cageRel (i j : Fin 126) : Prop := j.val = nxt i ∨ j.val = prv i ∨ j.val = chord i

instance : DecidableRel cageRel := fun i j => by unfold cageRel; infer_instance

lemma cageRel_symm (i j : Fin 126) (h : cageRel i j) : cageRel j i := by
  rcases h with h | h | h
  · right; left; rw [h, prv_nxt _ i.2]
  · left; rw [h, nxt_prv _ i.2]
  · right; right; rw [h, chord_chord i]

lemma cageRel_irrefl (i : Fin 126) : ¬ cageRel i i := by
  obtain ⟨h1, h2, h3, -⟩ := distinct i
  rintro (h | h | h)
  exacts [h1 h, h2 h, h3 h]

/-- The Tutte 12-cage, as the LCF graph `[17, 27, -13, -59, -35, 35, -11, 13, -53, 53, -27, 21, 57, 11, -21,
-57, 59, -17]^7` on `Fin 126`. -/
def cage : SimpleGraph (Fin 126) where
  Adj := cageRel
  symm := ⟨cageRel_symm⟩
  loopless := ⟨cageRel_irrefl⟩

lemma cage_adj (i j : Fin 126) : cage.Adj i j ↔ cageRel i j := Iff.rfl

instance : DecidableRel cage.Adj := inferInstanceAs (DecidableRel cageRel)

end CFSGOutside.VanDamHaemersGD12
