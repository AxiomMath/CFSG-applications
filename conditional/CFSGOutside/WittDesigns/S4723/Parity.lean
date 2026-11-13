import Mathlib
import CFSGOutside.WittDesigns.S5824.Code

/-!
The odd heptads of the hexad system fall into at most two classes: two of them are related when they
are equal or meet in an odd number of points.
-/

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSGOutside.WittDesigns.Witt4723

open CFSGOutside.Corpus CFSGOutside.Corpus.WittDesign CFSGOutside.PlessSloaneG22 CFSGOutside.WittDesigns.Witt5824
open scoped Matrix

variable [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}] [CardHexads] [CardHexadAut]

omit [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}] [CardHexads] [CardHexadAut] in
/-- Equal or meeting oddly. -/
def Kin (X Y : Finset (Fin 22)) : Prop := X = Y ∨ Odd (X ∩ Y).card

theorem Kin.symm {X Y : Finset (Fin 22)} (h : Kin X Y) : Kin Y X := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · exact Or.inr (by rwa [Finset.inter_comm])

theorem parity_sum {X Y Y' : Finset (Fin 22)} (hX : IsOddSeven X) (hY : IsOddSeven Y)
    (hY' : IsOddSeven Y') :
    ((X ∩ Y).card : ZMod 2) + ((X ∩ Y').card : ZMod 2) + ((Y ∩ Y').card : ZMod 2) = 1 := by
  have h0 := dot_eq_zero G22_isSelfDual (ind_add_mem_G22 hX hY) (ind_add_mem_G22 hX hY')
  rw [add_dotProduct, dotProduct_add, dotProduct_add, dot_ind_ind, dot_ind_ind, dot_ind_ind,
    dot_ind_ind, Finset.inter_self, hX.1, Finset.inter_comm Y X] at h0
  have h7 : ((7 : ℕ) : ZMod 2) = 1 := by decide
  rw [h7] at h0
  generalize ((X ∩ Y).card : ZMod 2) = a at h0 ⊢
  generalize ((X ∩ Y').card : ZMod 2) = b at h0 ⊢
  generalize ((Y ∩ Y').card : ZMod 2) = c at h0 ⊢
  revert a b c; decide

theorem Kin.trans {X Y Z : Finset (Fin 22)} (hX : IsOddSeven X) (hY : IsOddSeven Y)
    (hZ : IsOddSeven Z) (h1 : Kin X Y) (h2 : Kin Y Z) : Kin X Z := by
  rcases h1 with rfl | h1
  · exact h2
  rcases h2 with rfl | h2
  · exact Or.inr h1
  right
  have := parity_sum hY hX hZ
  rw [Finset.inter_comm Y X] at this
  have e1 : ((X ∩ Y).card : ZMod 2) = 1 := natCast_zmod2_eq_one_iff.2 h1
  have e2 : ((Y ∩ Z).card : ZMod 2) = 1 := natCast_zmod2_eq_one_iff.2 h2
  rw [e1, e2] at this
  have key : ∀ a : ZMod 2, 1 + 1 + a = 1 → a = 1 := by decide
  exact natCast_zmod2_eq_one_iff.1 (key _ (by simpa [Finset.inter_comm] using this))

/-- Among three odd heptads, two are related. -/
theorem Kin.pigeon {X Y Z : Finset (Fin 22)} (hX : IsOddSeven X) (hY : IsOddSeven Y)
    (hZ : IsOddSeven Z) (h1 : ¬ Kin X Y) (h2 : ¬ Kin X Z) : Kin Y Z := by
  right
  have e1 : Even (X ∩ Y).card := by
    exact Nat.not_odd_iff_even.1 (fun h => h1 (Or.inr h))
  have e2 : Even (X ∩ Z).card := Nat.not_odd_iff_even.1 (fun h => h2 (Or.inr h))
  exact odd_inter_of_even_inter hX hY hZ e1 e2

end CFSGOutside.WittDesigns.Witt4723
