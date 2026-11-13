import Mathlib
import CFSGOutside.PlessSloaneG22.Paper
import CFSGOutside.WittDesigns.S5824.Design

/-!
Facts about the hexads of `S(3,6,22)` and the code `G22` used in the uniqueness of `S(5,8,24)`.
-/

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSGOutside.WittDesigns.Witt5824

open CFSGOutside.Corpus CFSGOutside.Corpus.WittDesign CFSGOutside.PlessSloaneG22
open scoped Matrix

variable [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}] [CardHexads] [CardHexadAut]

theorem natCast_zmod2_eq_zero_iff {n : ℕ} : (n : ZMod 2) = 0 ↔ Even n :=
  ZMod.natCast_eq_zero_iff_even

theorem natCast_zmod2_eq_one_iff {n : ℕ} : (n : ZMod 2) = 1 ↔ Odd n := by
  rw [← Nat.not_even_iff_odd, ← natCast_zmod2_eq_zero_iff]
  have : ∀ a : ZMod 2, a ≠ 0 ↔ a = 1 := by decide
  rw [← this]

/-- A word orthogonal to all hexads lies in `G22`. -/
theorem mem_G22_of_dot {x : Word} (h : ∀ H ∈ hexads, ind H ⬝ᵥ x = 0) : x ∈ G22 := by
  rw [G22_isSelfDual x]
  intro c hc
  have hker : G22 ≤ LinearMap.ker (dotForm.flip x) := by
    rw [G22, Submodule.span_le]
    rintro _ ⟨H, hH, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.BilinForm.flip_apply, dotForm_apply]
    exact h H hH
  have := hker hc
  rwa [LinearMap.mem_ker, LinearMap.BilinForm.flip_apply, dotForm_apply] at this

omit [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}] [CardHexads] [CardHexadAut] in
/-- The sets of seven points meeting every hexad oddly. -/
def IsOddSeven (X : Finset (Fin 22)) : Prop := X.card = 7 ∧ ∀ H ∈ hexads, Odd (X ∩ H).card

theorem dot_ind_ind (X Y : Finset (Fin 22)) : ind X ⬝ᵥ ind Y = ((X ∩ Y).card : ZMod 2) := by
  rw [dot_eq_card, supp_ind, supp_ind]

theorem ind_add_mem_G22 {X Y : Finset (Fin 22)} (hX : IsOddSeven X) (hY : IsOddSeven Y) :
    ind X + ind Y ∈ G22 := by
  refine mem_G22_of_dot fun H hH => ?_
  rw [dotProduct_add, dot_ind_ind, dot_ind_ind, Finset.inter_comm H X, Finset.inter_comm H Y,
    (natCast_zmod2_eq_one_iff).2 (hX.2 H hH), (natCast_zmod2_eq_one_iff).2 (hY.2 H hH)]
  decide

theorem card_inter_le_four {X Y : Finset (Fin 22)} (hX : IsOddSeven X) (hY : IsOddSeven Y)
    (hne : X ≠ Y) : (X ∩ Y).card ≤ 4 := by
  have hm := G22_minWeight (ind X + ind Y) (ind_add_mem_G22 hX hY) (fun h0 => hne (by
    rw [add_eq_zero_iff_eq] at h0
    rw [← supp_ind X, h0, supp_ind]))
  have hw := wt_add_add (ind X) (ind Y)
  rw [supp_ind, supp_ind] at hw
  have h1 : wt (ind X) = 7 := by rw [wt, supp_ind, hX.1]
  have h2 : wt (ind Y) = 7 := by rw [wt, supp_ind, hY.1]
  omega

/-- Three odd sevens: the pairwise intersection parities add up to an odd number. -/
theorem odd_inter_of_even_inter {X Y Y' : Finset (Fin 22)} (hX : IsOddSeven X) (hY : IsOddSeven Y)
    (hY' : IsOddSeven Y') (h1 : Even (X ∩ Y).card) (h2 : Even (X ∩ Y').card) :
    Odd (Y ∩ Y').card := by
  have h0 := dot_eq_zero G22_isSelfDual (ind_add_mem_G22 hX hY) (ind_add_mem_G22 hX hY')
  rw [add_dotProduct, dotProduct_add, dotProduct_add, dot_ind_ind, dot_ind_ind, dot_ind_ind,
    dot_ind_ind, Finset.inter_self, hX.1, Finset.inter_comm Y X] at h0
  have e1 : ((X ∩ Y).card : ZMod 2) = 0 := natCast_zmod2_eq_zero_iff.2 h1
  have e2 : ((X ∩ Y').card : ZMod 2) = 0 := natCast_zmod2_eq_zero_iff.2 h2
  rw [e1, e2] at h0
  have : ((Y ∩ Y').card : ZMod 2) = 1 := by
    have h7 : ((7 : ℕ) : ZMod 2) = 1 := by decide
    rw [h7] at h0
    have key : ∀ a : ZMod 2, 1 + 0 + (0 + a) = 0 → a = 1 := by decide
    exact key _ (by simpa using h0)
  exact natCast_zmod2_eq_one_iff.1 this

end CFSGOutside.WittDesigns.Witt5824
