import Mathlib
import CFSGOutside.WittDesigns.S4723.Parity

/-!
An involutive automorphism of the hexads that exchanges the two classes of odd heptads.
-/

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSGOutside.WittDesigns.Witt4723

open CFSGOutside.Corpus CFSGOutside.Corpus.WittDesign
open CFSGOutside.WittDesigns.Witt5824 (IsOddSeven)

/-- An outer automorphism of the hexad system, as a table. -/
def aTab : Fin 22 → Fin 22 :=
  ![0, 1, 2, 3, 8, 21, 20, 13, 4, 19, 10, 15, 12, 7, 14, 11, 18, 17, 16, 9, 6, 5]

theorem aTab_invol : ∀ x, aTab (aTab x) = x := by decide

def aPerm : Equiv.Perm (Fin 22) := ⟨aTab, aTab, aTab_invol, aTab_invol⟩

theorem aPerm_symm_apply (x : Fin 22) : aPerm.symm x = aTab x := rfl

theorem aPerm_hexadList : ∀ H ∈ hexadList, H.map aPerm.toEmbedding ∈ hexadList := by
  have h : hexadList.all (fun H => decide (H.map aPerm.toEmbedding ∈ hexadList)) = true := by
    decide +kernel
  exact fun H hH => of_decide_eq_true (List.all_eq_true.1 h H hH)

theorem aPerm_hexads : ∀ H ∈ hexads, H.map aPerm.toEmbedding ∈ hexads := fun H hH => by
  rw [mem_hexads] at hH ⊢
  exact aPerm_hexadList H hH

theorem X1_hexadList : ∀ H ∈ hexadList, Odd (({0, 1, 2, 3, 4, 15, 16} : Finset (Fin 22)) ∩ H).card := by
  have h : hexadList.all (fun H => decide (Odd (({0, 1, 2, 3, 4, 15, 16} : Finset (Fin 22)) ∩ H).card))
      = true := by decide +kernel
  exact fun H hH => of_decide_eq_true (List.all_eq_true.1 h H hH)

theorem map_a_a (H : Finset (Fin 22)) : (H.map aPerm.toEmbedding).map aPerm.toEmbedding = H := by
  ext x
  rw [Finset.mem_map_equiv, Finset.mem_map_equiv, aPerm_symm_apply, aPerm_symm_apply, aTab_invol]

theorem aPerm_iff (H : Finset (Fin 22)) : H.map aPerm.toEmbedding ∈ hexads ↔ H ∈ hexads := by
  constructor
  · intro h
    have := aPerm_hexads _ h
    rwa [map_a_a] at this
  · exact aPerm_hexads H

theorem oddSeven_map {X : Finset (Fin 22)} (hX : IsOddSeven X) :
    IsOddSeven (X.map aPerm.toEmbedding) := by
  refine ⟨by rw [Finset.card_map]; exact hX.1, fun H hH => ?_⟩
  have h1 : X.map aPerm.toEmbedding ∩ H = (X ∩ H.map aPerm.toEmbedding).map aPerm.toEmbedding := by
    rw [Finset.map_inter, map_a_a]
  rw [h1, Finset.card_map]
  exact hX.2 _ ((aPerm_iff _).2 hH)

theorem kin_map {X Y : Finset (Fin 22)} (h : Kin X Y) :
    Kin (X.map aPerm.toEmbedding) (Y.map aPerm.toEmbedding) := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · right
    rwa [← Finset.map_inter, Finset.card_map]

/-- A seven-set meeting every hexad oddly. -/
def X1 : Finset (Fin 22) := {0, 1, 2, 3, 4, 15, 16}

theorem X1_odd : IsOddSeven X1 := by
  refine ⟨by decide, fun H hH => ?_⟩
  rw [mem_hexads] at hH
  exact X1_hexadList H hH

theorem aX1 : ¬ Kin (X1.map aPerm.toEmbedding) X1 := by
  unfold Kin
  decide +kernel

variable [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}] [CardHexads] [CardHexadAut] in
/-- The automorphism moves every odd heptad out of its class. -/
theorem not_kin_a {X : Finset (Fin 22)} (hX : IsOddSeven X) : ¬ Kin (X.map aPerm.toEmbedding) X := by
  intro hk
  by_cases h1 : Kin X X1
  · apply aX1
    have k1 : Kin (X.map aPerm.toEmbedding) X1 := Kin.trans (oddSeven_map hX) hX X1_odd hk h1
    have k2 : Kin (X.map aPerm.toEmbedding) (X1.map aPerm.toEmbedding) := kin_map h1
    exact Kin.trans (oddSeven_map X1_odd) (oddSeven_map hX) X1_odd k2.symm k1
  · have h3 : Kin (X1.map aPerm.toEmbedding) X :=
      Kin.pigeon X1_odd (oddSeven_map X1_odd) hX (fun h => aX1 h.symm) (fun h => h1 h.symm)
    have h4 := kin_map h3
    rw [map_a_a] at h4
    have h5 : Kin X1 X := Kin.trans X1_odd (oddSeven_map hX) hX h4 hk
    exact h1 h5.symm

variable [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}] [CardHexads] [CardHexadAut] in
/-- If two heptads lie in different classes, the automorphism carries the class of one to the other. -/
theorem swap_ok {Y0 Y0' : Finset (Fin 22)} (h0 : IsOddSeven Y0) (h0' : IsOddSeven Y0')
    (hn : ¬ Kin Y0 Y0') {Y : Finset (Fin 22)} (hY : IsOddSeven Y) (hk : Kin Y Y0) :
    Kin (Y.map aPerm.toEmbedding) Y0' := by
  have hp : Kin (Y0.map aPerm.toEmbedding) Y0' :=
    Kin.pigeon h0 (oddSeven_map h0) h0' (fun h => not_kin_a h0 h.symm) hn
  exact Kin.trans (oddSeven_map hY) (oddSeven_map h0) h0' (kin_map hk) hp

end CFSGOutside.WittDesigns.Witt4723
