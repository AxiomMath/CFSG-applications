import Mathlib
import CFSGOutside.WittDesigns.S4723.Main
import CFSGOutside.Corpus.CardHexadAut

/-!
The automorphisms of the hexad system that preserve a class of odd heptads form a subgroup of index 2.
-/

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSGOutside.WittDesigns.Aut4723

open CFSGOutside.Corpus CFSGOutside.Corpus.WittDesign CFSGOutside.WittDesigns.Witt4723
open CFSGOutside.WittDesigns.Witt5824 (IsOddSeven)
attribute [local instance] Classical.propDecidable

variable [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}] [CardHexads] [CardHexadAut]

theorem map_map_symm {α : Type*} (a : Equiv.Perm α) (H : Finset α) :
    (H.map a.symm.toEmbedding).map a.toEmbedding = H := by
  ext x
  simp [Finset.mem_map_equiv]

section Hex

variable {a : Equiv.Perm (Fin 22)} (ha : a ∈ hexadAut)
include ha

theorem map_symm_mem_hexads_iff (H : Finset (Fin 22)) :
    H.map a.symm.toEmbedding ∈ hexads ↔ H ∈ hexads := by
  have := mem_blockAut.1 ha (H.map a.symm.toEmbedding)
  rw [map_map_symm] at this
  exact this.symm

theorem oddSeven_map_of_mem {X : Finset (Fin 22)} (hX : IsOddSeven X) :
    IsOddSeven (X.map a.toEmbedding) := by
  refine ⟨by rw [Finset.card_map]; exact hX.1, fun H hH => ?_⟩
  have h1 : X.map a.toEmbedding ∩ H = (X ∩ H.map a.symm.toEmbedding).map a.toEmbedding := by
    rw [Finset.map_inter, map_map_symm]
  rw [h1, Finset.card_map]
  exact hX.2 _ ((map_symm_mem_hexads_iff ha H).2 hH)

theorem oddSeven_map_iff {X : Finset (Fin 22)} :
    IsOddSeven (X.map a.toEmbedding) ↔ IsOddSeven X := by
  refine ⟨fun h => ?_, oddSeven_map_of_mem ha⟩
  have ha' : a.symm ∈ hexadAut := hexadAut.inv_mem ha
  have := oddSeven_map_of_mem ha' h
  have e : (X.map a.toEmbedding).map a.symm.toEmbedding = X := by
    simpa using map_map_symm a.symm X
  rwa [e] at this

end Hex

theorem kin_map_iff (b : Equiv.Perm (Fin 22)) {X Y : Finset (Fin 22)} :
    Kin (X.map b.toEmbedding) (Y.map b.toEmbedding) ↔ Kin X Y := by
  unfold Kin
  rw [← Finset.map_inter, Finset.card_map, Finset.map_inj]

omit [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}] [CardHexads] [CardHexadAut] in
/-- The automorphism `a` carries the class of `Y0` to itself. -/
def Pres (Y0 : Finset (Fin 22)) (a : Equiv.Perm (Fin 22)) : Prop := Kin (Y0.map a.toEmbedding) Y0

theorem pres_mul_aPerm {Y0 : Finset (Fin 22)} (hY0 : IsOddSeven Y0) {b : Equiv.Perm (Fin 22)}
    (hb : b ∈ hexadAut) : Pres Y0 (b * aPerm) ↔ ¬ Pres Y0 b := by
  have hZ : IsOddSeven ((Y0.map aPerm.toEmbedding).map b.toEmbedding) :=
    oddSeven_map_of_mem hb (oddSeven_map hY0)
  have hZ' : IsOddSeven (Y0.map b.toEmbedding) := oddSeven_map_of_mem hb hY0
  have hnot : ¬ Kin ((Y0.map aPerm.toEmbedding).map b.toEmbedding) (Y0.map b.toEmbedding) :=
    fun h => not_kin_a hY0 ((kin_map_iff b).1 h)
  unfold Pres
  rw [map_perm_mul']
  constructor
  · intro h1 h2
    exact hnot (Kin.trans hZ hY0 hZ' h1 h2.symm)
  · intro h2
    by_contra h1
    exact h2 (Kin.pigeon hZ hZ' hY0 hnot h1)

theorem card_hexadAut_eq_two_mul {Y0 : Finset (Fin 22)} (hY0 : IsOddSeven Y0) :
    887040 = 2 * Nat.card {b : hexadAut // Pres Y0 b.1} := by
  have haP : (aPerm : Equiv.Perm (Fin 22)) ∈ hexadAut := fun H => aPerm_iff H
  have h1 : Nat.card hexadAut =
      Nat.card {b : hexadAut // Pres Y0 b.1} + Nat.card {b : hexadAut // ¬ Pres Y0 b.1} := by
    rw [← Nat.card_sum]
    exact Nat.card_congr (Equiv.sumCompl (fun b : hexadAut => Pres Y0 b.1)).symm
  have h2 : Nat.card {b : hexadAut // ¬ Pres Y0 b.1} = Nat.card {b : hexadAut // Pres Y0 b.1} := by
    apply le_antisymm
    · refine Nat.card_le_card_of_injective
        (fun b => (⟨⟨b.1.1 * aPerm, hexadAut.mul_mem b.1.2 haP⟩, ?_⟩ :
          {b : hexadAut // Pres Y0 b.1})) ?_
      · exact (pres_mul_aPerm hY0 b.1.2).2 b.2
      · intro b c h
        have := congrArg (fun x : {b : hexadAut // Pres Y0 b.1} => x.1.1) h
        exact Subtype.ext (Subtype.ext (mul_right_cancel this))
    · refine Nat.card_le_card_of_injective
        (fun b => (⟨⟨b.1.1 * aPerm, hexadAut.mul_mem b.1.2 haP⟩, ?_⟩ :
          {b : hexadAut // ¬ Pres Y0 b.1})) ?_
      · exact fun hc => ((pres_mul_aPerm hY0 b.1.2).1 hc) b.2
      · intro b c h
        have := congrArg (fun x : {b : hexadAut // ¬ Pres Y0 b.1} => x.1.1) h
        exact Subtype.ext (Subtype.ext (mul_right_cancel this))
  have h3 : Nat.card hexadAut = 887040 := CardHexadAut.card_hexadAut.1
  omega

end CFSGOutside.WittDesigns.Aut4723
