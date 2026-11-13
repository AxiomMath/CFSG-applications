import Mathlib
import CFSGOutside.WittDesigns.S5824.Struct

/-!
Two normalized `S(5,8,24)` differ at most by exchanging the two extra points.
-/

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSGOutside.WittDesigns.Witt5824

open CFSGOutside.Corpus CFSGOutside.Corpus.WittDesign CFSGOutside.PlessSloaneG22
open scoped Matrix
attribute [local instance] Classical.propDecidable

variable [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}] [CardHexads] [CardHexadAut]

omit [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}] [CardHexads] [CardHexadAut] in
/-- The weight-8 words of `G22`, as sets. -/
noncomputable def W8 : Finset (Finset (Fin 22)) :=
  Finset.univ.filter fun Z => Z.card = 8 ∧ ind Z ∈ G22

omit [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}] [CardHexads] [CardHexadAut] in
/-- The 22-point octads of a design on `Pt`. -/
noncomputable def O8 (𝒮 : Finset (Finset Pt)) : Finset (Finset (Fin 22)) :=
  Finset.univ.filter fun Z => Z.map ι ∈ 𝒮

theorem card_W8 : W8.card = 330 := by
  have h := (weight_distribution G22_isSelfDual G22_minWeight).2.1
  rw [← h, A]
  refine Finset.card_bij (fun Z hZ => (⟨ind Z, (Finset.mem_filter.1 hZ).2.2⟩ : G22)) ?_ ?_ ?_
  · intro Z hZ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [wt, supp_ind]
    exact (Finset.mem_filter.1 hZ).2.1
  · intro Z _ Z' _ h
    have := congrArg Subtype.val h
    simp only at this
    rw [← supp_ind Z, this, supp_ind]
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    refine ⟨supp (c : Word), Finset.mem_filter.2 ⟨Finset.mem_univ _, hc, ?_⟩, ?_⟩
    · rw [ind_supp]; exact c.2
    · apply Subtype.ext
      simp only
      exact ind_supp _
  
section Normal

variable {𝒮 : Finset (Finset Pt)} (hN : IsNormal 𝒮)
include hN

theorem O8_subset : O8 𝒮 ⊆ W8 := by
  intro Z hZ
  have hZ' : Z.map ι ∈ 𝒮 := (Finset.mem_filter.1 hZ).2
  refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, ?_⟩
  · have := hN.1.2.1 _ hZ'
    rwa [Finset.card_map] at this
  · refine mem_G22_of_dot fun H hH => ?_
    rw [dot_ind_ind, Finset.inter_comm]
    exact natCast_zmod2_eq_zero_iff.2 (even_map_hexad hN hZ' hH)

theorem card_O8 : (O8 𝒮).card = 330 := by
  have himg : (O8 𝒮).image (fun Z => Z.map ι) =
      𝒮.filter (fun B => (Sum.inr false : Pt) ∉ B ∧ (Sum.inr true : Pt) ∉ B) := by
    ext B
    simp only [Finset.mem_image, Finset.mem_filter, O8, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨Z, hZ, rfl⟩
      exact ⟨hZ, by simp [ι], by simp [ι]⟩
    · rintro ⟨hB, hp, hq⟩
      exact ⟨lift B, by rw [← eq_map_lift hp hq]; exact hB, (eq_map_lift hp hq).symm⟩
  rw [← Finset.card_image_of_injective _ (Finset.map_injective ι), himg]
  have hN1 := card_filter_lam hN.1 (j := 1) (by norm_num) (S := {Sum.inr false}) rfl
  have hN2 := card_filter_lam hN.1 (j := 1) (by norm_num) (S := {Sum.inr true}) rfl
  have hN12 := card_filter_lam hN.1 (j := 2) (by norm_num) (S := {Sum.inr false, Sum.inr true})
    (by simp)
  have hT := card_blocks hN.1
  simp only [lamNum, Finset.singleton_subset_iff, Finset.insert_subset_iff] at hN1 hN2 hN12
  have hU := Finset.card_union_add_card_inter (𝒮.filter (fun B => (Sum.inr false : Pt) ∈ B))
    (𝒮.filter (fun B => (Sum.inr true : Pt) ∈ B))
  rw [← Finset.filter_or, ← Finset.filter_and] at hU
  have hS := Finset.card_filter_add_card_filter_not (s := 𝒮)
    (fun B => (Sum.inr false : Pt) ∈ B ∨ (Sum.inr true : Pt) ∈ B)
  simp only [not_or] at hS
  omega

theorem O8_eq : O8 𝒮 = W8 :=
  Finset.eq_of_subset_of_card_le (O8_subset hN) (by rw [card_O8 hN, card_W8])

omit [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}] [CardHexads] [CardHexadAut] in
/-- Membership in a normalized design in terms of the two classes. -/
def Phi (Cf Ct : Set (Finset (Fin 22))) (B : Finset Pt) : Prop :=
  ((Sum.inr false : Pt) ∉ B ∧ (Sum.inr true : Pt) ∉ B ∧ lift B ∈ W8) ∨
  ((Sum.inr false : Pt) ∈ B ∧ (Sum.inr true : Pt) ∉ B ∧ lift B ∈ Cf) ∨
  ((Sum.inr false : Pt) ∉ B ∧ (Sum.inr true : Pt) ∈ B ∧ lift B ∈ Ct) ∨
  ((Sum.inr false : Pt) ∈ B ∧ (Sum.inr true : Pt) ∈ B ∧ lift B ∈ hexads)

theorem mem_iff (B : Finset Pt) :
    B ∈ 𝒮 ↔ Phi {Y | blk false Y ∈ 𝒮} {Y | blk true Y ∈ 𝒮} B := by
  constructor
  · intro hB
    by_cases hp : (Sum.inr false : Pt) ∈ B <;> by_cases hq : (Sum.inr true : Pt) ∈ B
    · exact Or.inr (Or.inr (Or.inr ⟨hp, hq, (hN.2 _).2 (by rw [← eq_hexBlk_lift hp hq]; exact hB)⟩))
    · exact Or.inr (Or.inl ⟨hp, hq, by
        show blk false (lift B) ∈ 𝒮
        rw [← eq_blk_false_lift hp hq]; exact hB⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hp, hq, by
        show blk true (lift B) ∈ 𝒮
        rw [← eq_blk_true_lift hp hq]; exact hB⟩))
    · refine Or.inl ⟨hp, hq, ?_⟩
      rw [← O8_eq hN]
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [← eq_map_lift hp hq]; exact hB⟩
  · rintro (⟨hp, hq, h⟩ | ⟨hp, hq, h⟩ | ⟨hp, hq, h⟩ | ⟨hp, hq, h⟩)
    · rw [eq_map_lift hp hq]
      rw [← O8_eq hN] at h
      exact (Finset.mem_filter.1 h).2
    · rw [eq_blk_false_lift hp hq]
      exact h
    · rw [eq_blk_true_lift hp hq]
      exact h
    · rw [eq_hexBlk_lift hp hq]
      exact (hN.2 _).1 h

end Normal

theorem seven_not_even : ¬ Even 7 := by decide

omit [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}] [CardHexads] [CardHexadAut] in
/-- Swapping the two extra points. -/
def swapPt : Equiv.Perm Pt := Equiv.swap (Sum.inr false) (Sum.inr true)

theorem mem_map_swap {B : Finset Pt} {x : Pt} : x ∈ B.map swapPt.toEmbedding ↔ swapPt x ∈ B := by
  rw [Finset.mem_map_equiv]
  simp [swapPt]

theorem lift_map_swap (B : Finset Pt) : lift (B.map swapPt.toEmbedding) = lift B := by
  ext a
  rw [mem_lift, mem_lift, mem_map_swap]
  simp [swapPt, Equiv.swap_apply_of_ne_of_ne]

section Two

variable {𝒮₁ 𝒮₂ : Finset (Finset Pt)} (h₁ : IsNormal 𝒮₁) (h₂ : IsNormal 𝒮₂)
include h₁ h₂

theorem class_or {e : Bool} {Z : Finset (Fin 22)} (hZ : IsOddSeven Z) {𝒮 : Finset (Finset Pt)}
    (hN : IsNormal 𝒮) : blk e Z ∈ 𝒮 ∨ blk (!e) Z ∈ 𝒮 := by
  cases e
  · exact oddSeven_mem_class hN hZ
  · exact (oddSeven_mem_class hN hZ).symm

theorem core {e : Bool} {Y₀ : Finset (Fin 22)} (hy1 : blk e Y₀ ∈ 𝒮₁) (hy2 : blk false Y₀ ∈ 𝒮₂)
    (Z : Finset (Fin 22)) :
    (blk false Z ∈ 𝒮₂ ↔ blk e Z ∈ 𝒮₁) ∧ (blk true Z ∈ 𝒮₂ ↔ blk (!e) Z ∈ 𝒮₁) := by
  have first : blk false Z ∈ 𝒮₂ ↔ blk e Z ∈ 𝒮₁ := by
    constructor
    · intro hz
      have hZ := isOddSeven_of_blk h₂ hz
      rcases class_or h₁ h₂ (e := e) hZ h₁ with h | h
      · exact h
      · exfalso
        exact Nat.not_even_iff_odd.2 (odd_blk_blk' h₂ hy2 hz) (even_cross h₁ hy1 h)
    · intro hz
      have hZ := isOddSeven_of_blk h₁ hz
      rcases oddSeven_mem_class h₂ hZ with h | h
      · exact h
      · exfalso
        exact Nat.not_even_iff_odd.2 (odd_blk_blk' h₁ hy1 hz) (even_cross h₂ (e := false) hy2 h)
  refine ⟨first, ?_⟩
  constructor
  · intro hz
    have hZ := isOddSeven_of_blk h₂ hz
    rcases class_or h₁ h₂ (e := e) hZ h₁ with h | h
    · exfalso
      have := (first).2 h
      have h' := even_blk_blk h₂ this hz
      rw [Finset.inter_self, card_of_blk h₂ hz] at h'
      exact seven_not_even h'
    · exact h
  · intro hz
    have hZ := isOddSeven_of_blk h₁ hz
    rcases oddSeven_mem_class h₂ hZ with h | h
    · exfalso
      have := (first).1 h
      have h' := even_cross h₁ (e := e) this hz
      rw [Finset.inter_self, card_of_blk h₁ hz] at h'
      exact seven_not_even h'
    · exact h

theorem classes :
    ({Y | blk false Y ∈ 𝒮₂} = {Y | blk false Y ∈ 𝒮₁} ∧
      {Y | blk true Y ∈ 𝒮₂} = {Y | blk true Y ∈ 𝒮₁}) ∨
    ({Y | blk false Y ∈ 𝒮₂} = {Y | blk true Y ∈ 𝒮₁} ∧
      {Y | blk true Y ∈ 𝒮₂} = {Y | blk false Y ∈ 𝒮₁}) := by
  obtain ⟨Y₀, hY₀⟩ := exists_class_false h₂
  rcases oddSeven_mem_class h₁ (isOddSeven_of_blk h₂ hY₀) with h | h
  · left
    have := core h₁ h₂ (e := false) h hY₀
    exact ⟨Set.ext fun Z => (this Z).1, Set.ext fun Z => (this Z).2⟩
  · right
    have := core h₁ h₂ (e := true) h hY₀
    exact ⟨Set.ext fun Z => (this Z).1, Set.ext fun Z => (this Z).2⟩

theorem iso_of_normal : ∃ σ : Equiv.Perm Pt, ∀ B, B ∈ 𝒮₁ ↔ B.map σ.toEmbedding ∈ 𝒮₂ := by
  rcases classes h₁ h₂ with ⟨hf, ht⟩ | ⟨hf, ht⟩
  · refine ⟨Equiv.refl _, fun B => ?_⟩
    rw [mem_iff h₁ B, mem_iff h₂ (B.map (Equiv.refl Pt).toEmbedding), hf, ht]
    simp
  · refine ⟨swapPt, fun B => ?_⟩
    rw [mem_iff h₁ B, mem_iff h₂ (B.map swapPt.toEmbedding), hf, ht, Phi, Phi, lift_map_swap]
    have e1 : (Sum.inr false : Pt) ∈ B.map swapPt.toEmbedding ↔ (Sum.inr true : Pt) ∈ B := by
      rw [mem_map_swap]; simp [swapPt]
    have e2 : (Sum.inr true : Pt) ∈ B.map swapPt.toEmbedding ↔ (Sum.inr false : Pt) ∈ B := by
      rw [mem_map_swap]; simp [swapPt]
    rw [e1, e2]
    constructor
    · rintro (⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩)
      · exact Or.inl ⟨b, a, c⟩
      · exact Or.inr (Or.inr (Or.inl ⟨b, a, c⟩))
      · exact Or.inr (Or.inl ⟨b, a, c⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨b, a, c⟩))
    · rintro (⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩)
      · exact Or.inl ⟨b, a, c⟩
      · exact Or.inr (Or.inr (Or.inl ⟨b, a, c⟩))
      · exact Or.inr (Or.inl ⟨b, a, c⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨b, a, c⟩))

end Two

end CFSGOutside.WittDesigns.Witt5824
