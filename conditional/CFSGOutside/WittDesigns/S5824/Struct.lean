import Mathlib
import CFSGOutside.WittDesigns.S5824.Normal

/-!
Structure of a normalized `S(5,8,24)`: its blocks through exactly one extra point form two classes
of seven-sets that are determined by the hexads up to exchange.
-/

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSGOutside.WittDesigns.Witt5824

open CFSGOutside.Corpus CFSGOutside.Corpus.WittDesign CFSGOutside.PlessSloaneG22
open scoped Matrix

variable [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}] [CardHexads] [CardHexadAut]

theorem eq_hexBlk_lift {B : Finset Pt} (hp : (Sum.inr false : Pt) ∈ B) (hq : (Sum.inr true : Pt) ∈ B) :
    B = hexBlk (lift B) := by
  ext x; rcases x with a | b
  · simp [hexBlk, blk, ι, mem_lift]
  · cases b <;> simp [hexBlk, blk, ι, hp, hq]

theorem eq_blk_false_lift {B : Finset Pt} (hp : (Sum.inr false : Pt) ∈ B)
    (hq : (Sum.inr true : Pt) ∉ B) : B = blk false (lift B) := by
  ext x; rcases x with a | b
  · simp [blk, ι, mem_lift]
  · cases b <;> simp [blk, ι, hp, hq]

theorem eq_blk_true_lift {B : Finset Pt} (hp : (Sum.inr false : Pt) ∉ B)
    (hq : (Sum.inr true : Pt) ∈ B) : B = blk true (lift B) := by
  ext x; rcases x with a | b
  · simp [blk, ι, mem_lift]
  · cases b <;> simp [blk, ι, hp, hq]

theorem eq_map_lift {B : Finset Pt} (hp : (Sum.inr false : Pt) ∉ B)
    (hq : (Sum.inr true : Pt) ∉ B) : B = (lift B).map ι := by
  ext x; rcases x with a | b
  · simp [ι, mem_lift]
  · cases b <;> simp [ι, hp, hq]

theorem card_hexads_through (z : Fin 22) : (hexads.filter (z ∈ ·)).card = 21 := by
  have hk : ∀ H ∈ hexads, H.card = 6 := fun H h => card_of_mem_hexads h
  have h3 : ∀ S : Finset (Fin 22), S.card = 3 → (hexads.filter (S ⊆ ·)).card = 1 := by
    intro S hS
    obtain ⟨B, ⟨hB, hSB⟩, hu⟩ := IsSteinerTripleHexads.isSteinerTriple_hexads.2.2 S hS
    rw [Finset.card_eq_one]
    refine ⟨B, ?_⟩
    ext B'
    simp only [Finset.mem_filter, Finset.mem_singleton]
    exact ⟨fun ⟨a, b⟩ => hu B' ⟨a, b⟩, fun e => e ▸ ⟨hB, hSB⟩⟩
  have h2 : ∀ S : Finset (Fin 22), S.card = 2 → (hexads.filter (S ⊆ ·)).card = 5 := by
    intro S hS
    have := card_filter_succ (i := 2) (c := 1) hk (Fintype.card_fin 22) h3 hS
    omega
  have h1 := card_filter_succ (i := 1) (c := 5) hk (Fintype.card_fin 22) h2
    (S := {z}) (Finset.card_singleton z)
  simp only [Finset.singleton_subset_iff] at h1
  omega

theorem exists_hexad_disjoint {Z : Finset (Fin 22)} (hZ : Z.card ≤ 3) :
    ∃ H ∈ hexads, Disjoint H Z := by
  by_contra hno
  push_neg at hno
  have hsub : hexads ⊆ Z.biUnion fun z => hexads.filter (z ∈ ·) := by
    intro H hH
    obtain ⟨z, hzH, hzZ⟩ := Finset.not_disjoint_iff.1 (hno H hH)
    exact Finset.mem_biUnion.2 ⟨z, hzZ, Finset.mem_filter.2 ⟨hH, hzH⟩⟩
  have := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  rw [Finset.sum_congr rfl fun z _ => card_hexads_through z, Finset.sum_const, smul_eq_mul,
    CardHexads.card_hexads] at this
  omega

section Normal

variable {𝒮 : Finset (Finset Pt)} (hN : IsNormal 𝒮)
include hN

theorem exists_near {X : Finset (Fin 22)} (hX : IsOddSeven X) (e : Bool) :
    ∃ Y, blk e Y ∈ 𝒮 ∧ 4 ≤ (X ∩ Y).card := by
  obtain ⟨Q, hQX, hQ⟩ := Finset.exists_subset_card_eq (show 4 ≤ X.card by rw [hX.1]; norm_num)
  obtain ⟨O, ⟨hO, hTO⟩, -⟩ := hN.1.2.2 (blk e Q) (by rw [card_blk, hQ])
  have he : (Sum.inr e : Pt) ∈ O := hTO (by simp [blk])
  have hQO : ∀ a ∈ Q, a ∈ lift O := fun a ha => mem_lift.2 (hTO (by simp [blk, ι, ha]))
  by_cases hb : (Sum.inr (!e) : Pt) ∈ O
  · exfalso
    have hpq : (Sum.inr false : Pt) ∈ O ∧ (Sum.inr true : Pt) ∈ O := by
      cases e <;> simp_all
    have hOe := eq_hexBlk_lift hpq.1 hpq.2
    have hH : lift O ∈ hexads := (hN.2 _).2 (by rw [← hOe]; exact hO)
    have h4 : 4 ≤ (X ∩ lift O).card := by
      rw [← hQ]
      exact Finset.card_le_card fun a ha => Finset.mem_inter.2 ⟨hQX ha, hQO a ha⟩
    have h6 : (X ∩ lift O).card ≤ 6 := by
      rw [← card_of_mem_hexads hH]
      exact Finset.card_le_card Finset.inter_subset_right
    have hodd := hX.2 _ hH
    have h5 : (X ∩ lift O).card = 5 := by
      rcases hodd with ⟨k, hk⟩
      omega
    have hw := wt_add_add (ind X) (ind (lift O))
    rw [supp_ind, supp_ind, h5] at hw
    have hX7 : wt (ind X) = 7 := by rw [wt, supp_ind, hX.1]
    have hH6 : wt (ind (lift O)) = 6 := by rw [wt, supp_ind, card_of_mem_hexads hH]
    obtain ⟨H', hH', hdis⟩ := exists_hexad_disjoint (Z := supp (ind X + ind (lift O)))
      (by rw [← wt]; omega)
    have h0 : ind H' ⬝ᵥ (ind X + ind (lift O)) = 0 := by
      rw [dot_eq_card, supp_ind]
      simp [Finset.disjoint_iff_inter_eq_empty.1 hdis]
    rw [dotProduct_add, dot_ind_ind, dot_ind_hexads hH' hH, Finset.inter_comm H' X,
      natCast_zmod2_eq_one_iff.2 (hX.2 H' hH')] at h0
    revert h0
    decide
  · refine ⟨lift O, ?_, ?_⟩
    · have : O = blk e (lift O) := by
        cases e
        · exact eq_blk_false_lift he (by simpa using hb)
        · exact eq_blk_true_lift (by simpa using hb) he
      rw [← this]; exact hO
    · rw [← hQ]
      exact Finset.card_le_card fun a ha => Finset.mem_inter.2 ⟨hQX ha, hQO a ha⟩

theorem odd_blk_blk' {e : Bool} {Y Y' : Finset (Fin 22)} (h : blk e Y ∈ 𝒮) (h' : blk e Y' ∈ 𝒮) :
    Odd (Y ∩ Y').card := by
  by_cases hne : Y = Y'
  · subst hne; rw [Finset.inter_self, card_of_blk hN h]; decide
  · exact odd_blk_blk hN h h' hne

theorem even_cross {e : Bool} {Y Y' : Finset (Fin 22)} (h : blk e Y ∈ 𝒮)
    (h' : blk (!e) Y' ∈ 𝒮) : Even (Y ∩ Y').card := by
  cases e
  · exact even_blk_blk hN h h'
  · rw [Finset.inter_comm]; exact even_blk_blk hN h' h

theorem oddSeven_mem_class {X : Finset (Fin 22)} (hX : IsOddSeven X) :
    blk false X ∈ 𝒮 ∨ blk true X ∈ 𝒮 := by
  obtain ⟨Y, hY, hY4⟩ := exists_near hN hX false
  obtain ⟨Y', hY', hY'4⟩ := exists_near hN hX true
  have hYo := isOddSeven_of_blk hN hY
  have hYo' := isOddSeven_of_blk hN hY'
  by_cases hXY : X = Y
  · subst hXY; exact Or.inl hY
  by_cases hXY' : X = Y'
  · subst hXY'; exact Or.inr hY'
  exfalso
  have a1 := card_inter_le_four hX hYo hXY
  have a2 := card_inter_le_four hX hYo' hXY'
  have := odd_inter_of_even_inter hX hYo hYo' ⟨2, by omega⟩ ⟨2, by omega⟩
  exact (Nat.not_even_iff_odd.2 this) (even_blk_blk hN hY hY')

theorem exists_class_false : ∃ Y, blk false Y ∈ 𝒮 := by
  have h1 := card_filter_lam hN.1 (j := 1) (by norm_num) (S := {Sum.inr false}) rfl
  have h2 := card_filter_lam hN.1 (j := 2) (by norm_num) (S := {Sum.inr false, Sum.inr true})
    (by simp)
  simp only [lamNum] at h1 h2
  by_contra hno
  push_neg at hno
  have hsub : 𝒮.filter ({Sum.inr false} ⊆ ·) ⊆ 𝒮.filter ({Sum.inr false, Sum.inr true} ⊆ ·) := by
    intro B hB
    obtain ⟨hB, hp⟩ := Finset.mem_filter.1 hB
    have hp' : (Sum.inr false : Pt) ∈ B := hp (by simp)
    refine Finset.mem_filter.2 ⟨hB, ?_⟩
    by_cases hq : (Sum.inr true : Pt) ∈ B
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    · exfalso
      exact hno (lift B) (by rw [← eq_blk_false_lift hp' hq]; exact hB)
  have := Finset.card_le_card hsub
  omega

end Normal

end CFSGOutside.WittDesigns.Witt5824
