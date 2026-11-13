import Mathlib
import CFSGOutside.WittDesigns.AutS5824.Transport

/-!
The automorphism group of a normalized `S(5,8,24)`: it is transitive on the 276 pairs of points, and
the stabilizer of the pair of extra points is isomorphic to the automorphism group of the hexads.
-/

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSGOutside.WittDesigns.Aut5824

open CFSGOutside.Corpus CFSGOutside.Corpus.WittDesign CFSGOutside.PlessSloaneG22 CFSGOutside.WittDesigns.Witt5824
open scoped Pointwise
attribute [local instance] Classical.propDecidable

variable [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}] [CardHexads] [CardHexadAut]

omit [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}] [CardHexads] [CardHexadAut] in
/-- The two extra points. -/
abbrev P0 : Finset Pt := {Sum.inr false, Sum.inr true}

theorem card_P0 : P0.card = 2 := by decide

theorem smul_eq_map (σ : Equiv.Perm Pt) (s : Finset Pt) : σ • s = s.map σ.toEmbedding := by
  rw [Finset.smul_finset_def, Finset.map_eq_image]
  rfl

theorem map_P0 {σ : Equiv.Perm Pt} (hσ : ∀ i, σ (Sum.inl i) = Sum.inl i) :
    P0.map σ.toEmbedding = P0 := by
  refine Finset.eq_of_subset_of_card_le ?_ (by rw [Finset.card_map])
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hy
  have hx' : x = Sum.inr false ∨ x = Sum.inr true := by simpa [P0] using hx
  show σ x ∈ P0
  rcases h : σ x with j | c
  · exfalso
    have := σ.injective ((hσ j).trans h.symm)
    rcases hx' with rfl | rfl <;> cases this
  · cases c <;> simp [P0]

theorem hexBlk_eq (H : Finset (Fin 22)) : hexBlk H = P0 ∪ H.map ι := by
  ext x
  simp [hexBlk, blk, P0, or_assoc]

theorem hexBlk_map_ext (a : Equiv.Perm (Fin 22)) (H : Finset (Fin 22)) :
    (hexBlk H).map (Equiv.Perm.sumCongr a (Equiv.refl Bool)).toEmbedding =
      hexBlk (H.map a.toEmbedding) := by
  ext x
  rw [Finset.mem_map_equiv]
  rcases x with i | b
  · simp [hexBlk, blk, ι, Finset.mem_map_equiv]
  · cases b <;> simp [hexBlk, blk, ι]

section Count

variable {𝒮 : Finset (Finset Pt)} (hN : IsNormal 𝒮)
include hN

theorem swapPt_not_mem : swapPt ∉ blockAut 𝒮 := by
  intro hmem
  obtain ⟨Y, hY⟩ := exists_class_false hN
  have h1 := (mem_blockAut.1 hmem (blk false Y)).2 hY
  have h2 : (blk false Y).map swapPt.toEmbedding = blk true Y := by
    ext x
    rw [mem_map_swap]
    rcases x with a | b
    · simp [blk, ι, swapPt, Equiv.swap_apply_of_ne_of_ne]
    · cases b <;> simp [blk, ι, swapPt]
  rw [h2] at h1
  have := even_blk_blk hN hY h1
  rw [Finset.inter_self, card_of_blk hN hY] at this
  exact seven_not_even this

theorem eq_one_of_fix {σ : Equiv.Perm Pt} (hσ : σ ∈ blockAut 𝒮)
    (hfix : ∀ i, σ (Sum.inl i) = Sum.inl i) : σ = 1 := by
  have hinr : ∀ b, ∃ c, σ (Sum.inr b) = Sum.inr c := by
    intro b
    rcases h : σ (Sum.inr b) with a | c
    · exfalso
      have := σ.injective ((hfix a).trans h.symm)
      cases this
    · exact ⟨c, rfl⟩
  obtain ⟨c, hc⟩ := hinr false
  obtain ⟨c', hc'⟩ := hinr true
  have hne : c ≠ c' := by
    intro e
    rw [e] at hc
    exact absurd (σ.injective (hc.trans hc'.symm)) (by simp)
  by_cases hF : c = false
  · have hT : c' = true := by
      subst hF
      cases c' <;> simp_all
    subst hF; subst hT
    ext x
    rcases x with i | b
    · simp [hfix]
    · cases b <;> simp [hc, hc']
  · exfalso
    have hc1 : c = true := by cases c <;> simp_all
    have hc2 : c' = false := by cases c' <;> simp_all
    subst hc1; subst hc2
    apply swapPt_not_mem hN
    have : σ = swapPt := by
      ext x
      rcases x with i | b
      · simp [hfix, swapPt, Equiv.swap_apply_of_ne_of_ne]
      · cases b <;> simp [hc, hc', swapPt]
    rw [← this]
    exact hσ

theorem exists_inl {g : Equiv.Perm Pt} (hg : P0.map g.toEmbedding = P0) (i : Fin 22) :
    ∃ j, g (Sum.inl i) = Sum.inl j := by
  rcases h : g (Sum.inl i) with j | y
  · exact ⟨j, rfl⟩
  · exfalso
    have hy : (Sum.inr y : Pt) ∈ P0 := by cases y <;> simp [P0]
    rw [← hg] at hy
    obtain ⟨x, hx, hxy⟩ := Finset.mem_map.1 hy
    have hx' : g x = Sum.inr y := hxy
    have : x = Sum.inl i := g.injective (hx'.trans h.symm)
    rw [this] at hx
    simp [P0] at hx

end Count

end CFSGOutside.WittDesigns.Aut5824
