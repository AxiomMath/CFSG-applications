import Mathlib
import CFSGOutside.WittDesigns.S5824.Iso

/-!
# Witt (1938): the Steiner system `S(5,8,24)` is unique

Any two Steiner systems `S(5,8,24)` are isomorphic. The proof reduces to the corpus theorem on the
uniqueness of `S(3,6,22)` (`steinerTriple_iso`) applied to the system derived at two points.
-/

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

universe u v

namespace CFSGOutside.WittDesigns.Witt5824

open CFSGOutside.Corpus CFSGOutside.Corpus.WittDesign CFSGOutside.PlessSloaneG22
attribute [local instance] Classical.propDecidable

section Transport

variable {Ω : Type u} {Ω' : Type v} [Fintype Ω] [DecidableEq Ω] [Fintype Ω'] [DecidableEq Ω']

theorem mem_image_map {𝒮 : Finset (Finset Ω)} (φ : Ω ≃ Ω') {X : Finset Ω'} :
    X ∈ 𝒮.image (fun B => B.map φ.toEmbedding) ↔ X.map φ.symm.toEmbedding ∈ 𝒮 := by
  constructor
  · rintro hX
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.1 hX
    simpa [Finset.map_map] using hB
  · intro hX
    exact Finset.mem_image.2 ⟨_, hX, by simp [Finset.map_map]⟩

theorem IsSteiner5.image {𝒮 : Finset (Finset Ω)} (h : IsSteiner5 𝒮) (φ : Ω ≃ Ω') :
    IsSteiner5 (𝒮.image fun B => B.map φ.toEmbedding) := by
  refine ⟨by rw [← Fintype.card_congr φ]; exact h.1, ?_, ?_⟩
  · intro X hX
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.1 hX
    rw [Finset.card_map]; exact h.2.1 B hB
  · intro T hT
    obtain ⟨B, ⟨hB, hTB⟩, hu⟩ := h.2.2 (T.map φ.symm.toEmbedding) (by rw [Finset.card_map]; exact hT)
    refine ⟨B.map φ.toEmbedding, ⟨Finset.mem_image.2 ⟨B, hB, rfl⟩, ?_⟩, ?_⟩
    · intro x hx
      exact Finset.mem_map_equiv.2 (hTB (Finset.mem_map.2 ⟨x, hx, rfl⟩))
    · rintro X ⟨hX, hTX⟩
      have hX' := (mem_image_map φ).1 hX
      have := hu (X.map φ.symm.toEmbedding) ⟨hX', by
        intro y hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hy
        exact Finset.mem_map.2 ⟨x, hTX hx, rfl⟩⟩
      rw [← this]
      simp [Finset.map_map]

end Transport

section Normalize

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]

/-- The points other than `p` and `q`. -/
abbrev Rest (p q : Ω) := {x : Ω // x ≠ p ∧ x ≠ q}

/-- The blocks through `p` and `q`, with those points removed. -/
def derived (p q : Ω) (𝒮 : Finset (Finset Ω)) : Finset (Finset (Rest p q)) :=
  Finset.univ.filter fun H => insert p (insert q (H.map (Function.Embedding.subtype _))) ∈ 𝒮

theorem card_rest {p q : Ω} (hpq : p ≠ q) (hΩ : Fintype.card Ω = 24) :
    Fintype.card (Rest p q) = 22 := by
  rw [Fintype.card_subtype]
  have : Finset.univ.filter (fun x : Ω => x ≠ p ∧ x ≠ q) = Finset.univ \ {p, q} := by
    ext x; simp
  rw [this, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hΩ,
    Finset.card_pair hpq]

theorem eq_insert_subtype {p q : Ω} {B : Finset Ω} (hp : p ∈ B) (hq : q ∈ B) :
    B = insert p (insert q ((B.subtype fun x => x ≠ p ∧ x ≠ q).map (Function.Embedding.subtype _))) := by
  ext x
  by_cases hxp : x = p
  · simp [hxp, hp]
  by_cases hxq : x = q
  · simp [hxq, hq]
  simp [hxp, hxq]

theorem card_insert_two {p q : Ω} (hpq : p ≠ q) (H : Finset (Rest p q)) :
    (insert p (insert q (H.map (Function.Embedding.subtype _)))).card = H.card + 2 := by
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_map]
  · simp
  · simp [hpq]

theorem isSteinerTriple_derived {𝒮 : Finset (Finset Ω)} (h : IsSteiner5 𝒮) {p q : Ω}
    (hpq : p ≠ q) : IsSteinerTriple (derived p q 𝒮) := by
  refine ⟨card_rest hpq h.1, ?_, ?_⟩
  · intro H hH
    have := h.2.1 _ (Finset.mem_filter.1 hH).2
    rw [card_insert_two hpq] at this
    omega
  · intro T hT
    obtain ⟨B, ⟨hB, hTB⟩, hu⟩ := h.2.2
      (insert p (insert q (T.map (Function.Embedding.subtype _)))) (by
        rw [card_insert_two hpq, hT])
    have hpB : p ∈ B := hTB (by simp)
    have hqB : q ∈ B := hTB (by simp)
    refine ⟨B.subtype fun x => x ≠ p ∧ x ≠ q, ⟨?_, ?_⟩, ?_⟩
    · refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      rw [← eq_insert_subtype hpB hqB]; exact hB
    · intro x hx
      exact Finset.mem_subtype.2 (hTB (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_map.2 ⟨x, hx, rfl⟩))))
    · rintro H' ⟨hH', hTH'⟩
      have hH'B := (Finset.mem_filter.1 hH').2
      have := hu _ ⟨hH'B, by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_map, Function.Embedding.coe_subtype] at hx ⊢
        rcases hx with rfl | rfl | ⟨y, hy, rfl⟩
        · simp
        · simp
        · right; right; exact ⟨y, hTH' hy, rfl⟩⟩
      ext y
      have h2 := congrArg (fun C : Finset Ω => y.1 ∈ C) this
      simpa [y.2.1, y.2.2, Finset.mem_subtype] using h2

end Normalize


section Build

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]

/-- The bijection sending `p`, `q` to the two extra points and the rest through `e`. -/
noncomputable def toPt {p q : Ω} (hpq : p ≠ q) (e : Rest p q ≃ Fin 22) : Ω ≃ Pt where
  toFun x := if hp : x = p then Sum.inr false else if hq : x = q then Sum.inr true
    else Sum.inl (e ⟨x, hp, hq⟩)
  invFun
    | Sum.inl a => (e.symm a).1
    | Sum.inr false => p
    | Sum.inr true => q
  left_inv x := by
    by_cases hp : x = p
    · simp [hp]
    by_cases hq : x = q
    · simp [hq, Ne.symm hpq]
    · simp [hp, hq]
  right_inv y := by
    rcases y with a | b
    · have := (e.symm a).2
      simp [this.1, this.2]
    · cases b <;> simp [hpq, Ne.symm hpq]

theorem toPt_p {p q : Ω} (hpq : p ≠ q) (e : Rest p q ≃ Fin 22) : toPt hpq e p = Sum.inr false := by
  simp [toPt]

theorem toPt_q {p q : Ω} (hpq : p ≠ q) (e : Rest p q ≃ Fin 22) : toPt hpq e q = Sum.inr true := by
  simp [toPt, Ne.symm hpq]

theorem toPt_rest {p q : Ω} (hpq : p ≠ q) (e : Rest p q ≃ Fin 22) (x : Rest p q) :
    toPt hpq e x.1 = Sum.inl (e x) := by
  simp [toPt, x.2.1, x.2.2]

variable [IsSteinerTripleHexads] [SteinerTripleIso.{u, 0}] in
theorem exists_normal {𝒮 : Finset (Finset Ω)} (h : IsSteiner5 𝒮) :
    ∃ φ : Ω ≃ Pt, IsNormal (𝒮.image fun B => B.map φ.toEmbedding) := by
  obtain ⟨p, q, hpq⟩ := Fintype.one_lt_card_iff.1 (by rw [h.1]; norm_num : 1 < Fintype.card Ω)
  obtain ⟨e, he⟩ := SteinerTripleIso.steinerTriple_iso (isSteinerTriple_derived h hpq) IsSteinerTripleHexads.isSteinerTriple_hexads
  refine ⟨toPt hpq e, h.image _, fun H => ?_⟩
  rw [mem_image_map]
  have key : (hexBlk H).map (toPt hpq e).symm.toEmbedding =
      insert p (insert q ((H.map e.symm.toEmbedding).map (Function.Embedding.subtype _))) := by
    ext x
    rw [Finset.mem_map_equiv, Equiv.symm_symm]
    by_cases hxp : x = p
    · subst hxp; simp [toPt_p, hexBlk]
    by_cases hxq : x = q
    · subst hxq; simp [toPt_q, hexBlk, blk]
    · have hx : toPt hpq e x = Sum.inl (e ⟨x, hxp, hxq⟩) := toPt_rest hpq e ⟨x, hxp, hxq⟩
      rw [hx]
      simp [hexBlk, blk, ι, hxp, hxq]
  rw [key]
  have hH : (H.map e.symm.toEmbedding).map e.toEmbedding = H := by simp [Finset.map_map]
  have := he (H.map e.symm.toEmbedding)
  rw [hH] at this
  rw [← this, derived, Finset.mem_filter]
  simp

end Build

variable [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}] [CardHexads] [CardHexadAut] in
/-- **Witt (1938).** Any two Steiner systems `S(5,8,24)` are isomorphic. -/
theorem witt_S5824_unique {Ω : Type u} {Ω' : Type v} [SteinerTripleIso.{u, 0}] [SteinerTripleIso.{v, 0}]
    [Fintype Ω] [DecidableEq Ω] [Fintype Ω']
    [DecidableEq Ω'] {𝒮 : Finset (Finset Ω)} {𝒮' : Finset (Finset Ω')} (h : IsSteiner5 𝒮)
    (h' : IsSteiner5 𝒮') :
    ∃ f : Ω ≃ Ω', ∀ B : Finset Ω, B ∈ 𝒮 ↔ B.map f.toEmbedding ∈ 𝒮' := by
  obtain ⟨φ, hφ⟩ := exists_normal h
  obtain ⟨φ', hφ'⟩ := exists_normal h'
  obtain ⟨σ, hσ⟩ := iso_of_normal hφ hφ'
  refine ⟨φ.trans (σ.trans φ'.symm), fun B => ?_⟩
  have h1 : B ∈ 𝒮 ↔ B.map φ.toEmbedding ∈ 𝒮.image fun B => B.map φ.toEmbedding := by
    rw [mem_image_map]; simp [Finset.map_map]
  rw [h1, hσ]
  have h2 := mem_image_map (𝒮 := 𝒮') φ' (X := (B.map φ.toEmbedding).map σ.toEmbedding)
  rw [h2]
  simp [Finset.map_map]
  rfl

end CFSGOutside.WittDesigns.Witt5824
