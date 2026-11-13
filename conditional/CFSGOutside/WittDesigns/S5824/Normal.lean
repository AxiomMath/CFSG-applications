import Mathlib
import CFSGOutside.WittDesigns.S5824.Code

/-!
Normal form of an `S(5,8,24)` on `Fin 22 ⊕ Bool` whose blocks through both points of `Bool` are the
hexads.
-/

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSGOutside.WittDesigns.Witt5824

open CFSGOutside.Corpus CFSGOutside.Corpus.WittDesign CFSGOutside.PlessSloaneG22

variable [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}] [CardHexads] [CardHexadAut]

omit [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}] [CardHexads] [CardHexadAut] in
abbrev Pt := Fin 22 ⊕ Bool

omit [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}] [CardHexads] [CardHexadAut] in
/-- The embedding of the 22 points. -/
def ι : Fin 22 ↪ Pt := Function.Embedding.inl

omit [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}] [CardHexads] [CardHexadAut] in
/-- The block through the point `inr e` with the 22-point part `Y`. -/
def blk (e : Bool) (Y : Finset (Fin 22)) : Finset Pt := insert (Sum.inr e) (Y.map ι)

omit [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}] [CardHexads] [CardHexadAut] in
/-- The block through both extra points with 22-point part `H`. -/
def hexBlk (H : Finset (Fin 22)) : Finset Pt := insert (Sum.inr false) (blk true H)

omit [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}] [CardHexads] [CardHexadAut] in
/-- The 22-point part of a block. -/
noncomputable def lift (B : Finset Pt) : Finset (Fin 22) := B.preimage Sum.inl Sum.inl_injective.injOn

theorem mem_map_ι {a : Fin 22} {Y : Finset (Fin 22)} : Sum.inl a ∈ Y.map ι ↔ a ∈ Y := by
  simp [ι]

theorem inr_notMem_map_ι {e : Bool} {Y : Finset (Fin 22)} : Sum.inr e ∉ Y.map ι := by
  simp [ι]

theorem mem_lift {B : Finset Pt} {a : Fin 22} : a ∈ lift B ↔ Sum.inl a ∈ B := by
  simp [lift]

theorem card_blk (e : Bool) (Y : Finset (Fin 22)) : (blk e Y).card = Y.card + 1 := by
  rw [blk, Finset.card_insert_of_notMem inr_notMem_map_ι, Finset.card_map]

theorem blk_inter_blk_same (e : Bool) (Y Y' : Finset (Fin 22)) :
    blk e Y ∩ blk e Y' = insert (Sum.inr e) ((Y ∩ Y').map ι) := by
  ext x
  rcases x with a | b
  · simp [blk, ι]
  · cases b <;> cases e <;> simp [blk, ι]

theorem blk_inter_blk_ne (Y Y' : Finset (Fin 22)) :
    blk false Y ∩ blk true Y' = (Y ∩ Y').map ι := by
  ext x
  rcases x with a | b
  · simp [blk, ι]
  · cases b <;> simp [blk, ι]

theorem blk_inter_hexBlk (e : Bool) (Y H : Finset (Fin 22)) :
    blk e Y ∩ hexBlk H = insert (Sum.inr e) ((Y ∩ H).map ι) := by
  ext x
  rcases x with a | b
  · simp [blk, hexBlk, ι]
  · cases b <;> cases e <;> simp [blk, hexBlk, ι]

theorem map_inter_hexBlk (Z H : Finset (Fin 22)) :
    Z.map ι ∩ hexBlk H = (Z ∩ H).map ι := by
  ext x
  rcases x with a | b
  · simp [blk, hexBlk, ι]
  · cases b <;> simp [blk, hexBlk, ι]

theorem blk_ne_hexBlk (e : Bool) (Y H : Finset (Fin 22)) : blk e Y ≠ hexBlk H := by
  intro h
  have : (Sum.inr (!e) : Pt) ∈ hexBlk H := by cases e <;> simp [hexBlk, blk]
  rw [← h] at this
  cases e <;> simp [blk, ι] at this

theorem map_ne_hexBlk (Z H : Finset (Fin 22)) : Z.map ι ≠ hexBlk H := by
  intro h
  have : (Sum.inr false : Pt) ∈ hexBlk H := by simp [hexBlk]
  rw [← h] at this
  simp [ι] at this

theorem blk_false_ne_blk_true (Y Y' : Finset (Fin 22)) : blk false Y ≠ blk true Y' := by
  intro h
  have : (Sum.inr false : Pt) ∈ blk false Y := by simp [blk]
  rw [h] at this
  simp [blk, ι] at this

theorem blk_injective (e : Bool) : Function.Injective (blk e) := by
  intro Y Y' h
  ext a
  have := congrArg (fun B : Finset Pt => Sum.inl a ∈ B) h
  simpa [blk, ι] using this

theorem decomp (B : Finset Pt) :
    (Sum.inr false ∉ B ∧ Sum.inr true ∉ B ∧ B = (lift B).map ι) ∨
    (Sum.inr false ∈ B ∧ Sum.inr true ∉ B ∧ B = blk false (lift B)) ∨
    (Sum.inr false ∉ B ∧ Sum.inr true ∈ B ∧ B = blk true (lift B)) ∨
    (Sum.inr false ∈ B ∧ Sum.inr true ∈ B ∧ B = hexBlk (lift B)) := by
  by_cases hp : (Sum.inr false : Pt) ∈ B <;> by_cases hq : (Sum.inr true : Pt) ∈ B
  · right; right; right
    refine ⟨hp, hq, ?_⟩
    ext x; rcases x with a | b
    · simp [hexBlk, blk, ι, mem_lift]
    · cases b <;> simp [hexBlk, blk, ι, hp, hq]
  · right; left
    refine ⟨hp, hq, ?_⟩
    ext x; rcases x with a | b
    · simp [blk, ι, mem_lift]
    · cases b <;> simp [blk, ι, hp, hq]
  · right; right; left
    refine ⟨hp, hq, ?_⟩
    ext x; rcases x with a | b
    · simp [blk, ι, mem_lift]
    · cases b <;> simp [blk, ι, hp, hq]
  · left
    refine ⟨hp, hq, ?_⟩
    ext x; rcases x with a | b
    · simp [ι, mem_lift]
    · cases b <;> simp [ι, hp, hq]

omit [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}] [CardHexads] [CardHexadAut] in
/-- A normalized `S(5,8,24)`: the blocks through both extra points are the hexads. -/
def IsNormal (𝒮 : Finset (Finset Pt)) : Prop :=
  IsSteiner5 𝒮 ∧ ∀ H : Finset (Fin 22), H ∈ hexads ↔ hexBlk H ∈ 𝒮

section Normal

variable {𝒮 : Finset (Finset Pt)} (hN : IsNormal 𝒮)
include hN

theorem card_of_blk {e : Bool} {Y : Finset (Fin 22)} (h : blk e Y ∈ 𝒮) : Y.card = 7 := by
  have := hN.1.2.1 _ h
  rw [card_blk] at this
  omega

theorem odd_blk_hexad {e : Bool} {Y H : Finset (Fin 22)} (h : blk e Y ∈ 𝒮) (hH : H ∈ hexads) :
    Odd (Y ∩ H).card := by
  have he := even_card_inter hN.1 h ((hN.2 H).1 hH) (blk_ne_hexBlk e Y H)
  rw [blk_inter_hexBlk, Finset.card_insert_of_notMem inr_notMem_map_ι, Finset.card_map] at he
  rcases he with ⟨k, hk⟩
  exact ⟨k - 1, by omega⟩

theorem isOddSeven_of_blk {e : Bool} {Y : Finset (Fin 22)} (h : blk e Y ∈ 𝒮) : IsOddSeven Y :=
  ⟨card_of_blk hN h, fun _ hH => odd_blk_hexad hN h hH⟩

theorem odd_blk_blk {e : Bool} {Y Y' : Finset (Fin 22)} (h : blk e Y ∈ 𝒮) (h' : blk e Y' ∈ 𝒮)
    (hne : Y ≠ Y') : Odd (Y ∩ Y').card := by
  have he := even_card_inter hN.1 h h' (fun h => hne (blk_injective e h))
  rw [blk_inter_blk_same, Finset.card_insert_of_notMem inr_notMem_map_ι, Finset.card_map] at he
  rcases he with ⟨k, hk⟩
  exact ⟨k - 1, by omega⟩

theorem even_blk_blk {Y Y' : Finset (Fin 22)} (h : blk false Y ∈ 𝒮) (h' : blk true Y' ∈ 𝒮) :
    Even (Y ∩ Y').card := by
  have he := even_card_inter hN.1 h h' (blk_false_ne_blk_true Y Y')
  rwa [blk_inter_blk_ne, Finset.card_map] at he

theorem even_map_hexad {Z H : Finset (Fin 22)} (h : Z.map ι ∈ 𝒮) (hH : H ∈ hexads) :
    Even (Z ∩ H).card := by
  have he := even_card_inter hN.1 h ((hN.2 H).1 hH) (fun e => map_ne_hexBlk Z H e)
  rwa [map_inter_hexBlk, Finset.card_map] at he

end Normal

end CFSGOutside.WittDesigns.Witt5824
