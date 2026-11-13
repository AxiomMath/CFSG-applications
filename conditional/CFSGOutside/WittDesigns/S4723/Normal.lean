import Mathlib
import CFSGOutside.WittDesigns.S4723.Design
import CFSGOutside.WittDesigns.S4723.Parity

/-!
A normalized `S(4,7,23)`: the blocks through the point `Q` are the hexads. Its other blocks form one
whole `Kin`-class of odd heptads.
-/

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

universe u v

namespace CFSGOutside.WittDesigns.Witt4723

open CFSGOutside.Corpus CFSGOutside.Corpus.WittDesign
open CFSGOutside.WittDesigns.Witt5824 (IsOddSeven card_inter_le_four)
attribute [local instance] Classical.propDecidable

variable [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}] [CardHexads] [CardHexadAut]

omit [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}] [CardHexads] [CardHexadAut] in
abbrev P23 := Fin 22 ⊕ Unit

omit [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}] [CardHexads] [CardHexadAut] in
def ι : Fin 22 ↪ P23 := Function.Embedding.inl

omit [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}] [CardHexads] [CardHexadAut] in
def Q : P23 := Sum.inr ()

omit [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}] [CardHexads] [CardHexadAut] in
noncomputable def lift (B : Finset P23) : Finset (Fin 22) := B.preimage Sum.inl Sum.inl_injective.injOn

theorem mem_map_ι {a : Fin 22} {Y : Finset (Fin 22)} : Sum.inl a ∈ Y.map ι ↔ a ∈ Y := by
  simp [ι]

theorem Q_notMem_map_ι {Y : Finset (Fin 22)} : Q ∉ Y.map ι := by
  simp [ι, Q]

theorem mem_lift {B : Finset P23} {a : Fin 22} : a ∈ lift B ↔ Sum.inl a ∈ B := by
  simp [lift]

theorem decomp_Q {B : Finset P23} (h : Q ∈ B) : B = insert Q ((lift B).map ι) := by
  ext x
  rcases x with a | u
  · simp [ι, mem_lift, Q]
  · cases u
    simpa [Q] using h

theorem decomp_noQ {B : Finset P23} (h : Q ∉ B) : B = (lift B).map ι := by
  ext x
  rcases x with a | u
  · simp [ι, mem_lift]
  · cases u
    simp only [ι, Finset.mem_map, Function.Embedding.inl_apply]
    simpa [Q] using h

omit [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}] [CardHexads] [CardHexadAut] in
/-- A normalized `S(4,7,23)`: the blocks through `Q` are the hexads. -/
def IsNormal (𝒯 : Finset (Finset P23)) : Prop :=
  IsSteiner4 𝒯 ∧ ∀ H : Finset (Fin 22), H ∈ hexads ↔ insert Q (H.map ι) ∈ 𝒯

theorem no_hexad_cover {Z : Finset (Fin 22)} (hZ : IsOddSeven Z) :
    ∃ S ⊆ Z, S.card = 4 ∧ ∀ H ∈ hexads, ¬ S ⊆ H := by
  by_contra hcon
  push Not at hcon
  have hcard6 : ∀ H ∈ hexads, H.card = 6 := fun H hH => IsSteinerTripleHexads.isSteinerTriple_hexads.2.1 H hH
  have h5 : ∀ H ∈ hexads, 4 ≤ (Z ∩ H).card → (Z ∩ H).card = 5 := by
    intro H hH h4
    have hodd := hZ.2 H hH
    have hle : (Z ∩ H).card ≤ 6 :=
      (Finset.card_le_card Finset.inter_subset_right).trans (hcard6 H hH).le
    obtain ⟨k, hk⟩ := hodd
    omega
  obtain ⟨S0, hS0Z, hS0c⟩ := Finset.exists_subset_card_eq (s := Z) (n := 4) (by rw [hZ.1]; norm_num)
  obtain ⟨H0, hH0, hS0H⟩ := hcon S0 hS0Z hS0c
  have hR : (Z ∩ H0).card = 5 := h5 H0 hH0 (by
    have := Finset.card_le_card (Finset.subset_inter hS0Z hS0H)
    omega)
  have hU : (Z \ H0).card = 2 := by
    have := Finset.card_sdiff_add_card_inter Z H0
    rw [hZ.1] at this
    omega
  obtain ⟨u, v, huv, hUeq⟩ := Finset.card_eq_two.1 hU
  obtain ⟨r1, hr1, r2, hr2, hr12⟩ := Finset.one_lt_card.1 (by omega : 1 < (Z ∩ H0).card)
  have hu : u ∈ Z \ H0 := by rw [hUeq]; simp
  have hv : v ∈ Z \ H0 := by rw [hUeq]; simp
  rw [Finset.mem_sdiff] at hu hv
  rw [Finset.mem_inter] at hr1 hr2
  have hr1u : r1 ≠ u := fun e => hu.2 (e ▸ hr1.2)
  have hr1v : r1 ≠ v := fun e => hv.2 (e ▸ hr1.2)
  have hr2u : r2 ≠ u := fun e => hu.2 (e ▸ hr2.2)
  have hr2v : r2 ≠ v := fun e => hv.2 (e ▸ hr2.2)
  set S' : Finset (Fin 22) := {r1, r2, u, v} with hS'
  have hS'c : S'.card = 4 := by
    rw [hS', Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair huv]
    · simp [hr2u, hr2v]
    · simp [hr12, hr1u, hr1v]
  have hS'Z : S' ⊆ Z := by
    intro x hx
    simp only [hS', Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hr1.1
    · exact hr2.1
    · exact hu.1
    · exact hv.1
  obtain ⟨H', hH', hS'H⟩ := hcon S' hS'Z hS'c
  have hR' : (Z ∩ H').card = 5 := h5 H' hH' (by
    have := Finset.card_le_card (Finset.subset_inter hS'Z hS'H)
    omega)
  have hw : ∃ w, w ∈ Z ∩ H' ∧ w ∉ S' := by
    by_contra hno
    push Not at hno
    have := Finset.card_le_card (show Z ∩ H' ⊆ S' from fun x hx => hno x hx)
    omega
  obtain ⟨w, hwZH, hwS⟩ := hw
  have hwr1 : w ≠ r1 := fun e => hwS (by simp [hS', e])
  have hwr2 : w ≠ r2 := fun e => hwS (by simp [hS', e])
  have hwu : w ≠ u := fun e => hwS (by simp [hS', e])
  have hwv : w ≠ v := fun e => hwS (by simp [hS', e])
  have hwH0 : w ∈ H0 := by
    by_contra hnot
    have : w ∈ Z \ H0 := Finset.mem_sdiff.2 ⟨(Finset.mem_inter.1 hwZH).1, hnot⟩
    rw [hUeq] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h
    · exact hwu h
    · exact hwv h
  have hT3 : ({r1, r2, w} : Finset (Fin 22)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm hwr2)]
    simp [hr12, Ne.symm hwr1]
  obtain ⟨B, _, hBu⟩ := IsSteinerTripleHexads.isSteinerTriple_hexads.2.2 {r1, r2, w} hT3
  have hS'r1 : r1 ∈ H' := hS'H (by simp [hS'])
  have hS'r2 : r2 ∈ H' := hS'H (by simp [hS'])
  have e0 : H0 = B := hBu H0 ⟨hH0, by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hr1.2
    · exact hr2.2
    · exact hwH0⟩
  have e1 : H' = B := hBu H' ⟨hH', by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hS'r1
    · exact hS'r2
    · exact (Finset.mem_inter.1 hwZH).2⟩
  have : u ∈ H0 := by
    rw [e0, ← e1]
    exact hS'H (by simp [hS'])
  exact hu.2 this

section Normal

variable {𝒯 : Finset (Finset P23)} (hN : IsNormal 𝒯)
include hN

theorem isOddSeven_of_mem {Y : Finset (Fin 22)} (hY : Y.map ι ∈ 𝒯) : IsOddSeven Y := by
  refine ⟨?_, fun H hH => ?_⟩
  · have := hN.1.2.1 _ hY
    rwa [Finset.card_map] at this
  · have hB' : insert Q (H.map ι) ∈ 𝒯 := (hN.2 H).1 hH
    have hne : Y.map ι ≠ insert Q (H.map ι) := fun e =>
      Q_notMem_map_ι (Y := Y) (by rw [e]; exact Finset.mem_insert_self _ _)
    have := odd_card_inter hN.1 hY hB' hne
    have e : Y.map ι ∩ insert Q (H.map ι) = (Y ∩ H).map ι := by
      ext x
      rcases x with a | u
      · simp [ι, Q]
      · cases u
        simp [ι, Q]
    rwa [e, Finset.card_map] at this

theorem kin_of_mem {Y Y' : Finset (Fin 22)} (hY : Y.map ι ∈ 𝒯) (hY' : Y'.map ι ∈ 𝒯) : Kin Y Y' := by
  by_cases e : Y = Y'
  · exact Or.inl e
  · right
    have hne : Y.map ι ≠ Y'.map ι := fun h => e (Finset.map_injective ι h)
    have := odd_card_inter hN.1 hY hY' hne
    rwa [← Finset.map_inter, Finset.card_map] at this

theorem hexad_of_mem {B : Finset P23} (hB : B ∈ 𝒯) (hQ : Q ∈ B) : lift B ∈ hexads :=
  (hN.2 _).2 (by rw [← decomp_Q hQ]; exact hB)

theorem exists_noQ : ∃ Y : Finset (Fin 22), Y.map ι ∈ 𝒯 := by
  by_contra hno
  push Not at hno
  have h0 := card_filter_lam hN.1 (j := 0) (by norm_num) (S := ∅) rfl
  have h1 := card_filter_lam hN.1 (j := 1) (by norm_num) (S := {Q}) (by simp)
  have : 𝒯.filter (∅ ⊆ ·) = 𝒯.filter ({Q} ⊆ ·) := by
    ext B
    simp only [Finset.mem_filter, Finset.empty_subset, and_true, Finset.singleton_subset_iff]
    refine ⟨fun hB => ?_, fun h => h.1⟩
    refine ⟨hB, ?_⟩
    by_contra hQ
    exact hno _ (by rw [← decomp_noQ hQ]; exact hB)
  rw [this, h1] at h0
  simp [lamNum] at h0

theorem class_closed {Y0 Z : Finset (Fin 22)} (hY0 : Y0.map ι ∈ 𝒯) (hZ : IsOddSeven Z)
    (hk : Kin Z Y0) : Z.map ι ∈ 𝒯 := by
  by_contra hZ'
  have hY0' := isOddSeven_of_mem hN hY0
  have hodd : ∀ Y, Y.map ι ∈ 𝒯 → (Z ∩ Y).card ≤ 3 := by
    intro Y hY
    have hY' := isOddSeven_of_mem hN hY
    have hkY : Kin Z Y := Kin.trans hZ hY0' hY' hk (kin_of_mem hN hY0 hY)
    have hne : Z ≠ Y := fun e => hZ' (by rw [e]; exact hY)
    rcases hkY with e | ho
    · exact absurd e hne
    · have := card_inter_le_four hZ hY' hne
      obtain ⟨k, hk⟩ := ho
      omega
  obtain ⟨S, hSZ, hSc, hSH⟩ := no_hexad_cover hZ
  obtain ⟨B, ⟨hB, hSB⟩, _⟩ := hN.1.2.2 (S.map ι) (by rw [Finset.card_map, hSc])
  by_cases hQ : Q ∈ B
  · refine hSH _ (hexad_of_mem hN hB hQ) fun x hx => ?_
    exact mem_lift.2 (hSB (Finset.mem_map_of_mem ι hx))
  · have hB2 : (lift B).map ι ∈ 𝒯 := by rwa [← decomp_noQ hQ]
    have hSB2 : S.map ι ⊆ (lift B).map ι := by rwa [← decomp_noQ hQ]
    have hSY : S ⊆ lift B := (Finset.map_subset_map).1 hSB2
    have := Finset.card_le_card (Finset.subset_inter hSZ hSY)
    have := hodd _ hB2
    omega

theorem mem_iff {Y0 : Finset (Fin 22)} (hY0 : Y0.map ι ∈ 𝒯) {Z : Finset (Fin 22)} :
    Z.map ι ∈ 𝒯 ↔ IsOddSeven Z ∧ Kin Z Y0 :=
  ⟨fun h => ⟨isOddSeven_of_mem hN h, kin_of_mem hN h hY0⟩,
    fun h => class_closed hN hY0 h.1 h.2⟩

theorem mem_iff_full {Y0 : Finset (Fin 22)} (hY0 : Y0.map ι ∈ 𝒯) {B : Finset P23} :
    B ∈ 𝒯 ↔ (Q ∈ B ∧ lift B ∈ hexads) ∨ (Q ∉ B ∧ IsOddSeven (lift B) ∧ Kin (lift B) Y0) := by
  constructor
  · intro hB
    by_cases hQ : Q ∈ B
    · exact Or.inl ⟨hQ, hexad_of_mem hN hB hQ⟩
    · exact Or.inr ⟨hQ, (mem_iff hN hY0).1 (by rwa [← decomp_noQ hQ])⟩
  · rintro (⟨hQ, hH⟩ | ⟨hQ, h1, h2⟩)
    · have := (hN.2 _).1 hH
      rwa [← decomp_Q hQ] at this
    · have := (mem_iff hN hY0).2 ⟨h1, h2⟩
      rwa [← decomp_noQ hQ] at this

end Normal

section Build

variable {Ω : Type u} {Ω' : Type v} [Fintype Ω] [DecidableEq Ω] [Fintype Ω'] [DecidableEq Ω']

theorem mem_image_map {𝒯 : Finset (Finset Ω)} (φ : Ω ≃ Ω') {X : Finset Ω'} :
    X ∈ 𝒯.image (fun B => B.map φ.toEmbedding) ↔ X.map φ.symm.toEmbedding ∈ 𝒯 := by
  constructor
  · rintro hX
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.1 hX
    simpa [Finset.map_map] using hB
  · intro hX
    exact Finset.mem_image.2 ⟨_, hX, by simp [Finset.map_map]⟩

theorem IsSteiner4.image {𝒯 : Finset (Finset Ω)} (h : IsSteiner4 𝒯) (φ : Ω ≃ Ω') :
    IsSteiner4 (𝒯.image fun B => B.map φ.toEmbedding) := by
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

omit [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}] [CardHexads] [CardHexadAut] in
abbrev Rest (p : Ω) := {x : Ω // x ≠ p}

omit [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}] [CardHexads] [CardHexadAut] in
/-- The blocks through `p`, with `p` removed. -/
def derived (p : Ω) (𝒯 : Finset (Finset Ω)) : Finset (Finset (Rest p)) :=
  Finset.univ.filter fun H => insert p (H.map (Function.Embedding.subtype _)) ∈ 𝒯

theorem card_rest (p : Ω) (hΩ : Fintype.card Ω = 23) : Fintype.card (Rest p) = 22 := by
  rw [Fintype.card_subtype, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, hΩ]

theorem eq_insert_subtype {p : Ω} {B : Finset Ω} (hp : p ∈ B) :
    B = insert p ((B.subtype fun x => x ≠ p).map (Function.Embedding.subtype _)) := by
  ext x
  by_cases hxp : x = p
  · simp [hxp, hp]
  · simp [hxp]

theorem isSteinerTriple_derived {𝒯 : Finset (Finset Ω)} (h : IsSteiner4 𝒯) (p : Ω) :
    IsSteinerTriple (derived p 𝒯) := by
  refine ⟨card_rest p h.1, ?_, ?_⟩
  · intro H hH
    have := h.2.1 _ (Finset.mem_filter.1 hH).2
    rw [Finset.card_insert_of_notMem (by simp), Finset.card_map] at this
    omega
  · intro T hT
    obtain ⟨B, ⟨hB, hTB⟩, hu⟩ := h.2.2 (insert p (T.map (Function.Embedding.subtype _))) (by
        rw [Finset.card_insert_of_notMem (by simp), Finset.card_map, hT])
    have hpB : p ∈ B := hTB (by simp)
    refine ⟨B.subtype fun x => x ≠ p, ⟨?_, ?_⟩, ?_⟩
    · refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      rw [← eq_insert_subtype hpB]; exact hB
    · intro x hx
      exact Finset.mem_subtype.2 (hTB (Finset.mem_insert_of_mem (Finset.mem_map.2 ⟨x, hx, rfl⟩)))
    · rintro H' ⟨hH', hTH'⟩
      have hH'B := (Finset.mem_filter.1 hH').2
      have := hu _ ⟨hH'B, by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_map, Function.Embedding.coe_subtype] at hx ⊢
        rcases hx with rfl | ⟨y, hy, rfl⟩
        · simp
        · right; exact ⟨y, hTH' hy, rfl⟩⟩
      ext y
      have h2 := congrArg (fun C : Finset Ω => y.1 ∈ C) this
      simpa [y.2, Finset.mem_subtype] using h2

omit [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}] [CardHexads] [CardHexadAut] in
/-- The bijection sending `p` to `Q` and the rest through `e`. -/
noncomputable def toP (p : Ω) (e : Rest p ≃ Fin 22) : Ω ≃ P23 where
  toFun x := if hp : x = p then Q else Sum.inl (e ⟨x, hp⟩)
  invFun
    | Sum.inl a => (e.symm a).1
    | Sum.inr _ => p
  left_inv x := by
    by_cases hp : x = p
    · simp [hp, Q]
    · simp [hp]
  right_inv y := by
    rcases y with a | u
    · have := (e.symm a).2
      simp [this]
    · cases u
      simp [Q]

theorem toP_p (p : Ω) (e : Rest p ≃ Fin 22) : toP p e p = Q := by
  simp [toP]

theorem toP_rest (p : Ω) (e : Rest p ≃ Fin 22) (x : Rest p) : toP p e x.1 = Sum.inl (e x) := by
  simp [toP, x.2]

variable [SteinerTripleIso.{u, 0}] in
theorem exists_normal {𝒯 : Finset (Finset Ω)} (h : IsSteiner4 𝒯) :
    ∃ φ : Ω ≃ P23, IsNormal (𝒯.image fun B => B.map φ.toEmbedding) := by
  obtain ⟨p⟩ : Nonempty Ω := Fintype.card_pos_iff.1 (by rw [h.1]; norm_num)
  obtain ⟨e, he⟩ := SteinerTripleIso.steinerTriple_iso (isSteinerTriple_derived h p) IsSteinerTripleHexads.isSteinerTriple_hexads
  refine ⟨toP p e, h.image _, fun H => ?_⟩
  rw [mem_image_map]
  have key : (insert Q (H.map ι)).map (toP p e).symm.toEmbedding =
      insert p ((H.map e.symm.toEmbedding).map (Function.Embedding.subtype _)) := by
    ext x
    rw [Finset.mem_map_equiv, Equiv.symm_symm]
    by_cases hxp : x = p
    · subst hxp; simp [toP_p]
    · have hx : toP p e x = Sum.inl (e ⟨x, hxp⟩) := toP_rest p e ⟨x, hxp⟩
      rw [hx]
      simp [ι, hxp, Q]
  rw [key]
  have hH : (H.map e.symm.toEmbedding).map e.toEmbedding = H := by simp [Finset.map_map]
  have := he (H.map e.symm.toEmbedding)
  rw [hH] at this
  rw [← this, derived, Finset.mem_filter]
  simp

end Build

end CFSGOutside.WittDesigns.Witt4723
