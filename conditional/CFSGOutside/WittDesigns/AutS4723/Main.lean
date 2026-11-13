import Mathlib
import CFSGOutside.WittDesigns.AutS4723.Class
import CFSGOutside.WittDesigns.AutS5824.Transport

/-!
# The automorphism group of the Steiner system `S(4,7,23)` has order `|M23| = 10200960`

Any `S(4,7,23)` is uniquely determined by its derived system at a point, which is the system of hexads,
and by one of the two classes of odd heptads of the hexads. The automorphism group is transitive on the 23
points. The stabilizer of a point restricts injectively to the automorphisms of the hexads, with image the
subgroup preserving the chosen class of heptads, which has index 2 in the group of order 887040 given by
the corpus. Hence `23 * 443520 = 10200960`.
-/

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

universe u v

namespace CFSGOutside.WittDesigns.Aut4723

open CFSGOutside.Corpus CFSGOutside.Corpus.WittDesign CFSGOutside.WittDesigns.Witt4723
open CFSGOutside.WittDesigns.Witt5824 (IsOddSeven)
attribute [local instance] Classical.propDecidable

variable [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}] [CardHexads] [CardHexadAut]

omit [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}] [CardHexads] [CardHexadAut] in
noncomputable def resFun (g : Equiv.Perm P23) (i : Fin 22) : Fin 22 :=
  Sum.elim id (fun _ => i) (g (Sum.inl i))

theorem exists_normal_at {Ω : Type u} [SteinerTripleIso.{u, 0}] [Fintype Ω] [DecidableEq Ω] {𝒯 : Finset (Finset Ω)}
    (h : IsSteiner4 𝒯) (p : Ω) :
    ∃ φ : Ω ≃ P23, φ p = Q ∧ IsNormal (𝒯.image fun B => B.map φ.toEmbedding) := by
  obtain ⟨e, he⟩ := SteinerTripleIso.steinerTriple_iso (isSteinerTriple_derived h p) IsSteinerTripleHexads.isSteinerTriple_hexads
  refine ⟨toP p e, toP_p p e, h.image _, fun H => ?_⟩
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

section Main

variable {𝒯 : Finset (Finset P23)} (hN : IsNormal 𝒯) {Y0 : Finset (Fin 22)}
include hN

theorem exists_aut_to_Q (p : P23) : ∃ g : Equiv.Perm P23, g ∈ blockAut 𝒯 ∧ g p = Q := by
  obtain ⟨φ, hφp, hφN⟩ := exists_normal_at hN.1 p
  obtain ⟨σ, hσQ, hσ⟩ := iso_of_normal hφN hN
  refine ⟨φ.trans σ, ?_, ?_⟩
  · rw [mem_blockAut]
    intro B
    have h1 : B.map (φ.trans σ).toEmbedding = (B.map φ.toEmbedding).map σ.toEmbedding := by
      rw [Finset.map_map]; rfl
    rw [h1, ← hσ, mem_image_map]
    simp [Finset.map_map]
  · show σ (φ p) = Q
    rw [hφp, hσQ]

theorem g_inl {g : Equiv.Perm P23} (hg : g Q = Q) (i : Fin 22) :
    g (Sum.inl i) = Sum.inl (resFun g i) := by
  rcases h : g (Sum.inl i) with j | u
  · simp [resFun, h]
  · exfalso
    have : g (Sum.inl i) = g Q := h.trans hg.symm
    exact absurd (g.injective this) (by simp [Q])

theorem resFun_injective {g : Equiv.Perm P23} (hg : g Q = Q) : Function.Injective (resFun g) := by
  intro i j h
  have h1 := g_inl hN hg i
  have h2 := g_inl hN hg j
  rw [h] at h1
  exact Sum.inl_injective (g.injective (h1.trans h2.symm))

omit [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}] [CardHexads] [CardHexadAut] in
noncomputable def resPerm {g : Equiv.Perm P23} (hg : g Q = Q) : Equiv.Perm (Fin 22) :=
  Equiv.ofBijective (resFun g) (Finite.injective_iff_bijective.1 (resFun_injective hN hg))

theorem resPerm_apply {g : Equiv.Perm P23} (hg : g Q = Q) (i : Fin 22) :
    resPerm hN hg i = resFun g i := rfl

theorem map_res {g : Equiv.Perm P23} (hg : g Q = Q) (H : Finset (Fin 22)) :
    (H.map ι).map g.toEmbedding = (H.map (resPerm hN hg).toEmbedding).map ι := by
  rw [Finset.map_map, Finset.map_map]
  congr 1
  ext i
  simp [ι, g_inl hN hg, resPerm_apply]

theorem resPerm_mem {g : Equiv.Perm P23} (hgG : g ∈ blockAut 𝒯) (hg : g Q = Q) :
    resPerm hN hg ∈ hexadAut := by
  rw [mem_blockAut]
  intro H
  have key : (insert Q (H.map ι)).map g.toEmbedding =
      insert Q ((H.map (resPerm hN hg).toEmbedding).map ι) := by
    rw [Finset.map_insert, map_res hN hg]
    simp [hg]
  calc H.map (resPerm hN hg).toEmbedding ∈ hexads
      ↔ insert Q ((H.map (resPerm hN hg).toEmbedding).map ι) ∈ 𝒯 := hN.2 _
    _ ↔ (insert Q (H.map ι)).map g.toEmbedding ∈ 𝒯 := by rw [key]
    _ ↔ insert Q (H.map ι) ∈ 𝒯 := mem_blockAut.1 hgG _
    _ ↔ H ∈ hexads := (hN.2 H).symm

theorem resPerm_pres (hY0 : Y0.map ι ∈ 𝒯) {g : Equiv.Perm P23} (hgG : g ∈ blockAut 𝒯) (hg : g Q = Q) :
    Pres Y0 (resPerm hN hg) := by
  have h1 : (Y0.map (resPerm hN hg).toEmbedding).map ι ∈ 𝒯 := by
    rw [← map_res hN hg]
    exact (mem_blockAut.1 hgG _).2 hY0
  exact ((mem_iff hN hY0).1 h1).2

theorem exists_ext (hY0 : Y0.map ι ∈ 𝒯) {a : Equiv.Perm (Fin 22)} (ha : a ∈ hexadAut) (hpres : Pres Y0 a) :
    ∃ g : Equiv.Perm P23, g ∈ blockAut 𝒯 ∧ g Q = Q ∧ ∀ i, g (Sum.inl i) = Sum.inl (a i) := by
  have hY0' : IsOddSeven Y0 := isOddSeven_of_mem hN hY0
  refine ⟨Equiv.sumCongr a (Equiv.refl Unit), ?_, by simp [Q], fun i => by simp⟩
  rw [mem_blockAut]
  intro B
  have hQ : Q ∈ B.map (Equiv.sumCongr a (Equiv.refl Unit)).toEmbedding ↔ Q ∈ B := by
    rw [Finset.mem_map_equiv]
    simp [Q]
  have hL : lift (B.map (Equiv.sumCongr a (Equiv.refl Unit)).toEmbedding) =
      (lift B).map a.toEmbedding := by
    ext x
    rw [mem_lift, Finset.mem_map_equiv, Finset.mem_map_equiv, mem_lift]
    simp
  rw [mem_iff_full hN hY0, mem_iff_full hN hY0, hQ, hL]
  refine or_congr (and_congr Iff.rfl (mem_blockAut.1 ha _)) (and_congr Iff.rfl ?_)
  constructor
  · rintro ⟨h1, h2⟩
    have h1' := (oddSeven_map_iff ha).1 h1
    refine ⟨h1', ?_⟩
    have h3 : Kin ((lift B).map a.toEmbedding) (Y0.map a.toEmbedding) :=
      Kin.trans h1 hY0' (oddSeven_map_of_mem ha hY0') h2 hpres.symm
    exact (kin_map_iff a).1 h3
  · rintro ⟨h1, h2⟩
    refine ⟨oddSeven_map_of_mem ha h1, ?_⟩
    have h3 := (kin_map_iff a).2 h2
    exact Kin.trans (oddSeven_map_of_mem ha h1) (oddSeven_map_of_mem ha hY0') hY0' h3 hpres

theorem card_stab (hY0 : Y0.map ι ∈ 𝒯) (hY0' : IsOddSeven Y0) :
    Nat.card (MulAction.stabilizer (blockAut 𝒯) Q) = 443520 := by
  have hK : Nat.card {b : hexadAut // Pres Y0 b.1} = 443520 := by
    have := card_hexadAut_eq_two_mul hY0'
    omega
  have hmem : ∀ x : MulAction.stabilizer (blockAut 𝒯) Q, x.1.1 Q = Q := fun x => by
    have := MulAction.mem_stabilizer_iff.1 x.2
    rwa [Subgroup.smul_def, Equiv.Perm.smul_def] at this
  rw [← hK]
  apply le_antisymm
  · refine Nat.card_le_card_of_injective
      (fun x => (⟨⟨resPerm hN (hmem x), resPerm_mem hN x.1.2 (hmem x)⟩,
        resPerm_pres hN hY0 x.1.2 (hmem x)⟩ : {b : hexadAut // Pres Y0 b.1})) ?_
    intro x y hxy
    have hres : ∀ i, resFun x.1.1 i = resFun y.1.1 i := fun i => by
      have := congrArg (fun f : {b : hexadAut // Pres Y0 b.1} => (f.1.1 : Equiv.Perm (Fin 22)) i) hxy
      exact this
    apply Subtype.ext
    apply Subtype.ext
    apply Equiv.ext
    intro z
    rcases z with i | u
    · rw [g_inl hN (hmem x), g_inl hN (hmem y), hres]
    · cases u
      exact (hmem x).trans (hmem y).symm
  · choose g hg using fun b : {b : hexadAut // Pres Y0 b.1} => exists_ext hN hY0 b.1.2 b.2
    refine Nat.card_le_card_of_injective
      (fun b => (⟨⟨g b, (hg b).1⟩, by
        rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def, Equiv.Perm.smul_def]
        exact (hg b).2.1⟩ : MulAction.stabilizer (blockAut 𝒯) Q)) ?_
    intro a b hab
    have hgab : g a = g b := congrArg (fun x => x.1.1) hab
    apply Subtype.ext
    apply Subtype.ext
    apply Equiv.ext
    intro i
    have h1 := (hg a).2.2 i
    have h2 := (hg b).2.2 i
    rw [hgab] at h1
    exact Sum.inl_injective (h1.symm.trans h2)

theorem card_aut_normal : Nat.card (blockAut 𝒯) = 10200960 := by
  obtain ⟨Y0, hY0⟩ := exists_noQ hN
  have h1 := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (blockAut 𝒯) Q
  have horb : MulAction.orbit (blockAut 𝒯) Q = Set.univ := by
    ext p
    simp only [Set.mem_univ, iff_true]
    obtain ⟨g, hg, hgp⟩ := exists_aut_to_Q hN p
    refine ⟨⟨g⁻¹, inv_mem hg⟩, ?_⟩
    show g⁻¹ Q = p
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact hgp.symm
  have hcard : Nat.card (MulAction.orbit (blockAut 𝒯) Q) = 23 := by
    rw [horb, Nat.card_univ, Nat.card_eq_fintype_card]
    simp
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at h1
  rw [hcard, card_stab hN hY0 (isOddSeven_of_mem hN hY0)] at h1
  omega

end Main

/-- **The automorphism group of `S(4,7,23)` has order `|M23|`.** -/
theorem card_aut_S4723 {Ω : Type u} [SteinerTripleIso.{u, 0}] [Fintype Ω] [DecidableEq Ω] {𝒯 : Finset (Finset Ω)}
    (h : IsSteiner4 𝒯) : Nat.card (blockAut 𝒯) = 10200960 := by
  obtain ⟨φ, hφ⟩ := exists_normal h
  rw [← CFSGOutside.WittDesigns.Aut5824.card_blockAut_image 𝒯 φ]
  exact card_aut_normal hφ

end CFSGOutside.WittDesigns.Aut4723
