import Mathlib
import CFSGOutside.WittDesigns.AutS5824.Count

/-!
# The automorphism group of the Steiner system `S(5,8,24)` has order `|M24| = 244823040`

Any `S(5,8,24)` is uniquely determined, up to exchanging the two extra points, by the hexads of the derived
`S(3,6,22)`. This gives transitivity on the 276 pairs of points, with stabilizer of a pair isomorphic to
the automorphism group of the hexads. The corpus computes that group to have order 887040, and
`276 * 887040 = 244823040`.
-/

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

universe u v

namespace CFSGOutside.WittDesigns.Aut5824

open CFSGOutside.Corpus CFSGOutside.Corpus.WittDesign CFSGOutside.PlessSloaneG22 CFSGOutside.WittDesigns.Witt5824
open scoped Pointwise
attribute [local instance] Classical.propDecidable

variable [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}] [CardHexads] [CardHexadAut]

omit [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}] [CardHexads] [CardHexadAut] in
noncomputable def resFun (g : Equiv.Perm Pt) (i : Fin 22) : Fin 22 :=
  Sum.elim id (fun _ => i) (g (Sum.inl i))

section Main

variable {𝒮 : Finset (Finset Pt)} (hN : IsNormal 𝒮)
include hN

theorem exists_aut_pair {s : Finset Pt} (hs : s.card = 2) :
    ∃ g : Equiv.Perm Pt, g ∈ blockAut 𝒮 ∧ s.map g.toEmbedding = P0 := by
  obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.1 hs
  obtain ⟨φ, hp, hq, hφ⟩ := exists_normal_at hN.1 hpq
  obtain ⟨σ, hσ, hiso⟩ := iso_of_normal' hφ hN
  refine ⟨φ.trans σ, ?_, ?_⟩
  · rw [mem_blockAut]
    intro B
    have h1 : B.map (φ.trans σ).toEmbedding = (B.map φ.toEmbedding).map σ.toEmbedding := by
      rw [Finset.map_map]; rfl
    rw [h1, ← hiso, mem_image_map]
    simp [Finset.map_map]
  · have h2 : ({p, q} : Finset Pt).map φ.toEmbedding = P0 := by
      simp [Finset.map_insert, hp, hq]
    rw [show (φ.trans σ).toEmbedding = φ.toEmbedding.trans σ.toEmbedding from rfl, ← Finset.map_map,
      h2]
    exact map_P0 hσ

theorem exists_ext {a : Equiv.Perm (Fin 22)} (ha : a ∈ hexadAut) :
    ∃ g : Equiv.Perm Pt, g ∈ blockAut 𝒮 ∧ P0.map g.toEmbedding = P0 ∧
      ∀ i, g (Sum.inl i) = Sum.inl (a i) := by
  set e : Equiv.Perm Pt := Equiv.Perm.sumCongr a (Equiv.refl Bool) with he
  have hNa : IsNormal (𝒮.image fun B => B.map e.toEmbedding) := by
    refine ⟨hN.1.image _, fun H => ?_⟩
    rw [mem_image_map]
    have hsymm : e.symm = Equiv.Perm.sumCongr a⁻¹ (Equiv.refl Bool) := by
      ext x
      rcases x with i | b
      · simp [he, Equiv.Perm.inv_def]
      · cases b <;> simp [he]
    rw [hsymm, hexBlk_map_ext, ← hN.2]
    exact (mem_blockAut.1 (hexadAut.inv_mem ha) H).symm
  obtain ⟨σ, hσ, hiso⟩ := iso_of_normal' hNa hN
  refine ⟨e.trans σ, ?_, ?_, ?_⟩
  · rw [mem_blockAut]
    intro B
    have h1 : B.map (e.trans σ).toEmbedding = (B.map e.toEmbedding).map σ.toEmbedding := by
      rw [Finset.map_map]; rfl
    rw [h1, ← hiso, mem_image_map]
    simp [Finset.map_map]
  · have h2 : P0.map e.toEmbedding = P0 := by
      simp [P0, he, Finset.map_insert]
    rw [show (e.trans σ).toEmbedding = e.toEmbedding.trans σ.toEmbedding from rfl, ← Finset.map_map,
      h2]
    exact map_P0 hσ
  · intro i
    show σ (e (Sum.inl i)) = _
    simp [he, hσ]

theorem stab_map (x : MulAction.stabilizer (blockAut 𝒮) P0) : P0.map x.1.1.toEmbedding = P0 := by
  have := MulAction.mem_stabilizer_iff.1 x.2
  rwa [Subgroup.smul_def, smul_eq_map] at this

theorem g_inl {g : Equiv.Perm Pt} (hg : P0.map g.toEmbedding = P0) (i : Fin 22) :
    g (Sum.inl i) = Sum.inl (resFun g i) := by
  obtain ⟨j, hj⟩ := exists_inl hN hg i
  simp [resFun, hj]

theorem resFun_injective {g : Equiv.Perm Pt} (hg : P0.map g.toEmbedding = P0) :
    Function.Injective (resFun g) := by
  intro i j h
  have h1 := g_inl hN hg i
  have h2 := g_inl hN hg j
  rw [h] at h1
  exact Sum.inl_injective (g.injective (h1.trans h2.symm))

omit [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}] [CardHexads] [CardHexadAut] in
noncomputable def resPerm {g : Equiv.Perm Pt} (hg : P0.map g.toEmbedding = P0) :
    Equiv.Perm (Fin 22) :=
  Equiv.ofBijective (resFun g) (Finite.injective_iff_bijective.1 (resFun_injective hN hg))

theorem resPerm_apply {g : Equiv.Perm Pt} (hg : P0.map g.toEmbedding = P0) (i : Fin 22) :
    resPerm hN hg i = resFun g i := rfl

theorem resPerm_mem {g : Equiv.Perm Pt} (hgG : g ∈ blockAut 𝒮) (hg : P0.map g.toEmbedding = P0) :
    resPerm hN hg ∈ hexadAut := by
  rw [mem_blockAut]
  intro B
  have key : (hexBlk B).map g.toEmbedding = hexBlk (B.map (resPerm hN hg).toEmbedding) := by
    rw [hexBlk_eq, hexBlk_eq, Finset.map_union, hg]
    have hemb : ι.trans g.toEmbedding = (resPerm hN hg).toEmbedding.trans ι := by
      ext i
      simp [ι, g_inl hN hg, resPerm_apply]
    rw [Finset.map_map, Finset.map_map, hemb]
  calc B.map (resPerm hN hg).toEmbedding ∈ hexads
      ↔ hexBlk (B.map (resPerm hN hg).toEmbedding) ∈ 𝒮 := hN.2 _
    _ ↔ (hexBlk B).map g.toEmbedding ∈ 𝒮 := by rw [key]
    _ ↔ hexBlk B ∈ 𝒮 := mem_blockAut.1 hgG _
    _ ↔ B ∈ hexads := (hN.2 B).symm

theorem card_stab : Nat.card (MulAction.stabilizer (blockAut 𝒮) P0) = 887040 := by
  have hf : Nat.card hexadAut = 887040 := CardHexadAut.card_hexadAut.1
  apply le_antisymm
  · rw [← hf]
    refine Nat.card_le_card_of_injective
      (fun x => (⟨resPerm hN (stab_map hN x), resPerm_mem hN x.1.2 (stab_map hN x)⟩ : hexadAut)) ?_
    intro x y hxy
    have hres : ∀ i, resFun x.1.1 i = resFun y.1.1 i := fun i => by
      have := congrArg (fun f : hexadAut => (f.1 : Equiv.Perm (Fin 22)) i) hxy
      exact this
    have hfix : ∀ i, (y.1.1⁻¹ * x.1.1) (Sum.inl i) = Sum.inl i := by
      intro i
      rw [Equiv.Perm.mul_apply, g_inl hN (stab_map hN x), Equiv.Perm.inv_eq_iff_eq, g_inl hN (stab_map hN y),
        hres]
    have h1 := eq_one_of_fix hN (mul_mem (inv_mem y.1.2) x.1.2) hfix
    have h2 : y.1.1 = x.1.1 := inv_mul_eq_one.1 h1
    exact (Subtype.ext (Subtype.ext h2.symm))
  · rw [← hf]
    choose g hg using fun a : hexadAut => exists_ext hN a.2
    refine Nat.card_le_card_of_injective
      (fun a => (⟨⟨g a, (hg a).1⟩, by
        rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def, smul_eq_map]
        exact (hg a).2.1⟩ : MulAction.stabilizer (blockAut 𝒮) P0)) ?_
    intro a b hab
    have hgab : g a = g b := congrArg (fun x => x.1.1) hab
    apply Subtype.ext
    apply Equiv.ext
    intro i
    have h1 := (hg a).2.2 i
    have h2 := (hg b).2.2 i
    rw [hgab] at h1
    exact Sum.inl_injective (h1.symm.trans h2)

theorem card_aut_normal : Nat.card (blockAut 𝒮) = 244823040 := by
  have h1 := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (blockAut 𝒮) P0
  have horb : MulAction.orbit (blockAut 𝒮) P0 = ↑(Finset.powersetCard 2 (Finset.univ : Finset Pt)) := by
    ext s
    rw [MulAction.mem_orbit_iff, Finset.mem_coe, Finset.mem_powersetCard]
    constructor
    · rintro ⟨g, rfl⟩
      refine ⟨Finset.subset_univ _, ?_⟩
      rw [Subgroup.smul_def, smul_eq_map, Finset.card_map, card_P0]
    · rintro ⟨-, hs⟩
      obtain ⟨g, hgG, hg⟩ := exists_aut_pair hN hs
      refine ⟨⟨g⁻¹, inv_mem hgG⟩, ?_⟩
      rw [Subgroup.smul_def, smul_eq_map]
      show P0.map (g⁻¹).toEmbedding = s
      rw [← hg]
      simp [Finset.map_map]
  have hcard : Nat.card (MulAction.orbit (blockAut 𝒮) P0) = 276 := by
    rw [horb, Nat.card_coe_set_eq, Set.ncard_coe_finset, Finset.card_powersetCard, Finset.card_univ]
    simp
    decide
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at h1
  rw [hcard, card_stab hN] at h1
  omega

end Main

/-- **The automorphism group of `S(5,8,24)` has order `|M24|`.** -/
theorem card_aut_S5824 {Ω : Type u} [SteinerTripleIso.{u, 0}] [Fintype Ω] [DecidableEq Ω] {𝒮 : Finset (Finset Ω)}
    (h : IsSteiner5 𝒮) : Nat.card (blockAut 𝒮) = 244823040 := by
  obtain ⟨φ, hφ⟩ := exists_normal h
  rw [← card_blockAut_image 𝒮 φ]
  exact card_aut_normal hφ

end CFSGOutside.WittDesigns.Aut5824
