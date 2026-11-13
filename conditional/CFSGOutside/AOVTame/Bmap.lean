import CFSGOutside.AOVTame.AutI

/-!
# AOV tameness: images of subgroups of `S` under automorphisms of `S`
-/

namespace AndersenOliverVentura.Tame

open Subgroup

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {T : Sylow p G}
  (β : (T : Subgroup G) ≃* (T : Subgroup G))

lemma mem_bmap_iff {P : Subgroup G} {y : G} :
    y ∈ bmap β P ↔ ∃ hy : y ∈ (T : Subgroup G), ((β.symm ⟨y, hy⟩ : (T : Subgroup G)) : G) ∈ P := by
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨(β x).2, ?_⟩
    have e : (⟨(T : Subgroup G).subtype (β.toMonoidHom x), (β x).2⟩ : (T : Subgroup G)) = β x := rfl
    rw [e, MulEquiv.symm_apply_apply]
    exact hx
  · rintro ⟨hy, h⟩
    exact ⟨⟨y, hy⟩, ⟨β.symm ⟨y, hy⟩, h, by simp⟩, rfl⟩

lemma bmap_le (P : Subgroup G) : bmap β P ≤ T := by
  rintro _ ⟨x, -, rfl⟩; exact x.2

lemma bmap_mono {P Q : Subgroup G} (h : P ≤ Q) : bmap β P ≤ bmap β Q := by
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨_, ⟨x, h hx, rfl⟩, rfl⟩

lemma bmap_le_iff {P Q : Subgroup G} (hP : P ≤ T) : bmap β P ≤ bmap β Q ↔ P ≤ Q := by
  refine ⟨fun h x hx => ?_, bmap_mono β⟩
  obtain ⟨_, h2⟩ := (mem_bmap_iff β).1 (h (mem_bmap ⟨x, hP hx⟩ hx))
  simpa using h2

lemma bmap_injOn {P Q : Subgroup G} (hP : P ≤ T) (hQ : Q ≤ T) (e : bmap β P = bmap β Q) : P = Q :=
  le_antisymm ((bmap_le_iff β hP).1 e.le) ((bmap_le_iff β hQ).1 e.ge)

lemma bmap_centralizer_inf {P : Subgroup G} (hP : P ≤ T) :
    bmap β (centralizer (P : Set G) ⊓ T) = centralizer (bmap β P : Set G) ⊓ T := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    obtain ⟨hxC, -⟩ := mem_inf.1 hx
    refine mem_inf.2 ⟨?_, (β x).2⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    have h1 := mem_centralizer_iff.1 hxC z hz
    have : z * x = x * z := Subtype.ext h1
    simp only [coe_subtype, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    rw [← coe_mul, ← coe_mul, ← map_mul, ← map_mul, this]
  · intro hy
    obtain ⟨hyC, hyT⟩ := mem_inf.1 hy
    refine ⟨β (β.symm ⟨y, hyT⟩), ⟨β.symm ⟨y, hyT⟩, ?_, rfl⟩, by simp⟩
    refine mem_inf.2 ⟨?_, (β.symm ⟨y, hyT⟩).2⟩
    rw [mem_centralizer_iff]
    intro z hz
    have h1 := mem_centralizer_iff.1 hyC _ (mem_bmap ⟨z, hP hz⟩ hz)
    have h2 : β ⟨z, hP hz⟩ * ⟨y, hyT⟩ = ⟨y, hyT⟩ * β ⟨z, hP hz⟩ := Subtype.ext h1
    have h3 := congrArg β.symm h2
    simp only [map_mul, MulEquiv.symm_apply_apply] at h3
    exact congrArg Subtype.val h3

lemma bmap_inf (Q R : Subgroup G) : bmap β (Q ⊓ R) = bmap β Q ⊓ bmap β R := by
  apply le_antisymm (le_inf (bmap_mono β inf_le_left) (bmap_mono β inf_le_right))
  intro y hy
  obtain ⟨hyT, hQ⟩ := (mem_bmap_iff β).1 (mem_inf.1 hy).1
  obtain ⟨hyT', hR⟩ := (mem_bmap_iff β).1 (mem_inf.1 hy).2
  exact (mem_bmap_iff β).2 ⟨hyT, mem_inf.2 ⟨hQ, hR⟩⟩

lemma bmap_inf_centralizer {P : Subgroup G} (hP : P ≤ T) :
    bmap β (P ⊓ centralizer (P : Set G)) = bmap β P ⊓ centralizer (bmap β P : Set G) := by
  have h1 : P ⊓ centralizer (P : Set G) = P ⊓ (centralizer (P : Set G) ⊓ T) := by
    rw [inf_comm (centralizer _), ← inf_assoc, inf_of_le_left hP]
  rw [h1, bmap_inf, bmap_centralizer_inf β hP]
  exact le_antisymm (le_inf inf_le_left (inf_le_right.trans inf_le_left))
    (le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans (bmap_le β P))))

end AndersenOliverVentura.Tame
