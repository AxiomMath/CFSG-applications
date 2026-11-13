import CFSGOutside.ChillagSonn.Fact5B
import CFSGOutside.Corpus.SemilinearEquivAut

/-!
# Fact 5 of Chillag–Sonn, part C: the index-2 subgroup and a compatible `SL(2, F)`

In a stem extension `A` by `D` of order 2, a subgroup `A₀ ⊇ D` of index 2 mapping onto a nonabelian simple group
with kernel `D` is perfect. An isomorphism `A₀ ≅ SL(2, F)` can be chosen compatible with a given map `A₀ → PSL(2, F)`,
since every automorphism of `PSL(2, F)` comes from `PΓL(2, F)` and lifts to `SL(2, F)`.
-/

noncomputable section

namespace CFSGOutside.ChillagSonn

open CFSGOutside.Corpus CFSGOutside.Corpus.GorensteinWalter Matrix SemidirectProduct
open scoped MatrixGroups

/-- A nonabelian simple group is perfect. -/
theorem commutator_eq_top_of_isSimpleGroup {X : Type} [Group X] [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a) :
    commutator X = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with h | h
  · obtain ⟨a, b, hab⟩ := hnab
    have := Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [← commutator_def, h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact absurd this hab
  · exact h

/-- A subgroup of index 2 of a stem extension, containing the kernel `D` (of order 2) and mapping onto a nonabelian
simple group with kernel `D`, is perfect. -/
theorem commutator_eq_top_of_stem {A X : Type} [Group A] [Finite A] [Group X] [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a) (D : Subgroup A) (hD : D ≤ commutator A) (hD2 : Nat.card D = 2)
    (A₀ : Subgroup A) [A₀.Normal] (hA₀ : A₀.index = 2) (θ : A₀ →* X) (hθ : Function.Surjective θ)
    (hker : θ.ker = D.subgroupOf A₀) (hDA : D ≤ A₀) : commutator A₀ = ⊤ := by
  have : Finite X := Finite.of_surjective θ hθ
  have hmap : (commutator A₀).map θ = ⊤ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, MonoidHom.range_eq_top.mpr hθ,
      ← commutator_def, commutator_eq_top_of_isSimpleGroup hnab]
  set K := ⁅A₀, A₀⁆
  have hKdef : (commutator A₀).map A₀.subtype = K := A₀.map_subtype_commutator
  have hDK : D ≤ K := by
    by_contra hDK
    have hbot : D ⊓ K = ⊥ := by
      have hdvd := Subgroup.card_dvd_of_le (inf_le_left : D ⊓ K ≤ D)
      rw [hD2, Nat.dvd_prime Nat.prime_two] at hdvd
      rcases hdvd with h1 | h2
      · exact Subgroup.eq_bot_of_card_eq _ h1
      · exact absurd ((Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h2, hD2])).symm.le.trans inf_le_right)
          hDK
    have hinj : Function.Injective (θ.comp (commutator A₀).subtype) := by
      rw [injective_iff_map_eq_one]
      rintro ⟨k, hk⟩ h1
      have h2 : k ∈ θ.ker := h1
      rw [hker, Subgroup.mem_subgroupOf] at h2
      have h3 : (k : A) ∈ D ⊓ K := ⟨h2, hKdef ▸ Subgroup.mem_map_of_mem _ hk⟩
      rw [hbot, Subgroup.mem_bot] at h3
      exact Subtype.ext (Subtype.ext h3)
    have hsurj : Function.Surjective (θ.comp (commutator A₀).subtype) := fun x => by
      obtain ⟨k, hk, rfl⟩ := (hmap ▸ Subgroup.mem_top x : x ∈ (commutator A₀).map θ)
      exact ⟨⟨k, hk⟩, rfl⟩
    have c1 : Nat.card (commutator A₀) = Nat.card X := Nat.card_eq_of_bijective _ ⟨hinj, hsurj⟩
    have c2 : Nat.card K = Nat.card (commutator A₀) := hKdef ▸ Subgroup.card_map_of_injective A₀.subtype_injective
    have c3 : Nat.card A₀ = Nat.card X * 2 := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup θ.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective θ hθ).toEquiv, hker,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDA).toEquiv, hD2]
    have c4 := A₀.index_mul_card
    have c5 := K.index_mul_card
    have hKi : K.index = 2 ^ 2 := by
      have : K.index * Nat.card X = 4 * Nat.card X := by
        rw [c2, c1] at c5; rw [c5, ← c4, c3, hA₀]; ring
      exact Nat.eq_of_mul_eq_mul_right Nat.card_pos this
    have hc := Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
      (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hKi)
    exact hDK (hD.trans hc)
  rw [eq_top_iff]
  intro a _
  obtain ⟨k, hk, hka⟩ := (hmap ▸ Subgroup.mem_top (θ a) : θ a ∈ (commutator A₀).map θ)
  have hmem : k⁻¹ * a ∈ θ.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hka, inv_mul_cancel]
  rw [hker, Subgroup.mem_subgroupOf] at hmem
  obtain ⟨k', hk', e⟩ := hKdef ▸ hDK hmem
  rw [show k' = k⁻¹ * a from Subtype.ext e] at hk'
  simpa using mul_mem hk hk'

variable {F : Type} [Field F]

/-- An isomorphism `H ≅ SL(2, F)` can be modified to be compatible with a given map `H → PSL(2, F)` with the same
kernel. -/
theorem exists_compatible_sl2 [SemilinearEquivAut.{0}] [Finite F] {H : Type} [Group H] (η₀ : H ≃* SL(2, F))
    (θ : H →* PSL2 F) (hθ : Function.Surjective θ)
    (hker : ∀ a, θ a = 1 ↔ η₀ a ∈ Subgroup.center SL(2, F)) :
    ∃ η : H →* SL(2, F), Function.Surjective η ∧
      ∀ a, ProjectiveSpecialLinearGroup.toPGL (θ a) = SpecialLinearGroup.toPGL (η a) := by
  let β : SL(2, F) →* PSL2 F := θ.comp η₀.symm.toMonoidHom
  have hβ : Function.Surjective β := hθ.comp η₀.symm.surjective
  have hβker : β.ker = Subgroup.center SL(2, F) := by
    ext x; rw [MonoidHom.mem_ker]; simp [β, hker]
  let α : PSL2 F ≃* PSL2 F :=
    (QuotientGroup.quotientMulEquivOfEq hβker).symm.trans (QuotientGroup.quotientKerEquivOfSurjective β hβ)
  have hα : ∀ x : SL(2, F), α (x : PSL2 F) = β x := fun x => rfl
  obtain ⟨E, hE⟩ := SemilinearEquivAut.semilinearEquivAut F
  have hy : ∀ z : PSL2 F, inl (ProjectiveSpecialLinearGroup.toPGL (α z)) =
      E.symm α * inl (ProjectiveSpecialLinearGroup.toPGL z) * (E.symm α)⁻¹ := fun z => by
    rw [← hE, ← hE, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    ext w
    simp [MulAut.conj_apply]
  obtain ⟨h, hh⟩ := ProjGenLinGroup.mk_surjective (E.symm α).left
  refine ⟨(semiConj h (E.symm α).right).comp η₀.toMonoidHom,
    (semiConj_surjective h _).comp η₀.surjective, fun a => ?_⟩
  have ha : θ a = α ((η₀ a : SL(2, F)) : PSL2 F) := by rw [hα]; simp [β]
  apply inl_injective (φ := pgl2FieldAut F) (G := F ≃+* F)
  rw [ha, hy, conj_inl]
  change _ = inl (SpecialLinearGroup.toPGL (semiConj h _ (η₀ a)))
  rw [toPGL_semiConj, hh]
  rfl

end CFSGOutside.ChillagSonn
