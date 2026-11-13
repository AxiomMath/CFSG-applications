import CFSGOutside.Corpus.QuaternionSylowStructure
import CFSGOutside.GiuliettiKorchmaros.Thm61SL2
import CFSGOutside.GiuliettiKorchmaros.Thm61Defs
import CFSGOutside.GiuliettiKorchmaros.Order48

/-!
# Theorem 6.1: generalized quaternion Sylow 2-subgroups (Lemma 6.10)
-/

namespace CFSGOutside.GiuliettiKorchmaros

open CFSGOutside.Corpus
open scoped MatrixGroups

/-- A ring isomorphism induces an isomorphism of `SL(2, -)`. -/
def slCongr {K L : Type} [Field K] [Field L] (e : K ≃+* L) : SL(2, K) ≃* SL(2, L) :=
  { Matrix.SpecialLinearGroup.map e.toRingHom with
    invFun := Matrix.SpecialLinearGroup.map e.symm.toRingHom
    left_inv := fun A => by ext i j; simp
    right_inv := fun A => by ext i j; simp }

/-- A field with 3 elements is `ZMod 3`. -/
noncomputable def ringEquivZModThree (F : Type) [Field F] [Finite F] (h3 : Nat.card F = 3) :
    F ≃+* ZMod 3 := by
  haveI := Fintype.ofFinite F
  exact FiniteField.ringEquivOfCardEq (by rw [← Nat.card_eq_fintype_card, h3]; rfl)

/-- `|SL(2,F)| = 24` for `|F| = 3`. -/
theorem card_sl2_of_card_three (F : Type) [Field F] [Finite F] (h3 : Nat.card F = 3) :
    Nat.card SL(2, F) = 24 := by
  have hF : ringChar F ≠ 2 := by
    intro h
    haveI := Fintype.ofFinite F
    haveI : CharP F 2 := h ▸ ringChar.charP F
    obtain ⟨m, -, hm⟩ := FiniteField.card F 2
    rw [← Nat.card_eq_fintype_card, h3] at hm
    have : (2 : ℕ) ∣ 3 := hm ▸ dvd_pow_self 2 (PNat.ne_zero m)
    omega
  have h1 := LinearTwo.card_PSL2_mul_two F hF
  have h2 := LinearTwo.card_center_SL2 F hF
  have h3' := Subgroup.card_mul_index (Subgroup.center SL(2, F))
  rw [h2, Subgroup.index_eq_card] at h3'
  have h4 : Nat.card (SL(2, F) ⧸ Subgroup.center SL(2, F)) = Nat.card (GorensteinWalter.PSL2 F) := rfl
  rw [h4, h3] at *
  omega

variable {X : Type} [Group X] [Finite X]

/-- Transport of the five conclusions along an isomorphism. -/
theorem quaternion_conclusion_transport {Y : Type} [Group Y] [Finite Y] (π : X ≃* Y)
    (h : IsPGroup 2 X ∨
      (∃ (F : Type) (_ : Field F) (_ : Finite F), ringChar F ≠ 2 ∧ 5 ≤ Nat.card F ∧
        Nonempty (commutator X ≃* SL(2, F))) ∨
      Nonempty (X ≃* SL(2, ZMod 3)) ∨
      (Nonempty (X ≃* binaryOctahedral) ∧ ∃ J : Subgroup X, J.Normal ∧ J.index = 2 ∧
        Nonempty (J ≃* SL(2, ZMod 3))) ∨
      (commutator X = ⊤ ∧ Nat.card X = 5040 ∧
        Nonempty (X ⧸ Subgroup.center X ≃* alternatingGroup (Fin 7)))) :
    IsPGroup 2 Y ∨
      (∃ (F : Type) (_ : Field F) (_ : Finite F), ringChar F ≠ 2 ∧ 5 ≤ Nat.card F ∧
        Nonempty (commutator Y ≃* SL(2, F))) ∨
      Nonempty (Y ≃* SL(2, ZMod 3)) ∨
      (Nonempty (Y ≃* binaryOctahedral) ∧ ∃ J : Subgroup Y, J.Normal ∧ J.index = 2 ∧
        Nonempty (J ≃* SL(2, ZMod 3))) ∨
      (commutator Y = ⊤ ∧ Nat.card Y = 5040 ∧
        Nonempty (Y ⧸ Subgroup.center Y ≃* alternatingGroup (Fin 7))) := by
  have hcomm : (commutator X).map π.toMonoidHom = commutator Y := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _
      π.surjective]
  rcases h with h | ⟨F, hF1, hF2, hF, h5, ⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩, J, hJn, hJi, ⟨eJ⟩⟩ | ⟨h1, h2, ⟨e⟩⟩
  · exact Or.inl (h.of_equiv π)
  · refine Or.inr (Or.inl ⟨F, hF1, hF2, hF, h5, ⟨?_⟩⟩)
    exact (MulEquiv.subgroupCongr hcomm.symm).trans
      ((Subgroup.equivMapOfInjective (commutator X) π.toMonoidHom π.injective).symm.trans e)
  · exact Or.inr (Or.inr (Or.inl ⟨π.symm.trans e⟩))
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨π.symm.trans e⟩, J.map π.toMonoidHom,
      hJn.map _ π.surjective, ?_, ⟨(Subgroup.equivMapOfInjective J _ π.injective).symm.trans eJ⟩⟩)))
    rw [Subgroup.index_map_of_bijective π.bijective]; exact hJi
  · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_⟩)))
    · rw [← hcomm, h1, Subgroup.map_top_of_surjective _ π.surjective]
    · rw [← h2]; exact (Nat.card_congr π.toEquiv).symm
    · exact ⟨(QuotientGroup.congr _ _ π.symm (Subgroup.map_center_eq _)).trans e⟩

variable [QuaternionSylowStructure.{0}] [SemilinearEquivAut.{0}] [SpecialLinearGroupSylowQuaternion.{0}]

/-- Lemma 6.10 (with the case `SL(2,3)` the paper omits): an odd core-free group with `CyclicIndexTwo` and
generalized quaternion Sylow 2-subgroups is a 2-group, has commutator subgroup `SL(2,q)` with `q ≥ 5`, or is `SL(2,3)`,
the binary octahedral group, or the perfect group `2.A₇` of order 5040. -/
theorem quaternion_cases (hP : CyclicIndexTwo X) (hO : OddCoreFree X) (S : Sylow 2 X)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup X) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    IsPGroup 2 X ∨
      (∃ (F : Type) (_ : Field F) (_ : Finite F), ringChar F ≠ 2 ∧ 5 ≤ Nat.card F ∧
        Nonempty (commutator X ≃* SL(2, F))) ∨
      Nonempty (X ≃* SL(2, ZMod 3)) ∨
      (Nonempty (X ≃* binaryOctahedral) ∧ ∃ J : Subgroup X, J.Normal ∧ J.index = 2 ∧
        Nonempty (J ≃* SL(2, ZMod 3))) ∨
      (commutator X = ⊤ ∧ Nat.card X = 5040 ∧
        Nonempty (X ⧸ Subgroup.center X ≃* alternatingGroup (Fin 7))) := by
  classical
  obtain ⟨z, hz2, hzc, hzu, hcases⟩ := QuaternionSylowStructure.quaternion_sylow_structure S hS
  set Q := X ⧸ oddCore X
  let π : Q ≃* X := quotientBotEquiv _ (oddCore_eq_bot hO)
  apply quaternion_conclusion_transport π
  have hPQ : CyclicIndexTwo Q := cyclicIndexTwo_of_mulEquiv π.symm hP
  have hOQ : OddCoreFree Q := oddCoreFree_of_mulEquiv π.symm hO
  have huniq : ∀ x y : Q, x ^ 2 = 1 → y ^ 2 = 1 → x ≠ 1 → y ≠ 1 → x = y := fun x y hx hy hx1 hy1 =>
    (hzu x (orderOf_eq_prime hx hx1)).trans (hzu y (orderOf_eq_prime hy hy1)).symm
  rcases hcases with h | ⟨F, _, _, hF, L, hLn, hLi, ⟨eL⟩⟩ |
      ⟨F, _, _, hF, L, hLn, hLi, ⟨φ, hφ, hker⟩, -, M, hMn, hML, ⟨eM⟩⟩ | ⟨⟨hcomm, -⟩, hZ, ⟨e⟩⟩
  · exact Or.inl h
  · -- a normal `SL(2,F)` of odd index
    haveI := hLn
    have hC := centralizer_le_of_normal_sl2 hPQ hOQ hF L eL
    rcases card_three_or_five_le F hF with h3 | h5
    · -- `|F| = 3`: then `Q = L ≅ SL(2,3)`
      have hcard := Key.card_le_of_normal_sl2 hF L eL
      rw [Key.card_PGammaL2_of_card_three F h3] at hcard
      have hCle : Nat.card (Subgroup.centralizer (L : Set Q)) ≤ 2 :=
        (centralizer_le_of_normal_sl2' hPQ hOQ hF L eL).2
      have hL24 : Nat.card L = 24 := by rw [Nat.card_congr eL.toEquiv, card_sl2_of_card_three F h3]
      have hidx : 24 * L.index = Nat.card Q := by rw [← hL24]; exact Subgroup.card_mul_index L
      have hidx1 : L.index = 1 := by
        obtain ⟨j, hj⟩ := hLi
        have : Nat.card Q ≤ 2 * 24 := le_trans hcard (Nat.mul_le_mul_right _ hCle)
        omega
      have hLtop : L = ⊤ := Subgroup.index_eq_one.mp hidx1
      refine Or.inr (Or.inr (Or.inl ⟨?_⟩))
      exact ((Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hLtop.symm)).trans eL).trans
        (slCongr (ringEquivZModThree F h3))
    · refine Or.inr (Or.inl ⟨F, inferInstance, inferInstance, hF, h5, ⟨?_⟩⟩)
      exact (MulEquiv.subgroupCongr (commutator_eq_of_normal_sl2 hPQ hOQ hF h5 L eL)).trans eL
  · -- `L` maps onto `PGL(2,F)` with kernel `⟨z⟩`, and `M ≅ SL(2,F)` is normal
    haveI := hMn
    obtain ⟨hC, hCle⟩ := centralizer_le_of_normal_sl2' hPQ hOQ hF M eM
    rcases card_three_or_five_le F hF with h3 | h5
    · have hcard := Key.card_le_of_normal_sl2 hF M eM
      rw [Key.card_PGammaL2_of_card_three F h3] at hcard
      have hQle : Nat.card Q ≤ 48 := le_trans hcard (Nat.mul_le_mul_right 24 hCle)
      have hker2 : Nat.card φ.ker = 2 := by
        rw [← Subgroup.card_map_of_injective L.subtype_injective, hker, Nat.card_zpowers, hz2]
      have hPGL : Nat.card (Matrix.ProjGenLinGroup (Fin 2) F) = 24 := by
        rw [LinearTwo.card_PGL2 F, h3]; norm_num
      have hL48 : Nat.card L = 48 := by
        have := Subgroup.card_ker_mul_card_range φ
        rw [hker2, MonoidHom.range_eq_top.mpr hφ, Subgroup.card_top, hPGL] at this
        omega
      have hQ48 : Nat.card Q = 48 := le_antisymm hQle (hL48 ▸ Subgroup.card_le_card_group L)
      have hMidx : M.index = 2 := by
        have h1 := Subgroup.card_mul_index M
        rw [Nat.card_congr eM.toEquiv, card_sl2_of_card_three F h3, hQ48] at h1
        omega
      refine Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, M, hMn, hMidx,
        ⟨eM.trans (slCongr (ringEquivZModThree F h3))⟩⟩)))
      exact Order48.nonempty_mulEquiv_binaryOctahedral hQ48 M hMn
        (eM.trans (slCongr (ringEquivZModThree F h3))) hC huniq
    · refine Or.inr (Or.inl ⟨F, inferInstance, inferInstance, hF, h5, ⟨?_⟩⟩)
      exact (MulEquiv.subgroupCongr (commutator_eq_of_normal_sl2 hPQ hOQ hF h5 M eM)).trans eM
  · -- the perfect group `2.A₇`
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨hcomm, ?_, ⟨e⟩⟩)))
    have h1 := Subgroup.card_mul_index (Subgroup.center Q)
    rw [hZ, Subgroup.index_eq_card, Nat.card_congr e.toEquiv, nat_card_alternatingGroup] at h1
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at h1
    rw [← h1]; decide

end CFSGOutside.GiuliettiKorchmaros
