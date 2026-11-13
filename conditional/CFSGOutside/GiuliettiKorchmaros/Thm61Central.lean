import CFSGOutside.GiuliettiKorchmaros.Thm61Thompson
import CFSGOutside.GiuliettiKorchmaros.Thm61Descent

/-!
# Theorem 6.1: a central involution (Lemmas 6.6, 6.10, 6.11)

For an odd core-free group with `CyclicIndexTwo` and a central involution, by induction on the order: abelian Sylow
2-subgroups give a 2-group (Burnside); generalized quaternion ones are handled by Lemma 6.10; otherwise there is an
involution outside the cyclic subgroup of index 2, Thompson's transfer lemma gives a subgroup of index 2, and the
conclusion descends from it.
-/

namespace CFSGOutside.GiuliettiKorchmaros

open CFSGOutside.Corpus
open scoped MatrixGroups

/-- The possible structures of an odd core-free group with `CyclicIndexTwo` and a central involution. -/
def CentralConclusion (G : Type) [Group G] [Finite G] : Prop :=
  IsPGroup 2 G ∨
  (∃ (F : Type) (_ : Field F) (_ : Finite F), ringChar F ≠ 2 ∧ 5 ≤ Nat.card F ∧
    Nonempty (commutator G ≃* SL(2, F))) ∨
  Nonempty (G ≃* SL(2, ZMod 3)) ∨
  (Nat.card G = 48 ∧ (∃ J : Subgroup G, J.Normal ∧ J.index = 2 ∧ Nonempty (J ≃* SL(2, ZMod 3))) ∧
    (Nonempty (G ≃* binaryOctahedral) ∨ Nonempty (G ≃* GL (Fin 2) (ZMod 3)))) ∨
  (commutator G = ⊤ ∧ Nat.card G = 5040 ∧
    Nonempty (G ⧸ Subgroup.center G ≃* alternatingGroup (Fin 7)))

variable {G : Type} [Group G] [Finite G]

instance fact_prime_three : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

theorem ringChar_zmod_three : ringChar (ZMod 3) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]; norm_num

theorem card_zmod_three : Nat.card (ZMod 3) = 3 := by simp

theorem card_sl23 : Nat.card SL(2, ZMod 3) = 24 := card_sl2_of_card_three (ZMod 3) card_zmod_three

variable [SemilinearEquivAut.{0}] [SpecialLinearGroupSylowQuaternion.{0}] [AutAlternatingBijectiveConj]

/-- Descent along a subgroup of index 2. -/
theorem central_descent (hP : CyclicIndexTwo G) (hO : OddCoreFree G) (M : Subgroup G) (hidx : M.index = 2)
    (hM : CentralConclusion M) : CentralConclusion G := by
  classical
  haveI hMn : M.Normal := Subgroup.normal_of_index_eq_two hidx
  have hcardG : Nat.card G = 2 * Nat.card M := by
    rw [← Subgroup.card_mul_index M, hidx, mul_comm]
  rcases hM with h2 | ⟨F, _, _, hF, h5, ⟨e⟩⟩ | ⟨⟨eM⟩⟩ | ⟨h48, ⟨J, -, hJi, ⟨eJ⟩⟩, -⟩ | ⟨hperf, h5040, ⟨e⟩⟩
  · -- a 2-group
    left
    obtain ⟨n, hn⟩ := h2.exists_card_eq
    exact IsPGroup.of_card (n := n + 1) (by rw [hcardG, hn, pow_succ, mul_comm])
  · -- `M' ≅ SL(2,q)`
    set Y : Subgroup G := (commutator M).map M.subtype
    have hY : Y = ⁅M, M⁆ := by
      simp only [Y, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    haveI : Y.Normal := hY ▸ Subgroup.commutator_normal M M
    have eY : Y ≃* SL(2, F) := (Subgroup.equivMapOfInjective _ _ M.subtype_injective).symm.trans e
    refine Or.inr (Or.inl ⟨F, inferInstance, inferInstance, hF, h5, ⟨?_⟩⟩)
    exact (MulEquiv.subgroupCongr (commutator_eq_of_normal_sl2 hP hO hF h5 Y eY)).trans eY
  · -- `M ≅ SL(2,3)`: `G ≅ GL(2,3)` or the binary octahedral group
    have hM24 : Nat.card M = 24 := by rw [Nat.card_congr eM.toEquiv, card_sl23]
    have hG48 : Nat.card G = 48 := by rw [hcardG, hM24]
    have hC := centralizer_le_of_normal_sl2 hP hO ringChar_zmod_three M eM
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨hG48, ⟨M, hMn, hidx, ⟨eM⟩⟩, ?_⟩)))
    by_cases hinv : ∃ g : G, g ∉ M ∧ g ^ 2 = 1
    · obtain ⟨g, hg, hg2⟩ := hinv
      exact Or.inr (Order48.nonempty_mulEquiv_GL23 hG48 M hMn eM hC g hg hg2)
    · push Not at hinv
      refine Or.inl (Order48.nonempty_mulEquiv_binaryOctahedral hG48 M hMn eM hC ?_)
      intro x y hx hy hx1 hy1
      have hxM : x ∈ M := by_contra fun h => hinv x h hx
      have hyM : y ∈ M := by_contra fun h => hinv y h hy
      exact involution_unique_of_sl23 eM hxM hyM hx hy hx1 hy1
  · -- `|M| = 48`: impossible
    exfalso
    have hG96 : Nat.card G = 96 := by rw [hcardG, h48]
    exact false_of_card_96 hP hO hG96 M (J.map M.subtype) (Subgroup.map_subtype_le _) h48
      ((Subgroup.equivMapOfInjective _ _ M.subtype_injective).symm.trans eJ)
  · -- `M ≅ 2.A₇`: impossible
    exact (false_of_double_cover_A7 hP hO M hidx hperf h5040 e).elim

variable [QuaternionSylowStructure.{0}] [ThompsonTransferLemma.{0}]

/-- The quaternion case gives `CentralConclusion`. -/
theorem central_of_quaternion (hP : CyclicIndexTwo G) (hO : OddCoreFree G) (S : Sylow 2 G)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup G) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    CentralConclusion G := by
  rcases quaternion_cases hP hO S hS with h | h | h | ⟨h, J, hJn, hJi, ⟨eJ⟩⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, ⟨J, hJn, hJi, ⟨eJ⟩⟩, Or.inl h⟩)))
    rw [← Subgroup.card_mul_index J, hJi, Nat.card_congr eJ.toEquiv, card_sl23]
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

/-- The central involution case, by induction on the order. -/
theorem central_cases (n : ℕ) : ∀ (G : Type) [Group G] [Finite G], Nat.card G = n → CyclicIndexTwo G →
    OddCoreFree G → ∀ z ∈ Subgroup.center G, orderOf z = 2 → CentralConclusion G := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ _ hn hP hO z hz hz2
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 G) := inferInstance
  have hzS : z ∈ (S : Subgroup G) := mem_sylow_of_central hz hz2 S
  by_cases hcomm : ∀ x ∈ (S : Subgroup G), ∀ y ∈ (S : Subgroup G), x * y = y * x
  · -- abelian Sylow 2-subgroup
    left
    exact Complement.isPGroup_of_abelian_sylow_of_central hO S hcomm z hzS hz hz2
      (card_sq_eq_one_le_four hP S hcomm)
  push Not at hcomm
  obtain ⟨x0, hx0, y0, hy0, hxy0⟩ := hcomm
  have hnab : ∃ x y : (S : Subgroup G), x * y ≠ y * x :=
    ⟨⟨x0, hx0⟩, ⟨y0, hy0⟩, fun h => hxy0 (congrArg Subtype.val h)⟩
  obtain ⟨C, hCS, hC, hCidx⟩ := hP S S.isPGroup'
  -- `C` has index exactly 2 in `S`
  have hCidx2 : C.relIndex (S : Subgroup G) = 2 := by
    rcases Nat.lt_or_ge (C.relIndex (S : Subgroup G)) 2 with h | h
    · exfalso
      have h1 : C.relIndex (S : Subgroup G) = 1 := by
        have hm := Subgroup.relIndex_mul_card C (S : Subgroup G)
        rw [inf_of_le_left hCS] at hm
        have : C.relIndex (S : Subgroup G) ≠ 0 := by
          intro h0; rw [h0, zero_mul] at hm; exact (Nat.card_pos (α := (S : Subgroup G))).ne' hm.symm
        omega
      have hSC : (S : Subgroup G) ≤ C := Subgroup.relIndex_eq_one.mp h1
      obtain ⟨g, hg⟩ := hC.exists_generator
      apply hxy0
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x0, hSC hx0⟩)
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y0, hSC hy0⟩)
      have hx' : x0 = (g : G) ^ i := by rw [← Subgroup.coe_zpow, hi]
      have hy' : y0 = (g : G) ^ j := by rw [← Subgroup.coe_zpow, hj]
      rw [hx', hy', ← zpow_add, ← zpow_add, add_comm]
    · omega
  -- a generator `a` of `C`, as an element of `S`
  obtain ⟨g, hg⟩ := hC.exists_generator
  set a : (S : Subgroup G) := ⟨g, hCS g.2⟩
  have hCa : C.subgroupOf (S : Subgroup G) = Subgroup.zpowers a := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff]
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
      exact ⟨i, Subtype.ext (by rw [Subgroup.coe_zpow]; exact congrArg Subtype.val hi)⟩
    · rintro ⟨i, rfl⟩
      rw [Subgroup.coe_zpow]
      exact Subgroup.zpow_mem _ g.2 i
  have hidxa : (Subgroup.zpowers a).index = 2 := by rw [← hCa, ← Subgroup.relIndex]; exact hCidx2
  -- `orderOf a` is a power of 2
  obtain ⟨k, hk⟩ : ∃ k : ℕ, orderOf a = 2 ^ k := by
    obtain ⟨m, hm⟩ := S.isPGroup'.exists_card_eq
    have hdvd : orderOf a ∣ 2 ^ m := hm ▸ orderOf_dvd_natCard a
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact ⟨k, hk⟩
  by_cases hq : ∀ x : (S : Subgroup G), x ∉ Subgroup.zpowers a → x ^ 2 ≠ 1
  · -- generalized quaternion
    obtain ⟨hk2, ⟨eQ⟩⟩ := TwoGroups.quaternion_type a k hk hidxa hq hnab
    exact central_of_quaternion hP hO S ⟨k + 1, by omega, by
      rw [show k + 1 - 2 = k - 1 by omega]; exact ⟨eQ⟩⟩
  · push Not at hq
    obtain ⟨b, hb, hb2⟩ := hq
    obtain ⟨hk2, -⟩ := TwoGroups.conj_exponent_cases a b k hk hidxa hb hb2 hnab
    obtain ⟨M, hMidx⟩ := exists_index_two_of_involution S hz hz2 a b hidxa hb hb2 hnab
    haveI hMn : M.Normal := Subgroup.normal_of_index_eq_two hMidx
    -- `z` is a square, so lies in `M`
    have hzM : z ∈ M := by
      set zS : (S : Subgroup G) := ⟨z, hzS⟩
      have hzS_center : zS ∈ Subgroup.center (S : Subgroup G) := by
        rw [Subgroup.mem_center_iff]
        intro y
        exact Subtype.ext (Subgroup.mem_center_iff.mp hz y)
      have hzA : zS ∈ Subgroup.zpowers a :=
        TwoGroups.center_le_of_index_two (Subgroup.isCyclic_zpowers a) hidxa hnab hzS_center
      set w := a ^ (2 ^ (k - 2))
      have hw : w ^ 2 = a ^ (2 ^ (k - 1)) := by
        rw [← pow_mul, ← pow_succ, show k - 2 + 1 = k - 1 by omega]
      have hinv : (a ^ (2 ^ (k - 1))) ^ 2 = 1 := by
        rw [← pow_mul, ← pow_succ, show k - 1 + 1 = k by omega, ← hk, pow_orderOf_eq_one]
      have hne : a ^ (2 ^ (k - 1)) ≠ 1 := by
        intro h
        have := orderOf_dvd_of_pow_eq_one h
        rw [hk] at this
        have := Nat.le_of_dvd (by positivity) this
        have : 2 ^ k ≤ 2 ^ (k - 1) := this
        have := (Nat.pow_le_pow_iff_right (by norm_num)).mp this
        omega
      have hz1 : zS ≠ 1 := fun h => by
        have : z = 1 := congrArg Subtype.val h
        rw [this, orderOf_one] at hz2; norm_num at hz2
      have hzS2 : zS ^ 2 = 1 := Subtype.ext (by
        simp only [zS, Subgroup.coe_pow, Subgroup.coe_one]
        rw [← hz2]; exact pow_orderOf_eq_one z)
      have heq : a ^ (2 ^ (k - 1)) = zS :=
        cyclic_involution_unique (Subgroup.isCyclic_zpowers a) (Subgroup.pow_mem _ (Subgroup.mem_zpowers a) _)
          hzA hinv hzS2 hne hz1
      have hzsq : z = ((w : (S : Subgroup G)) : G) ^ 2 := by
        rw [← Subgroup.coe_pow, hw, heq]
      rw [hzsq]
      exact Subgroup.sq_mem_of_index_two hMidx _
    have hcardM : Nat.card M < n := by
      rw [← hn, ← Subgroup.card_mul_index M, hMidx]
      have := Nat.card_pos (α := M)
      omega
    have hM := ih (Nat.card M) hcardM M rfl (cyclicIndexTwo_subgroup hP M)
      (Complement.oddCoreFree_of_normal hO M) ⟨z, hzM⟩ (by
        rw [Subgroup.mem_center_iff]
        intro y
        exact Subtype.ext (Subgroup.mem_center_iff.mp hz y))
      (by rw [Subgroup.orderOf_mk]; exact hz2)
    exact central_descent hP hO M hMidx hM

end CFSGOutside.GiuliettiKorchmaros
