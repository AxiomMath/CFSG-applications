import CFSGOutside.Corpus.SpecialLinearGroupSylowQuaternion
import CFSGOutside.GiuliettiKorchmaros.Thm61Key
import CFSGOutside.GiuliettiKorchmaros.Thm61Centralizer

/-!
# Theorem 6.1: normal subgroups isomorphic to `SL(2,q)`
-/

namespace CFSGOutside.GiuliettiKorchmaros

open CFSGOutside.Corpus
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

/-- A finite field of odd characteristic has 3 or at least 5 elements. -/
theorem card_three_or_five_le (F : Type) [Field F] [Finite F] (hF : ringChar F ≠ 2) :
    Nat.card F = 3 ∨ 5 ≤ Nat.card F := by
  haveI := Fintype.ofFinite F
  obtain ⟨p, n, hp, hcard⟩ : ∃ p n, Nat.Prime p ∧ Nat.card F = p ^ (n : ℕ) := by
    obtain ⟨p, hchar, n, hp, hc⟩ := FiniteField.card' F
    exact ⟨p, n, hp, by rw [Nat.card_eq_fintype_card, hc]⟩
  have hchar : ringChar F = p := by
    haveI : Fact p.Prime := ⟨hp⟩
    haveI := charP_of_card_eq_prime_pow (R := F) (by rw [← Nat.card_eq_fintype_card, hcard])
    exact ringChar.eq F p
  have hp2 : p ≠ 2 := hchar ▸ hF
  have hodd : Odd (Nat.card F) := hcard ▸ (hp.odd_of_ne_two hp2).pow
  have h2 : 2 ≤ Nat.card F := by
    haveI : Nontrivial F := inferInstance
    exact Finite.one_lt_card
  obtain ⟨k, hk⟩ := hodd
  omega

/-- A field with at least 4 elements has `a ≠ 0` with `a ^ 2 ≠ 1`. -/
theorem exists_ne_zero_sq_ne_one (F : Type) [Field F] [Finite F] (h4 : 4 ≤ Nat.card F) :
    ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1 := by
  classical
  by_contra h
  push Not at h
  haveI := Fintype.ofFinite F
  have hsub : (Finset.univ : Finset F) ⊆ {0, 1, -1} := by
    intro a _
    by_cases ha : a = 0
    · simp [ha]
    · have := h a ha
      have h' : (a - 1) * (a + 1) = 0 := by linear_combination this
      rcases mul_eq_zero.1 h' with h1 | h1
      · simp [sub_eq_zero.1 h1]
      · simp [eq_neg_of_add_eq_zero_left h1]
  have := Finset.card_le_card hsub
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at this
  have h3 : ({0, 1, -1} : Finset F).card ≤ 3 := Finset.card_le_three
  omega

variable [SpecialLinearGroupSylowQuaternion.{0}]

/-- A normal subgroup `Y ≅ SL(2,F)` of an odd core-free group with `CyclicIndexTwo` contains its centralizer, and
the centralizer is the center of `Y`. -/
theorem centralizer_le_of_normal_sl2' (hP : CyclicIndexTwo G) (hO : OddCoreFree G) {F : Type} [Field F]
    [Finite F] (hF : ringChar F ≠ 2) (Y : Subgroup G) [Y.Normal] (eY : Y ≃* SL(2, F)) :
    Subgroup.centralizer (Y : Set G) ≤ Y ∧ Nat.card (Subgroup.centralizer (Y : Set G)) ≤ 2 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 SL(2, F)) := inferInstance
  obtain ⟨k, hk, ⟨eP⟩⟩ := SpecialLinearGroupSylowQuaternion.specialLinearGroup_sylow_quaternion F hF P
  -- the quaternion subgroup `Q ≤ Y` of `G`
  set Q : Subgroup G := ((P : Subgroup SL(2, F)).map eY.symm.toMonoidHom).map Y.subtype with hQ
  have hQY : Q ≤ Y := Subgroup.map_subtype_le _
  have hQcard : Nat.card Q = 4 * 2 ^ k := by
    rw [hQ, Subgroup.card_map_of_injective Y.subtype_injective,
      Subgroup.card_map_of_injective eY.symm.injective, Nat.card_congr eP.toEquiv,
      Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hQ2 : IsPGroup 2 Q := by
    apply IsPGroup.of_card (n := k + 2)
    rw [hQcard, pow_add]; ring
  have hQ8 : 8 ≤ Nat.card Q := by
    rw [hQcard]
    have : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  have hQexp : ∀ q ∈ Q, q ^ (Nat.card Q / 2) = 1 := by
    intro q hq
    have hhalf : Nat.card Q / 2 = 2 ^ (k + 1) := by rw [hQcard, pow_succ]; omega
    rw [hhalf]
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hq
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hy
    have h1 := quaternion_pow_eq_one k hk (eP ⟨s, hs⟩)
    rw [← map_pow, MulEquiv.map_eq_one_iff] at h1
    have h2 : s ^ (2 ^ (k + 1)) = 1 := by simpa using congrArg Subtype.val h1
    simp only [MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
    rw [← Subgroup.coe_pow, ← map_pow, h2, map_one, Subgroup.coe_one]
  -- `Y ⊓ C_G(Y)` is the center of `Y`, of order 2
  have hcenter : ∀ (c : G) (hc : c ∈ Y ⊓ Subgroup.centralizer (Y : Set G)),
      (⟨c, (Subgroup.mem_inf.mp hc).1⟩ : Y) ∈ Subgroup.center Y := by
    intro c hc
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 y y.2)
  have hZ2 : Nat.card (Subgroup.center Y) = 2 := by
    rw [← LinearTwo.card_center_SL2 F hF, ← Subgroup.map_center_eq eY]
    exact (Subgroup.card_map_of_injective eY.injective).symm
  have hYC : Nat.card (Y ⊓ Subgroup.centralizer (Y : Set G) : Subgroup G) ≤ 2 := by
    rw [← hZ2]
    refine Nat.card_le_card_of_injective (fun c => ⟨⟨c, (Subgroup.mem_inf.mp c.2).1⟩, hcenter c c.2⟩) ?_
    intro a b h
    exact Subtype.ext (congrArg (fun t : Subgroup.center Y => ((t : Y) : G)) h)
  have hC2 := card_centralizer_le_two hP hO Y hQY hQ2 hQ8 hQexp hYC
  -- the image of `Z(Y)` lies in `C_G(Y)` and has 2 elements, so it is all of it
  set Zc : Subgroup G := (Subgroup.center Y).map Y.subtype
  have hZc : Zc ≤ Subgroup.centralizer (Y : Set G) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨y, hy⟩)
  have hZccard : Nat.card Zc = 2 := by rw [Subgroup.card_map_of_injective Y.subtype_injective, hZ2]
  have heq := Subgroup.eq_of_le_of_card_ge hZc (by omega)
  refine ⟨?_, hC2⟩
  rw [← heq]
  exact Subgroup.map_subtype_le _

theorem centralizer_le_of_normal_sl2 (hP : CyclicIndexTwo G) (hO : OddCoreFree G) {F : Type} [Field F]
    [Finite F] (hF : ringChar F ≠ 2) (Y : Subgroup G) [Y.Normal] (eY : Y ≃* SL(2, F)) :
    Subgroup.centralizer (Y : Set G) ≤ Y :=
  (centralizer_le_of_normal_sl2' hP hO hF Y eY).1

/-- `SL(2,F)`, `|F| ≥ 4`, is perfect, and so is any group isomorphic to it. -/
theorem commutator_eq_top_of_sl2 {H : Type} [Group H] {F : Type} [Field F] [Finite F]
    (h4 : 4 ≤ Nat.card F) (e : H ≃* SL(2, F)) : commutator H = ⊤ := by
  obtain ⟨a, ha, hasq⟩ := exists_ne_zero_sq_ne_one F h4
  have htop : commutator SL(2, F) = ⊤ := Matrix.SL2.commutator_eq_top ha hasq
  have hmap : (commutator H).map e.toMonoidHom = commutator SL(2, F) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective]
  rw [htop] at hmap
  apply eq_top_iff.2
  intro x _
  have : e x ∈ (commutator H).map e.toMonoidHom := hmap ▸ Subgroup.mem_top _
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp this
  rwa [← e.injective hyx]

/-- A normal subgroup of a group is contained in its commutator subgroup if it is perfect. -/
theorem le_commutator_of_perfect (Y : Subgroup G) (hY : commutator Y = ⊤) : Y ≤ commutator G := by
  intro y hy
  have h1 : (⟨y, hy⟩ : Y) ∈ commutator Y := hY ▸ Subgroup.mem_top _
  have h2 : (commutator Y).map Y.subtype ≤ commutator G := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  exact h2 ⟨_, h1, rfl⟩

/-- Lemma 6.10/6.11, `q ≥ 5`: a normal `SL(2,q)` is the commutator subgroup. -/
theorem commutator_eq_of_normal_sl2 [SemilinearEquivAut.{0}] (hP : CyclicIndexTwo G) (hO : OddCoreFree G)
    {F : Type} [Field F] [Finite F] (hF : ringChar F ≠ 2) (h5 : 5 ≤ Nat.card F) (Y : Subgroup G) [Y.Normal]
    (eY : Y ≃* SL(2, F)) : commutator G = Y := by
  apply le_antisymm
  · have h1 := Key.commutator_le_of_normal_sl2 hF Y eY
    rwa [sup_of_le_left (centralizer_le_of_normal_sl2 hP hO hF Y eY)] at h1
  · exact le_commutator_of_perfect Y (commutator_eq_top_of_sl2 (by omega) eY)

end CFSGOutside.GiuliettiKorchmaros
