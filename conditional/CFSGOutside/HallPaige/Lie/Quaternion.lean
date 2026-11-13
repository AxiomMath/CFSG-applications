import CFSGOutside.HallPaige.Reduction
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# A quaternion subgroup makes a group good

If a finite group contains elements `I`, `J` with `I⁴ = 1 ≠ I²`, `J² = I²`, `I J = J I⁻¹` and
`J ∉ ⟨I⟩`, then the subgroup they generate is a non-cyclic `2`-group (a quaternion group of order
`8`), so the group is good (`CFSGOutside.HallPaige.isGood_of_quaternion`).
-/

namespace CFSGOutside.HallPaige

variable {X : Type*} [Group X]

section

variable {I J : X}

theorem zpow_mul_J (hIJ : I * J = J * I⁻¹) (k : ℤ) : I ^ k * J = J * I ^ (-k) := by
  have hIJ' : I⁻¹ * J = J * I := by
    calc I⁻¹ * J = I⁻¹ * (J * I⁻¹) * I := by group
      _ = I⁻¹ * (I * J) * I := by rw [hIJ]
      _ = J * I := by group
  induction k using Int.induction_on with
  | zero => simp
  | succ m ih =>
    rw [zpow_add_one, mul_assoc, hIJ, ← mul_assoc, ih, mul_assoc, ← zpow_neg_one,
      ← zpow_add]
    congr 2; ring
  | pred m ih =>
    rw [zpow_sub_one, mul_assoc, hIJ', ← mul_assoc, ih, mul_assoc, ← zpow_add_one]
    congr 2; ring

/-- The subgroup `{Iᵏ, J Iᵏ}`. -/
def quatSub (hI4 : I ^ 4 = 1) (hJ2 : J ^ 2 = I ^ 2) (hIJ : I * J = J * I⁻¹) : Subgroup X where
  carrier := {x | ∃ k : ℤ, x = I ^ k ∨ x = J * I ^ k}
  mul_mem' := by
    rintro x y ⟨a, rfl | rfl⟩ ⟨b, rfl | rfl⟩
    · exact ⟨a + b, Or.inl (zpow_add I a b).symm⟩
    · refine ⟨b - a, Or.inr ?_⟩
      rw [← mul_assoc, zpow_mul_J hIJ, mul_assoc, ← zpow_add]; congr 2; ring
    · exact ⟨a + b, Or.inr (by rw [mul_assoc, ← zpow_add])⟩
    · refine ⟨2 + (b - a), Or.inl ?_⟩
      calc J * I ^ a * (J * I ^ b) = J * (I ^ a * J) * I ^ b := by group
        _ = J * (J * I ^ (-a)) * I ^ b := by rw [zpow_mul_J hIJ]
        _ = J ^ 2 * (I ^ (-a) * I ^ b) := by rw [sq]; group
        _ = I ^ (2 + (b - a)) := by
          rw [hJ2, ← zpow_add, ← zpow_natCast, ← zpow_add]; congr 1; push_cast; ring
  one_mem' := ⟨0, Or.inl (by simp)⟩
  inv_mem' := by
    rintro x ⟨a, rfl | rfl⟩
    · exact ⟨-a, Or.inl (zpow_neg I a).symm⟩
    · refine ⟨a + 2, Or.inr ?_⟩
      have hJ4 : J ^ 4 = 1 := by
        rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, hJ2, ← pow_mul]; exact hI4
      have hJinv : J⁻¹ = J * I ^ (2 : ℤ) := by
        rw [inv_eq_iff_mul_eq_one, ← mul_assoc, ← sq, hJ2]
        rw [show (I ^ (2 : ℤ)) = I ^ 2 from zpow_natCast I 2, ← pow_add]
        exact hI4
      rw [mul_inv_rev, hJinv, ← mul_assoc, ← zpow_neg, zpow_mul_J hIJ, neg_neg, mul_assoc,
        ← zpow_add]

theorem pow_four_of_mem_quatSub (hI4 : I ^ 4 = 1) (hJ2 : J ^ 2 = I ^ 2) (hIJ : I * J = J * I⁻¹)
    {x : X} (hx : x ∈ quatSub hI4 hJ2 hIJ) : x ^ 4 = 1 := by
  obtain ⟨a, rfl | rfl⟩ := hx
  · rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hI4, one_zpow]
  · have h2 : (J * I ^ a) ^ 2 = I ^ 2 := by
      calc (J * I ^ a) ^ 2 = J * (I ^ a * J) * I ^ a := by rw [sq]; group
        _ = J * (J * I ^ (-a)) * I ^ a := by rw [zpow_mul_J hIJ]
        _ = J ^ 2 * (I ^ (-a) * I ^ a) := by rw [sq]; group
        _ = I ^ 2 := by rw [hJ2, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, h2, ← pow_mul]; exact hI4

end

/-- **The quaternion criterion.** -/
theorem isGood_of_quaternion [Finite X] {I J : X} (hI4 : I ^ 4 = 1) (hI2 : I ^ 2 ≠ 1)
    (hJ2 : J ^ 2 = I ^ 2) (hIJ : I * J = J * I⁻¹) (hJ : ∀ k : ℤ, J ≠ I ^ k) : IsGood X := by
  set Q := quatSub hI4 hJ2 hIJ
  have hQ2 : IsPGroup 2 Q := by
    intro x
    exact ⟨2, by ext; simpa using pow_four_of_mem_quatSub hI4 hJ2 hIJ x.2⟩
  have hnc : ¬ IsCyclic Q := by
    intro hc
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Q)
    have hord : orderOf g = Nat.card Q := orderOf_eq_card_of_forall_mem_zpowers hg
    have hg4 : orderOf g ∣ 4 := orderOf_dvd_of_pow_eq_one
      (Subtype.ext (by simpa using pow_four_of_mem_quatSub hI4 hJ2 hIJ g.2))
    have hIord : orderOf I = 4 := by
      have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := I) (by simpa using hI2)
        (by simpa using hI4)
      simpa using this
    have hIQ : I ∈ Q := ⟨1, Or.inl (zpow_one I).symm⟩
    have hJQ : J ∈ Q := ⟨0, Or.inr (by simp)⟩
    have hle : Subgroup.zpowers I ≤ Q := (Subgroup.zpowers_le).2 hIQ
    have hne : Subgroup.zpowers I ≠ Q := by
      intro h
      rw [← h] at hJQ
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hJQ
      exact hJ k hk.symm
    have hlt : Nat.card (Subgroup.zpowers I) < Nat.card Q := by
      rcases (Subgroup.card_le_of_le hle).lt_or_eq with h | h
      · exact h
      · exact absurd (Subgroup.eq_of_le_of_card_ge hle h.ge) hne
    rw [Nat.card_zpowers, hIord] at hlt
    have := Nat.le_of_dvd (by norm_num) hg4
    omega
  exact isGood_of_injective hQ2 hnc Q.subtype Q.subtype_injective

/-- The quaternion criterion inside a subgroup. -/
theorem Subgroup.isGood_of_quaternion [Finite X] (H : Subgroup X) {I J : X} (hIH : I ∈ H)
    (hJH : J ∈ H) (hI4 : I ^ 4 = 1) (hI2 : I ^ 2 ≠ 1) (hJ2 : J ^ 2 = I ^ 2)
    (hIJ : I * J = J * I⁻¹) (hJ : ∀ k : ℤ, J ≠ I ^ k) : IsGood H :=
  CFSGOutside.HallPaige.isGood_of_quaternion (I := ⟨I, hIH⟩) (J := ⟨J, hJH⟩) (Subtype.ext hI4)
    (fun h => hI2 (congrArg Subtype.val h)) (Subtype.ext hJ2) (Subtype.ext hIJ)
    (fun k h => hJ k (by simpa using congrArg Subtype.val h))

/-- The quaternion criterion; `J ∉ ⟨I⟩` follows from the relations. -/
theorem not_mem_zpowers_of_quaternion {I J : X} (hI2 : I ^ 2 ≠ 1) (hIJ : I * J = J * I⁻¹)
    (k : ℤ) : J ≠ I ^ k := by
  rintro rfl
  apply hI2
  have h : I * I ^ k = I ^ k * I := by
    rw [← zpow_one_add, ← zpow_add_one, add_comm]
  have h' : I ^ k * I = I ^ k * I⁻¹ := h.symm.trans hIJ
  have := mul_left_cancel h'
  calc I ^ 2 = I * I := sq I
    _ = I * I⁻¹ := by rw [← this]
    _ = 1 := mul_inv_cancel I

/-- The quaternion criterion inside a subgroup, without the hypothesis `J ∉ ⟨I⟩`. -/
theorem Subgroup.isGood_of_quaternion' [Finite X] (H : Subgroup X) {I J : X} (hIH : I ∈ H)
    (hJH : J ∈ H) (hI4 : I ^ 4 = 1) (hI2 : I ^ 2 ≠ 1) (hJ2 : J ^ 2 = I ^ 2)
    (hIJ : I * J = J * I⁻¹) : IsGood H :=
  Subgroup.isGood_of_quaternion H hIH hJH hI4 hI2 hJ2 hIJ (not_mem_zpowers_of_quaternion hI2 hIJ)

end CFSGOutside.HallPaige
