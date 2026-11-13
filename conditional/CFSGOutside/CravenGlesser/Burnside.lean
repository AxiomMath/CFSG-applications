import CFSGOutside.CravenGlesser.Basic

/-!
# Burnside: odd-order automorphisms act faithfully on `P / Φ(P)`

An automorphism of odd order of a finite 2-group `P` with `x⁻¹ * ψ x ∈ Φ(P)` for every `x` is trivial.
The proof counts: an automorphism of odd prime order permutes each coset of `Φ(P)`, which has 2-power
size, so it fixes a point of each coset; its fixed points then generate `P` modulo `Φ(P)`.
-/

namespace CFSGOutside.CravenGlesser

open Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- Automorphisms acting trivially modulo the Frattini subgroup. -/
def frattiniKernel (G : Type*) [Group G] : Subgroup (MulAut G) where
  carrier := {σ | ∀ x, x⁻¹ * σ x ∈ frattini G}
  mul_mem' {σ τ} hσ hτ x := by
    have hc := (frattini_characteristic (G := G)).fixed σ
    have h1 : σ (x⁻¹ * τ x) ∈ frattini G := by
      have := hτ x
      rw [← hc] at this
      exact this
    have : x⁻¹ * (σ * τ) x = (x⁻¹ * σ x) * σ (x⁻¹ * τ x) := by
      rw [MulAut.mul_apply, map_mul, map_inv]; group
    rw [this]
    exact mul_mem (hσ x) (by simpa using h1)
  one_mem' x := by simp
  inv_mem' {σ} hσ x := by
    have := hσ (σ⁻¹ x)
    have h : x⁻¹ * σ⁻¹ x = ((σ⁻¹ x)⁻¹ * σ (σ⁻¹ x))⁻¹ := by
      rw [MulAut.inv_apply, MulEquiv.apply_symm_apply]; group
    rw [h]
    exact inv_mem this

/-- The subgroup of fixed points of an automorphism. -/
def fixedSubgroup (σ : MulAut G) : Subgroup G where
  carrier := {x | σ x = x}
  mul_mem' {a b} ha hb := by simp_all [map_mul]
  one_mem' := by simp
  inv_mem' {a} ha := by simp_all [map_inv]

theorem eq_one_of_mem_frattini (hG : IsPGroup 2 G) (ψ : MulAut G) (hodd : Odd (orderOf ψ))
    (hψ : ∀ x, x⁻¹ * ψ x ∈ frattini G) : ψ = 1 := by
  classical
  by_contra hne
  set n := orderOf ψ with hn
  have hn0 : n ≠ 0 := (orderOf_pos ψ).ne'
  have hn1 : n ≠ 1 := fun h => hne (orderOf_eq_one_iff.mp h)
  set q := n.minFac with hq
  have hqp : q.Prime := Nat.minFac_prime hn1
  have hqn : q ∣ n := Nat.minFac_dvd n
  have hq2 : q ≠ 2 := by
    intro h
    rw [h] at hqn
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hqn)
  haveI : Fact q.Prime := ⟨hqp⟩
  set ψ' := ψ ^ (n / q) with hψ'
  have hord : orderOf ψ' = q := orderOf_pow_orderOf_div hn0 hqn
  have hK : ψ ∈ frattiniKernel G := hψ
  have hK' : zpowers ψ' ≤ frattiniKernel G := by
    rw [zpowers_le]; exact pow_mem hK _
  set H := zpowers ψ'
  have hHp : IsPGroup q H := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hord, pow_one]
  -- every coset of the Frattini subgroup contains a fixed point of `ψ'`
  have hfixed : ∀ x : G, ∃ y : G, x⁻¹ * y ∈ frattini G ∧ ψ' y = y := by
    intro x
    let S := {y : G // x⁻¹ * y ∈ frattini G}
    have hmem : ∀ h : H, ∀ y : S, x⁻¹ * (h : MulAut G) y.1 ∈ frattini G := by
      intro h y
      have h1 := hK' h.2 y.1
      have : x⁻¹ * (h : MulAut G) y.1 = (x⁻¹ * y.1) * (y.1⁻¹ * (h : MulAut G) y.1) := by group
      rw [this]; exact mul_mem y.2 h1
    letI : MulAction H S :=
      { smul := fun h y => ⟨(h : MulAut G) y.1, hmem h y⟩
        one_smul := fun y => by apply Subtype.ext; rfl
        mul_smul := fun a b y => by apply Subtype.ext; rfl }
    have hcard : Nat.card S = Nat.card (frattini G) := by
      apply Nat.card_congr
      exact
        { toFun := fun y => ⟨x⁻¹ * y.1, y.2⟩
          invFun := fun f => ⟨x * f.1, by simpa using f.2⟩
          left_inv := fun y => by apply Subtype.ext; simp
          right_inv := fun f => by apply Subtype.ext; simp }
    have hmod := hHp.card_modEq_card_fixedPoints S
    by_contra hnone
    push Not at hnone
    have hempty : Nat.card (MulAction.fixedPoints H S) = 0 := by
      rw [Nat.card_eq_zero]
      left
      constructor
      rintro ⟨y, hy⟩
      apply hnone y.1 y.2
      have := hy ⟨ψ', mem_zpowers ψ'⟩
      exact congrArg Subtype.val this
    rw [hempty, hcard] at hmod
    have hdvd : q ∣ Nat.card (frattini G) := Nat.modEq_zero_iff_dvd.mp hmod
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hG.to_subgroup (frattini G))
    rw [hk] at hdvd
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).mp (hqp.dvd_of_dvd_pow hdvd))
  -- hence the fixed points and the Frattini subgroup generate `G`
  have htop : fixedSubgroup ψ' ⊔ frattini G = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, hy, hyf⟩ := hfixed x
    have : x = y * (x⁻¹ * y)⁻¹ := by group
    rw [this]
    exact mul_mem (mem_sup_left hyf) (mem_sup_right (inv_mem hy))
  have hfix := frattini_nongenerating htop
  have : ψ' = 1 := by
    ext x
    have : x ∈ fixedSubgroup ψ' := by rw [hfix]; trivial
    exact this
  rw [this, orderOf_one] at hord
  exact hqp.one_lt.ne hord

end CFSGOutside.CravenGlesser
