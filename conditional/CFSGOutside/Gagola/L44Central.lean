import CFSGOutside.Gagola.SkewSymm
import CFSGOutside.Gagola.PCube

/-!
# Gagola, Lemma 4.4: no special element is central

Let `N ⊴ D` with `D/N` nonabelian of order `p³` and `θ ∈ Irr N` invariant. If a special `g ∉ N` is
central modulo `N`, then every element of `D` is special, and there are `p + 1` pairwise non-fused
special elements (`1, g, …, g^{p-1}` and a noncentral element).
-/

namespace CFSGOutside.Gagola

open scoped BigOperators Pointwise
open Classical

noncomputable section

variable {D : Type*} [Group D] [Fintype D] {N : Subgroup D} [hN : N.Normal] {θ : N → ℂ}

theorem comm_mem_iff_mk (a b : D) :
    a * b * a⁻¹ * b⁻¹ ∈ N ↔ (a : D ⧸ N) * b = b * a := by
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  constructor
  · intro h
    have := hN.conj_mem _ (N.inv_mem h) (b⁻¹ * a⁻¹)
    convert this using 1; group
  · intro h
    have := hN.conj_mem _ (N.inv_mem h) (a * b)
    convert this using 1; group

theorem many_special_of_central (hθ : θ ∈ Irr N) (hinv : IsInvariant (G := D) θ) {p : ℕ}
    [hp : Fact p.Prime] (hQ : Nat.card (D ⧸ N) = p ^ 3)
    (hnab : ∃ a b : D ⧸ N, a * b ≠ b * a) {g : D} (hsp : IsSpecial θ g) (hgN : g ∉ N)
    (hgc : ∀ d : D, d * g * d⁻¹ * g⁻¹ ∈ N) :
    ∃ T : Finset D, T.card = p + 1 ∧ (∀ x ∈ T, IsSpecial θ x) ∧
      ∀ x ∈ T, ∀ y ∈ T, (∃ u : D, u⁻¹ * y * u * x⁻¹ ∈ N) → x = y := by
  set π : D →* D ⧸ N := QuotientGroup.mk' N
  have hπ : ∀ a : D, π a = (a : D ⧸ N) := fun _ => rfl
  have hπ1 : ∀ a : D, π a = 1 ↔ a ∈ N := fun a => QuotientGroup.eq_one_iff a
  set gb := π g
  have hgb : gb ∈ Subgroup.center (D ⧸ N) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective y
    exact (comm_mem_iff_mk d g).mp (hgc d)
  have hgb1 : gb ≠ 1 := fun h => hgN ((hπ1 g).mp h)
  have hord : orderOf gb = p := pcube_orderOf_central hQ hnab hgb hgb1
  -- every element is special
  have hall : ∀ x : D, IsSpecial θ x := by
    intro x
    by_cases hx : π x ∈ Subgroup.center (D ⧸ N)
    · obtain ⟨i, hi⟩ := pcube_exists_pow_of_central hQ hnab hgb hgb1 hx
      have hmem : (g ^ i)⁻¹ * x ∈ N := by
        rw [← hπ1, map_mul, map_inv, map_pow, ← hi, inv_mul_cancel]
      have := isSpecial_of_central_power hθ hinv hsp hgc i ⟨_, hmem⟩
      simpa using this
    · obtain ⟨ψ, hψ, hfix⟩ := exists_ext_fixed hθ hinv hsp hgc x
      have hgx : g * x * g⁻¹ * x⁻¹ ∈ N := by
        have := N.inv_mem (hgc x); simpa [mul_assoc] using this
      refine isSpecial_of_explicit hθ hψ hfix hgx fun d hd => ?_
      have hcomm : π d * π x = π x * π d := (comm_mem_iff_mk d x).mp hd
      obtain ⟨i, j, hij⟩ := pcube_centralizer hQ hnab hx hgb hgb1 hcomm
      have hmem : (x ^ i * g ^ j)⁻¹ * d ∈ N := by
        rw [← hπ1, map_mul, map_inv, map_mul, map_pow, map_pow, ← hij, inv_mul_cancel]
      exact ⟨i, j, ⟨_, hmem⟩, by simp only; group⟩
  -- a noncentral element
  obtain ⟨a, b, hab⟩ := hnab
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective a
  have hx₀ : π x₀ ∉ Subgroup.center (D ⧸ N) := fun h => hab (Subgroup.mem_center_iff.mp h b).symm
  set S := (Finset.range p).image (fun i => g ^ i)
  have hinj : Set.InjOn (fun i => g ^ i) (Finset.range p : Set ℕ) := by
    intro i hi j hj hij
    have h1 : gb ^ i = gb ^ j := by simp only [gb, ← map_pow]; exact congrArg π hij
    have := pow_injOn_Iio_orderOf (x := gb) (by rw [hord]; exact Finset.mem_range.mp hi)
      (by rw [hord]; exact Finset.mem_range.mp hj) h1
    exact this
  have hcardS : S.card = p := by rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hSc : ∀ y ∈ S, π y ∈ Subgroup.center (D ⧸ N) := by
    intro y hy
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
    rw [map_pow]; exact Subgroup.pow_mem _ hgb i
  have hx₀S : x₀ ∉ S := fun h => hx₀ (hSc x₀ h)
  refine ⟨insert x₀ S, by rw [Finset.card_insert_of_notMem hx₀S, hcardS], fun x _ => hall x, ?_⟩
  -- pairwise non-fused
  have hfuse : ∀ x y : D, (∃ u : D, u⁻¹ * y * u * x⁻¹ ∈ N) → ∃ w : D ⧸ N, w⁻¹ * π y * w = π x := by
    rintro x y ⟨u, hu⟩
    refine ⟨π u, ?_⟩
    have := (hπ1 _).mpr hu
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one] at this
    exact this
  have hcent_conj : ∀ (w z : D ⧸ N), z ∈ Subgroup.center (D ⧸ N) → w⁻¹ * z * w = z := by
    intro w z hz
    rw [mul_assoc, ← Subgroup.mem_center_iff.mp hz w, ← mul_assoc, inv_mul_cancel, one_mul]
  intro x hx y hy hxy
  obtain ⟨w, hw⟩ := hfuse x y hxy
  rcases Finset.mem_insert.mp hx with rfl | hxS <;> rcases Finset.mem_insert.mp hy with rfl | hyS
  · rfl
  · exfalso; apply hx₀; rw [← hw, hcent_conj w _ (hSc y hyS)]; exact hSc y hyS
  · exfalso; apply hx₀
    have : π y = w * π x * w⁻¹ := by rw [← hw]; group
    rw [this, show w * π x * w⁻¹ = (w⁻¹)⁻¹ * π x * w⁻¹ by group, hcent_conj _ _ (hSc x hxS)]
    exact hSc x hxS
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hxS
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hyS
    rw [hcent_conj w _ (hSc _ hyS)] at hw
    have h1 : gb ^ j = gb ^ i := by simpa [gb, map_pow] using hw
    have := pow_injOn_Iio_orderOf (x := gb) (by rw [hord]; exact Finset.mem_range.mp hj)
      (by rw [hord]; exact Finset.mem_range.mp hi) h1
    rw [this]

end

end CFSGOutside.Gagola
