import Mathlib

/-!
# An extension lemma for groups with an index-two subgroup
-/

namespace CFSGOutside.GiuliettiKorchmaros.Order48

/-- (1) Extension lemma: two groups with index-2 subgroups identified compatibly are isomorphic. -/
theorem nonempty_mulEquiv_of_index_two {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    (J : Subgroup X) (J' : Subgroup Y) (hJ : J.index = 2) (hJ' : J'.index = 2) (ι : J ≃* J')
    (y : X) (hy : y ∉ J) (Y₀ : Y) (hY₀ : Y₀ ∉ J')
    (hconj : ∀ j : J, ((ι ⟨y * j * y⁻¹, (Subgroup.normal_of_index_eq_two hJ).conj_mem _ j.2 y⟩ : J') : Y)
      = Y₀ * ι j * Y₀⁻¹)
    (hsq : ((ι ⟨y ^ 2, Subgroup.sq_mem_of_index_two hJ y⟩ : J') : Y) = Y₀ ^ 2) :
    Nonempty (X ≃* Y) := by
  classical
  have hyi : y⁻¹ ∉ J := fun h => hy (by simpa using J.inv_mem h)
  have hmem : ∀ x : X, x ∉ J → y⁻¹ * x ∈ J := fun x hx => by
    rw [Subgroup.mul_mem_iff_of_index_two hJ]; exact iff_of_false hyi hx
  let ψ : X → Y := fun x => if h : x ∈ J then (ι ⟨x, h⟩ : Y)
    else Y₀ * (ι ⟨y⁻¹ * x, hmem x h⟩ : Y)
  -- conjugation relation in the other direction
  have hc : ∀ (x : X) (hx : x ∈ J) (h2 : y⁻¹ * x * y ∈ J),
      Y₀ * (ι ⟨y⁻¹ * x * y, h2⟩ : Y) = (ι ⟨x, hx⟩ : Y) * Y₀ := by
    intro x hx h2
    have := hconj ⟨y⁻¹ * x * y, h2⟩
    have e : (⟨y * (y⁻¹ * x * y) * y⁻¹, (Subgroup.normal_of_index_eq_two hJ).conj_mem _ h2 y⟩ : J)
        = ⟨x, hx⟩ := Subtype.ext (by simp [mul_assoc])
    rw [e] at this
    rw [this]; group
  have hmul : ∀ x x', ψ (x * x') = ψ x * ψ x' := by
    intro x x'
    by_cases hx : x ∈ J <;> by_cases hx' : x' ∈ J
    · have hxx : x * x' ∈ J := J.mul_mem hx hx'
      have : (⟨x * x', hxx⟩ : J) = ⟨x, hx⟩ * ⟨x', hx'⟩ := rfl
      simp only [ψ, dif_pos hx, dif_pos hx', dif_pos hxx, this, map_mul]; rfl
    · have hxx : x * x' ∉ J := fun h => hx' (by
        have := J.mul_mem (J.inv_mem hx) h; simpa using this)
      have h2 : y⁻¹ * x * y ∈ J := by
        have := (Subgroup.normal_of_index_eq_two hJ).conj_mem _ hx y⁻¹
        simpa using this
      have h3 : (⟨y⁻¹ * (x * x'), hmem _ hxx⟩ : J) = ⟨y⁻¹ * x * y, h2⟩ * ⟨y⁻¹ * x', hmem _ hx'⟩ :=
        Subtype.ext (by simp [mul_assoc])
      simp only [ψ, dif_pos hx, dif_neg hx', dif_neg hxx, h3, map_mul, Subgroup.coe_mul]
      have := hc x hx h2
      rw [← mul_assoc, this, mul_assoc]
    · have hxx : x * x' ∉ J := fun h => hx (by
        have := J.mul_mem h (J.inv_mem hx'); simpa using this)
      have h3 : (⟨y⁻¹ * (x * x'), hmem _ hxx⟩ : J) = ⟨y⁻¹ * x, hmem _ hx⟩ * ⟨x', hx'⟩ :=
        Subtype.ext (by simp [mul_assoc])
      simp only [ψ, dif_neg hx, dif_pos hx', dif_neg hxx, h3, map_mul]
      simp [mul_assoc]
    · have hxx : x * x' ∈ J := by
        rw [Subgroup.mul_mem_iff_of_index_two hJ]; exact iff_of_false hx hx'
      have h3 : (⟨x * x', hxx⟩ : J) =
          ⟨y * (y⁻¹ * x) * y⁻¹, (Subgroup.normal_of_index_eq_two hJ).conj_mem _ (hmem _ hx) y⟩ *
          ⟨y ^ 2, Subgroup.sq_mem_of_index_two hJ y⟩ * ⟨y⁻¹ * x', hmem _ hx'⟩ :=
        Subtype.ext (by simp [mul_assoc, pow_two])
      simp only [ψ, dif_neg hx, dif_neg hx', dif_pos hxx, h3, map_mul]
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      have h := hconj ⟨y⁻¹ * x, hmem _ hx⟩
      dsimp only at h
      rw [h, hsq]
      simp only [pow_two, mul_assoc, inv_mul_cancel_left]
  let φ : X →* Y := MonoidHom.mk' ψ hmul
  have hker : ∀ x, φ x = 1 → x = 1 := by
    intro x hx
    change ψ x = 1 at hx
    by_cases h : x ∈ J
    · simp only [ψ, dif_pos h] at hx
      have : ι ⟨x, h⟩ = 1 := Subtype.ext hx
      have := ι.injective (this.trans (map_one ι).symm)
      simpa using congrArg Subtype.val this
    · simp only [ψ, dif_neg h] at hx
      apply absurd _ hY₀
      have : Y₀ = ((ι ⟨y⁻¹ * x, hmem x h⟩ : J')⁻¹ : J') := by
        apply eq_inv_of_mul_eq_one_left hx |>.trans ?_
        rfl
      rw [this]; exact J'.inv_mem (ι _).2
  have hinj : Function.Injective φ := (injective_iff_map_eq_one φ).2 hker
  have hcardX : Nat.card X = 2 * Nat.card J := by
    rw [← hJ, mul_comm, Subgroup.card_mul_index]
  have hcardY : Nat.card Y = 2 * Nat.card J' := by
    rw [← hJ', mul_comm, Subgroup.card_mul_index]
  have hcJ : Nat.card J = Nat.card J' := Nat.card_congr ι.toEquiv
  have hbij : Function.Bijective φ :=
    (Nat.bijective_iff_injective_and_card φ).2 ⟨hinj, by rw [hcardX, hcardY, hcJ]⟩
  exact ⟨MulEquiv.ofBijective φ hbij⟩

end CFSGOutside.GiuliettiKorchmaros.Order48
