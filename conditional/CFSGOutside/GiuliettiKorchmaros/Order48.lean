import Mathlib
import CFSGOutside.GiuliettiKorchmaros.Order48Ext
import CFSGOutside.GiuliettiKorchmaros.Order48Gen
import CFSGOutside.GiuliettiKorchmaros.Order48GL
import CFSGOutside.GiuliettiKorchmaros.Order48Oct

/-!
# Recognition of `GL(2,3)` and of the binary octahedral group `2O`

Main results (all in namespace `CFSGOutside.GiuliettiKorchmaros.Order48`):
* `nonempty_mulEquiv_of_index_two` (Order48Ext): extension lemma for index-two subgroups;
* `nonempty_mulEquiv_GL23` (Order48GL): recognition of `GL(2,3)`;
* `nonempty_mulEquiv_binaryOctahedral` (below): recognition of `binaryOctahedral`.

The statements are exactly as requested; the generic argument is `core` in `Order48Gen`, and the
finite computations (automorphisms of `SL(2,3)`, centralizers, etc.) are done by `decide +kernel`.
-/

open scoped MatrixGroups

namespace CFSGOutside.GiuliettiKorchmaros.Order48

/-- (3) Binary octahedral recognition. -/
theorem nonempty_mulEquiv_binaryOctahedral {X : Type*} [Group X] [Finite X]
    (hcard : Nat.card X = 48)
    (J : Subgroup X) (hJn : J.Normal) (eJ : J ≃* SL(2, ZMod 3))
    (hC : Subgroup.centralizer (J : Set X) ≤ J)
    (huniq : ∀ x y : X, x ^ 2 = 1 → y ^ 2 = 1 → x ≠ 1 → y ≠ 1 → x = y) :
    Nonempty (X ≃* binaryOctahedral) := by
  have hJ : J.index = 2 := by
    have h1 := J.index_mul_card
    have h2 : Nat.card J = 24 := by rw [Nat.card_congr eJ.toEquiv, card_SL3]
    rw [h2, hcard] at h1
    omega
  have hfi : Fb.range.index = 2 := by
    have h1 := Fb.range.index_mul_card
    have h2 : Nat.card Fb.range = 24 := by
      rw [← Nat.card_congr (MonoidHom.ofInjective Fb_inj).toEquiv, card_SL3]
    rw [h2, card_binOct] at h1
    omega
  -- an element outside `J`
  obtain ⟨y, hy⟩ : ∃ y : X, y ∉ J := by
    by_contra h
    push Not at h
    have : J = ⊤ := eq_top_iff.2 fun x _ => h x
    rw [this, Subgroup.index_top] at hJ
    omega
  let e : binaryOctahedral := Fb m1
  have hAut : ∀ β : SL(2, ZMod 3) ≃* SL(2, ZMod 3), ∃ Y₀ : binaryOctahedral,
      ∀ a, Fb (β a) = Y₀ * Fb a * Y₀⁻¹ := by
    apply hAut_of_pairs Fb s3 t3 hgen3 hP3
    intro a b hab
    obtain ⟨X, hX, h1, h2⟩ := Ffun_pairs a b hab
    refine ⟨⟨X, (mem_bin_iff _).2 hX⟩, Subtype.ext h1, Subtype.ext h2⟩
  have hCY : ∀ c : binaryOctahedral, (∀ a, c * Fb a = Fb a * c) → c = 1 ∨ c = e := by
    intro c hc
    have hs := congrArg Subtype.val (hc s3)
    have ht := congrArg Subtype.val (hc t3)
    rcases Ffun_cent c.1 ((mem_bin_iff _).1 c.2) hs ht with h | h
    · left; exact Subtype.ext h
    · right; exact Subtype.ext h
  obtain ⟨Y₀, hout, hconj, c, hc, hcomm, hsq, hsq2⟩ :=
    core J hJ eJ hC Fb Fb_inj hAut e hCY y hy
  rcases hc with rfl | rfl
  · rw [mul_one] at hsq
    exact apply_ext J hJ eJ Fb Fb_inj hfi y hy Y₀ hout hconj hsq
  · exfalso
    -- there is `w` with `(Y₀ * Fb w)^2 = e`
    have hout' : ¬ ∃ a, Ffun a = Y₀.1 := by
      rintro ⟨a, ha⟩; exact hout ⟨a, Subtype.ext ha⟩
    obtain ⟨w, hw⟩ := Ffun_sq Y₀.1 ((mem_bin_iff _).1 Y₀.2) hout'
    have hw' : (Y₀ * Fb w) ^ 2 = e := Subtype.ext hw
    have he2 : e * e = 1 := by
      have : Fb (m1 ^ 2) = 1 := by rw [m1_facts.1, map_one]
      rw [map_pow, pow_two] at this; exact this
    set j : J := eJ.symm w with hj
    have h1 := hsq2 j
    rw [hj, MulEquiv.apply_symm_apply, hw', he2] at h1
    have h2 : eJ ⟨(y * j) ^ 2, Subgroup.sq_mem_of_index_two hJ _⟩ = 1 := Fb_inj (h1.trans (map_one Fb).symm)
    have h3 : (y * (j : X)) ^ 2 = 1 := by
      have := eJ.injective (h2.trans (map_one eJ).symm)
      exact congrArg Subtype.val this
    have h4 : y * (j : X) ≠ 1 := by
      intro h
      apply hy
      have : y = (j : X)⁻¹ := eq_inv_of_mul_eq_one_left h
      rw [this]; exact J.inv_mem j.2
    -- an involution in `J`
    set j₀ : J := eJ.symm m1 with hj₀
    have h5 : ((j₀ : J) : X) ^ 2 = 1 := by
      have : eJ (j₀ ^ 2) = 1 := by rw [map_pow, hj₀, MulEquiv.apply_symm_apply, m1_facts.1]
      have := eJ.injective (this.trans (map_one eJ).symm)
      simpa using congrArg Subtype.val this
    have h6 : ((j₀ : J) : X) ≠ 1 := by
      intro h
      have : j₀ = 1 := Subtype.ext h
      have := congrArg eJ this
      rw [hj₀, MulEquiv.apply_symm_apply, map_one] at this
      exact m1_facts.2 this
    have h7 := huniq _ _ h3 h5 h4 h6
    apply hy
    have : y = (j₀ : X) * (j : X)⁻¹ := by rw [← h7]; group
    rw [this]; exact J.mul_mem j₀.2 (J.inv_mem j.2)

end CFSGOutside.GiuliettiKorchmaros.Order48
