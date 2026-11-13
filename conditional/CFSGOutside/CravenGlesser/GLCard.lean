import Mathlib

/-!
# Orders of invertible linear maps of small `𝔽₂`-spaces

On an `𝔽₂`-space of dimension `k ≤ 3`, the order of an invertible linear map divides `|GL_k(2)|`, which
divides 168; on a space of dimension at most 1 it is 1.
-/

namespace CFSGOutside.CravenGlesser

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

theorem card_units_end :
    Nat.card (Module.End (ZMod 2) W)ˣ =
      ∏ i : Fin (Module.finrank (ZMod 2) W),
        (2 ^ Module.finrank (ZMod 2) W - 2 ^ (i : ℕ)) := by
  set k := Module.finrank (ZMod 2) W
  let e : W ≃ₗ[ZMod 2] (Fin k → ZMod 2) := (Module.finBasisOfFinrankEq (ZMod 2) W rfl).equivFun
  let conj : (W ≃ₗ[ZMod 2] W) ≃ ((Fin k → ZMod 2) ≃ₗ[ZMod 2] (Fin k → ZMod 2)) :=
    { toFun := fun f => e.symm.trans (f.trans e)
      invFun := fun g => e.trans (g.trans e.symm)
      left_inv := fun f => by ext x; simp
      right_inv := fun g => by ext x; simp }
  have h1 : Nat.card (Module.End (ZMod 2) W)ˣ = Nat.card (W ≃ₗ[ZMod 2] W) :=
    Nat.card_congr (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).toEquiv
  have h2 : Nat.card ((Fin k → ZMod 2) ≃ₗ[ZMod 2] (Fin k → ZMod 2)) =
      Nat.card (GL (Fin k) (ZMod 2)) :=
    Nat.card_congr ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin k → ZMod 2)).symm.trans
      Matrix.GeneralLinearGroup.toLin.symm).toEquiv
  rw [h1, Nat.card_congr conj, h2, Matrix.card_GL_field, ZMod.card]

theorem orderOf_dvd_of_finrank_le_three (f : Module.End (ZMod 2) W) (hf : IsUnit f)
    (hk : Module.finrank (ZMod 2) W ≤ 3) : orderOf f ∣ 168 := by
  obtain ⟨u, rfl⟩ := hf
  rw [orderOf_units]
  have hdvd := orderOf_dvd_natCard u
  rw [card_units_end] at hdvd
  refine hdvd.trans ?_
  interval_cases h : Module.finrank (ZMod 2) W <;> simp [Fin.prod_univ_succ] <;> norm_num

theorem orderOf_eq_one_of_finrank_le_one (f : Module.End (ZMod 2) W) (hf : IsUnit f)
    (hk : Module.finrank (ZMod 2) W ≤ 1) : orderOf f = 1 := by
  obtain ⟨u, rfl⟩ := hf
  rw [orderOf_units]
  have hdvd := orderOf_dvd_natCard u
  rw [card_units_end] at hdvd
  apply Nat.dvd_one.mp
  refine hdvd.trans ?_
  interval_cases h : Module.finrank (ZMod 2) W <;> simp [Fin.prod_univ_succ]

end CFSGOutside.CravenGlesser
