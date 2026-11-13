import CFSGOutside.ChillagSonn.Overgroups
import CFSGOutside.ChillagSonn.Covers

/-!
# Fact 5 of Chillag–Sonn, part A: semilinear automorphisms of `SL(2, F)`

For `g ∈ GL(2, F)` and a field automorphism `τ`, `semiConj g τ : x ↦ g τ(x) g⁻¹` is an automorphism of `SL(2, F)`
inducing on `PGL(2, F)` the action of `(ḡ, τ) ∈ PΓL(2, F)`. Two homomorphisms from a perfect group into `SL(2, F)`
that agree modulo the centre are equal, and an element of `GL(2, F)` centralizing `SL(2, F)` is scalar.
-/

noncomputable section

namespace CFSGOutside.ChillagSonn

open CFSGOutside.Corpus CFSGOutside.Corpus.GorensteinWalter Matrix SemidirectProduct
open scoped MatrixGroups

variable {F : Type} [Field F]

/-- `x ↦ g τ(x) g⁻¹` on `SL(2, F)`. -/
def semiConj (g : GL (Fin 2) F) (τ : F ≃+* F) : SL(2, F) →* SL(2, F) where
  toFun x := ⟨(g : Matrix (Fin 2) (Fin 2) F) * (τ : F →+* F).mapMatrix (x : Matrix (Fin 2) (Fin 2) F) *
      ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F), by
    rw [det_mul, det_mul, ← RingHom.map_det, x.prop, map_one, mul_one, ← det_mul, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, det_one]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by
    have hinv : ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    change _ * (τ : F →+* F).mapMatrix ((x : Matrix (Fin 2) (Fin 2) F) * (y : Matrix (Fin 2) (Fin 2) F)) * _ =
      (_ * _ * _) * (_ * _ * _)
    simp only [map_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc _ (g : Matrix (Fin 2) (Fin 2) F), hinv, Matrix.one_mul])

/-- `semiConj` on `GL(2, F)`. -/
theorem toGL_semiConj (g : GL (Fin 2) F) (τ : F ≃+* F) (x : SL(2, F)) :
    SpecialLinearGroup.toGL (semiConj g τ x) = g * GeneralLinearGroup.map (τ : F →+* F)
      (SpecialLinearGroup.toGL x) * g⁻¹ := by
  ext1; rfl

/-- `semiConj g τ` induces `(ḡ, τ)` on `PGL(2, F)`. -/
theorem toPGL_semiConj (g : GL (Fin 2) F) (τ : F ≃+* F) (x : SL(2, F)) :
    SpecialLinearGroup.toPGL (semiConj g τ x) = ProjGenLinGroup.mk g *
      pgl2FieldAut F τ (SpecialLinearGroup.toPGL x) * (ProjGenLinGroup.mk g)⁻¹ := by
  change ProjGenLinGroup.mk (SpecialLinearGroup.toGL (semiConj g τ x)) = _
  rw [toGL_semiConj, map_mul, map_mul, map_inv]
  rfl

/-- `semiConj g τ` is injective. -/
theorem semiConj_injective (g : GL (Fin 2) F) (τ : F ≃+* F) : Function.Injective (semiConj g τ) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h := congrArg SpecialLinearGroup.toGL hx
  rw [toGL_semiConj, map_one, mul_inv_eq_one, mul_eq_left] at h
  ext i j
  have := congrArg (fun A : GL (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F) i j) h
  simpa [one_apply, apply_ite] using this

/-- `semiConj g τ` is surjective. -/
theorem semiConj_surjective [Finite F] (g : GL (Fin 2) F) (τ : F ≃+* F) :
    Function.Surjective (semiConj g τ) :=
  Finite.surjective_of_injective (semiConj_injective g τ)

/-- Conjugation of `PGL(2, F)` inside `PΓL(2, F)`. -/
theorem conj_inl (x : PGammaL2 F) (z : PGL2 F) :
    x * inl z * x⁻¹ = inl (x.left * pgl2FieldAut F x.right z * x.left⁻¹) := by
  ext
  · simp only [mul_left, left_inl, inv_left, right_inl, mul_right, mul_one]
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  · simp

/-- Homomorphisms from a perfect group to `SL(2, F)` agreeing in `PGL(2, F)` are equal. -/
theorem eq_of_toPGL_eq {H : Type} [Group H] (hH : commutator H = ⊤) (f₁ f₂ : H →* SL(2, F))
    (h : ∀ a, SpecialLinearGroup.toPGL (f₁ a) = SpecialLinearGroup.toPGL (f₂ a)) : f₁ = f₂ := by
  have hc : ∀ a, f₁ a * (f₂ a)⁻¹ ∈ Subgroup.center SL(2, F) := fun a => by
    rw [← SpecialLinearGroup.toPGL_ker, MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
  let f : H →* SL(2, F) :=
    { toFun a := f₁ a * (f₂ a)⁻¹
      map_one' := by simp
      map_mul' a b := by
        have e := Subgroup.mem_center_iff.mp (hc b) (f₂ a)⁻¹
        simp only [map_mul, _root_.mul_inv_rev]
        calc f₁ a * f₁ b * ((f₂ b)⁻¹ * (f₂ a)⁻¹) = f₁ a * ((f₁ b * (f₂ b)⁻¹) * (f₂ a)⁻¹) := by
              group
          _ = f₁ a * (f₂ a)⁻¹ * (f₁ b * (f₂ b)⁻¹) := by rw [← e]; group }
  have hker : commutator H ≤ f.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_center_iff.mp (hc b) (f a)
  ext a : 1
  have ha : f a = 1 := (hH ▸ hker) (Subgroup.mem_top a)
  exact mul_inv_eq_one.mp ha

/-- An element of `GL(2, F)` commuting with `SL(2, F)` is scalar. -/
theorem exists_scalar_of_comm [Finite F] (M : GL (Fin 2) F)
    (h : ∀ x : SL(2, F), M * SpecialLinearGroup.toGL x = SpecialLinearGroup.toGL x * M) :
    ∃ u : Fˣ, M = GeneralLinearGroup.scalar (Fin 2) u := by
  have h1 := LinearTwo.mk_eq_one_of_commute F M (SpecialLinearGroup.toGL (LinearTwo.E12 F))
    (SpecialLinearGroup.toGL (LinearTwo.E21 F)) rfl rfl (by rw [← map_mul, h, map_mul])
    (by rw [← map_mul, h, map_mul])
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at h1
  obtain ⟨u, hu⟩ := h1
  exact ⟨u, hu.symm⟩

end CFSGOutside.ChillagSonn
