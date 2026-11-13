import Mathlib

open scoped MatrixGroups

namespace CFSGOutside.Psl2Basic

lemma map_center_equiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    (Subgroup.center G).map e.toMonoidHom = Subgroup.center H := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_center_iff, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨y, hy, rfl⟩ z
    have h := congrArg e (hy (e.symm z))
    simpa using h
  · intro hx
    refine ⟨e.symm x, fun z => ?_, by simp⟩
    apply e.injective
    simpa using hx (e z)

def slEquiv {K L : Type*} [Field K] [Field L] (e : K ≃+* L) :
    Matrix.SpecialLinearGroup (Fin 2) K ≃* Matrix.SpecialLinearGroup (Fin 2) L where
  toFun := Matrix.SpecialLinearGroup.map (e : K →+* L)
  invFun := Matrix.SpecialLinearGroup.map (e.symm : L →+* K)
  left_inv x := by ext i j; simp
  right_inv x := by ext i j; simp
  map_mul' := map_mul _

def pslEquiv {K L : Type*} [Field K] [Field L] (e : K ≃+* L) :
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) L :=
  QuotientGroup.congr _ _ (slEquiv e) (map_center_equiv _)

lemma card_psl2_congr {K L : Type*} [Field K] [Field L] (e : K ≃+* L) :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) =
      Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) L) :=
  Nat.card_congr (pslEquiv e).toEquiv

instance finite_sl2 (K : Type*) [Field K] [Finite K] : Finite (Matrix.SpecialLinearGroup (Fin 2) K) :=
  Finite.of_injective (fun g : Matrix.SpecialLinearGroup (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K))
    Subtype.val_injective

lemma eq_top_of_equiv_psl2 {K L : Type*} [Field K] [Finite K] [Field L] (e : K ≃+* L)
    (H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K))
    (φ : H ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) L) : H = ⊤ := by
  have : Finite H := inferInstance
  rw [← Subgroup.card_eq_iff_eq_top, Nat.card_congr φ.toEquiv, card_psl2_congr e.symm]

lemma card_gl2_dvd_aux (K : Type*) [Field K] [Fintype K] :
    Nat.card (GL (Fin 2) K) = (Fintype.card K ^ 2 - 1) * (Fintype.card K ^ 2 - Fintype.card K) := by
  rw [Matrix.card_GL_field]
  simp [Fin.prod_univ_two]

lemma card_psl2_dvd (K : Type*) [Field K] [Fintype K] :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) ∣
      (Fintype.card K ^ 2 - 1) * (Fintype.card K ^ 2 - Fintype.card K) := by
  rw [← card_gl2_dvd_aux]
  refine (Subgroup.card_quotient_dvd_card _).trans ?_
  exact Subgroup.card_dvd_of_injective (Matrix.SpecialLinearGroup.toGL) (by
    intro a b h
    ext i j
    have := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) i j) h
    simpa using this)

lemma card_pgl2_dvd (K : Type*) [Field K] [Fintype K] :
    Nat.card (Matrix.ProjGenLinGroup (Fin 2) K) ∣
      (Fintype.card K ^ 2 - 1) * (Fintype.card K ^ 2 - Fintype.card K) := by
  rw [← card_gl2_dvd_aux]
  exact Subgroup.card_quotient_dvd_card _

lemma card_psl2_dvd' (K : Type*) [Field K] [Finite K] :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) ∣
      (Nat.card K ^ 2 - 1) * (Nat.card K ^ 2 - Nat.card K) := by
  have := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card (α := K)]
  exact card_psl2_dvd K

lemma card_pgl2_dvd' (K : Type*) [Field K] [Finite K] :
    Nat.card (Matrix.ProjGenLinGroup (Fin 2) K) ∣
      (Nat.card K ^ 2 - 1) * (Nat.card K ^ 2 - Nat.card K) := by
  have := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card (α := K)]
  exact card_pgl2_dvd K

end CFSGOutside.Psl2Basic
