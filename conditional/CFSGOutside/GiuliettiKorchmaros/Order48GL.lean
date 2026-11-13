import Mathlib
import CFSGOutside.GiuliettiKorchmaros.Order48Gen

/-!
# Recognition of `GL(2,3)`
-/

open scoped MatrixGroups

namespace CFSGOutside.GiuliettiKorchmaros.Order48

/-- The generator `[[1,1],[0,1]]` of `SL(2,3)`. -/
def s3 : SL(2, ZMod 3) := ⟨!![1, 1; 0, 1], by decide⟩
/-- The generator `[[1,0],[1,1]]` of `SL(2,3)`. -/
def t3 : SL(2, ZMod 3) := ⟨!![1, 0; 1, 1], by decide⟩

instance (a b : SL(2, ZMod 3)) : Decidable (PRel a b) := by unfold PRel; infer_instance

def wordsSL3 : List (List Bool) :=
  [[],
   [true],
   [false],
   [true, true],
   [true, false],
   [false, true],
   [false, false],
   [true, true, false],
   [true, false, true],
   [true, false, false],
   [false, true, true],
   [false, true, false],
   [false, false, true],
   [true, true, false, true],
   [true, true, false, false],
   [true, false, true, true],
   [true, false, true, false],
   [true, false, false, true],
   [false, true, true, false],
   [false, true, false, false],
   [false, false, true, true],
   [false, false, true, false],
   [true, true, false, true, false],
   [true, false, true, false, false]]

theorem hgen3 : Subgroup.closure ({s3, t3} : Set SL(2, ZMod 3)) = ⊤ :=
  closure_eq_top_of_words s3 t3 wordsSL3 (by unfold evalW wordsSL3; decide +kernel)

theorem hP3 : PRel s3 t3 := by decide

theorem pairsGL : ∀ a b : SL(2, ZMod 3), PRel a b → ∃ X : GL (Fin 2) (ZMod 3),
    Matrix.SpecialLinearGroup.toGL a = X * Matrix.SpecialLinearGroup.toGL s3 * X⁻¹ ∧
    Matrix.SpecialLinearGroup.toGL b = X * Matrix.SpecialLinearGroup.toGL t3 * X⁻¹ := by
  unfold PRel
  decide +kernel

theorem autGL : ∀ β : SL(2, ZMod 3) ≃* SL(2, ZMod 3), ∃ Y₀ : GL (Fin 2) (ZMod 3),
    ∀ a, Matrix.SpecialLinearGroup.toGL (β a) = Y₀ * Matrix.SpecialLinearGroup.toGL a * Y₀⁻¹ :=
  hAut_of_pairs Matrix.SpecialLinearGroup.toGL s3 t3 hgen3 hP3 pairsGL

theorem centGL : ∀ c : GL (Fin 2) (ZMod 3),
    c * Matrix.SpecialLinearGroup.toGL s3 = Matrix.SpecialLinearGroup.toGL s3 * c →
    c * Matrix.SpecialLinearGroup.toGL t3 = Matrix.SpecialLinearGroup.toGL t3 * c →
    c = 1 ∨ c = -1 := by
  decide +kernel

theorem sqGL : ∀ Y₀ : GL (Fin 2) (ZMod 3),
    (¬ ∃ a : SL(2, ZMod 3), Matrix.SpecialLinearGroup.toGL a = Y₀) → Y₀ ^ 2 ≠ -1 := by
  decide +kernel

theorem injGL : Function.Injective
    (Matrix.SpecialLinearGroup.toGL : SL(2, ZMod 3) →* GL (Fin 2) (ZMod 3)) := by
  intro a b
  revert a b
  decide +kernel

theorem card_SL3 : Nat.card SL(2, ZMod 3) = 24 := by
  rw [Nat.card_eq_fintype_card]; decide +kernel

theorem card_GL3 : Nat.card (GL (Fin 2) (ZMod 3)) = 48 := by
  rw [Nat.card_eq_fintype_card]; decide +kernel

/-- (2) `GL(2,3)` recognition. -/
theorem nonempty_mulEquiv_GL23 {G : Type*} [Group G] [Finite G] (hcard : Nat.card G = 48)
    (M : Subgroup G) (hMn : M.Normal) (eM : M ≃* SL(2, ZMod 3))
    (hC : Subgroup.centralizer (M : Set G) ≤ M)
    (g : G) (hg : g ∉ M) (hg2 : g ^ 2 = 1) :
    Nonempty (G ≃* GL (Fin 2) (ZMod 3)) := by
  have hM : M.index = 2 := by
    have h1 := M.index_mul_card
    have h2 : Nat.card M = 24 := by rw [Nat.card_congr eM.toEquiv, card_SL3]
    rw [h2, hcard] at h1
    omega
  have hfi : (Matrix.SpecialLinearGroup.toGL :
      SL(2, ZMod 3) →* GL (Fin 2) (ZMod 3)).range.index = 2 := by
    have h1 := (Matrix.SpecialLinearGroup.toGL :
      SL(2, ZMod 3) →* GL (Fin 2) (ZMod 3)).range.index_mul_card
    have h2 : Nat.card (Matrix.SpecialLinearGroup.toGL :
      SL(2, ZMod 3) →* GL (Fin 2) (ZMod 3)).range = 24 := by
      rw [← Nat.card_congr (MonoidHom.ofInjective injGL).toEquiv, card_SL3]
    rw [h2, card_GL3] at h1
    omega
  obtain ⟨Y₀, hout, hconj, c, hc, hcomm, hsq, -⟩ :=
    core M hM eM hC Matrix.SpecialLinearGroup.toGL injGL autGL (-1)
      (fun c hc => centGL c (hc s3) (hc t3)) g hg
  have hout' : ¬ ∃ a : SL(2, ZMod 3), Matrix.SpecialLinearGroup.toGL a = Y₀ := by
    rintro ⟨a, ha⟩; exact hout ⟨a, ha⟩
  have h1 : (⟨g ^ 2, Subgroup.sq_mem_of_index_two hM g⟩ : M) = 1 := Subtype.ext hg2
  have hsq' := hsq
  rw [h1, map_one, map_one] at hsq
  rcases hc with rfl | rfl
  · rw [mul_one] at hsq hsq'
    exact apply_ext M hM eM _ injGL hfi g hg Y₀ hout hconj hsq'
  · exfalso
    apply sqGL Y₀ hout'
    have : Y₀ ^ 2 * -1 = 1 := hsq.symm
    calc Y₀ ^ 2 = Y₀ ^ 2 * -1 * -1 := by simp
      _ = -1 := by rw [this]; simp

end CFSGOutside.GiuliettiKorchmaros.Order48
