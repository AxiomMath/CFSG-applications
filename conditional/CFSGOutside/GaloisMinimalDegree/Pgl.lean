import CFSGOutside.GaloisMinimalDegree.Basic

open scoped MatrixGroups

namespace CFSGOutside.GaloisMinimalDegree

open CFSGOutside.Psl2Basic

lemma card_pgl2_le (K : Type) [Field K] [Finite K] :
    Nat.card (Matrix.ProjGenLinGroup (Fin 2) K) ≤
      Nat.card K * (Nat.card K * Nat.card K - 1) := by
  have := Fintype.ofFinite K
  have hmul : Nat.card (GL (Fin 2) K) = Nat.card (Matrix.ProjGenLinGroup (Fin 2) K) *
      Nat.card (Subgroup.center (GL (Fin 2) K)) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hGL := card_gl2_dvd_aux K
  have hinj : Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin 2) : Kˣ →* GL (Fin 2) K) := by
    intro a b h
    have := congrArg (fun g : GL (Fin 2) K => ((g : Matrix (Fin 2) (Fin 2) K) 0 0)) h
    apply Units.ext
    simpa [Matrix.GeneralLinearGroup.scalar] using this
  have hZ : Nat.card Kˣ ≤ Nat.card (Subgroup.center (GL (Fin 2) K)) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact Nat.card_le_card_of_injective _ (MonoidHom.rangeRestrict_injective_iff.2 hinj)
  rw [Nat.card_units] at hZ
  rw [Nat.card_eq_fintype_card (α := K)] at hZ ⊢
  rw [hGL] at hmul
  have hq : 2 ≤ Fintype.card K := by
    have : 1 < Nat.card K := Finite.one_lt_card
    rwa [Nat.card_eq_fintype_card] at this
  generalize Fintype.card K = q at *
  have h1 : 1 ≤ q * q := by nlinarith
  have h2 : q ≤ q ^ 2 := by nlinarith
  have h3 : 1 ≤ q ^ 2 := by nlinarith
  have e : (q ^ 2 - 1) * (q ^ 2 - q) = q * (q * q - 1) * (q - 1) := by
    zify [h1, h2, h3, (by omega : 1 ≤ q)]
    ring
  rw [e] at hmul
  have : Nat.card (Matrix.ProjGenLinGroup (Fin 2) K) * (q - 1) ≤ q * (q * q - 1) * (q - 1) := by
    rw [hmul]; exact Nat.mul_le_mul_left _ hZ
  exact Nat.le_of_mul_le_mul_right this (by omega)

end CFSGOutside.GaloisMinimalDegree
