import CFSGOutside.Corpus.HallPaige.B.Defs

/-!
# Conjugation invariance of the corpus involution classes of `B`

`BabyInv k` and `BabyOrbit k` (copied from `CFSG/Monster/GMS/Facts/BabyTables.lean`) are invariant under
conjugation; `BabyOrbit k r s` depends only on the conjugacy class of `r * s`, and the four orbit types
are mutually exclusive. Pure group theory, no corpus theorem.
-/

namespace CFSGOutside.HallPaige.B

open CFSGOutside.Corpus.B.Blueprint CFSGOutside.Corpus.B.Monster.GMS

local notation "𝔹" => NativeSporadic.B

section Group

variable {G : Type*} [Group G]

theorem orderOf_conj' (g x : G) : orderOf (g * x * g⁻¹) = orderOf x := by
  have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
  simpa [MulAut.conj_apply] using this

theorem card_centralizer_conj (g x : G) :
    Nat.card (Subgroup.centralizer ({g * x * g⁻¹} : Set G)) =
      Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  refine (Nat.card_congr ((MulAut.conj g).toEquiv.subtypeEquiv fun c => ?_)).symm
  simp only [Subgroup.mem_centralizer_singleton_iff, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv,
    MulAut.conj_apply]
  rw [show g * x * g⁻¹ * (g * c * g⁻¹) = g * (x * c) * g⁻¹ by group,
    show g * c * g⁻¹ * (g * x * g⁻¹) = g * (c * x) * g⁻¹ by group]
  constructor
  · intro h
    rw [h]
  · intro h
    exact mul_left_cancel (mul_right_cancel h)

end Group

theorem babyInv_conj_iff {k : Fin 4} (g x : 𝔹) : BabyInv k (g * x * g⁻¹) ↔ BabyInv k x := by
  unfold BabyInv
  rw [orderOf_conj', card_centralizer_conj]

/-- `BabyOrbit k r s` depends only on the conjugacy class of `r * s`. -/
theorem babyOrbit_iff_of_mul {k : Fin 4} {r s r' s' g : 𝔹} (h : r * s = g * (r' * s') * g⁻¹) :
    BabyOrbit k r s ↔ BabyOrbit k r' s' := by
  match k with
  | 0 =>
    show BabyInv 1 (r * s) ↔ BabyInv 1 (r' * s')
    rw [h, babyInv_conj_iff]
  | 1 =>
    show BabyInv 3 (r * s) ↔ BabyInv 3 (r' * s')
    rw [h, babyInv_conj_iff]
  | 2 =>
    show orderOf (r * s) = 3 ↔ orderOf (r' * s') = 3
    rw [h, orderOf_conj']
  | 3 =>
    show (orderOf (r * s) = 4 ∧ BabyInv 1 ((r * s) ^ 2)) ↔
      (orderOf (r' * s') = 4 ∧ BabyInv 1 ((r' * s') ^ 2))
    rw [h, orderOf_conj', conj_pow, babyInv_conj_iff]

theorem babyOrbit_conj_iff {k : Fin 4} (g r s : 𝔹) :
    BabyOrbit k (g * r * g⁻¹) (g * s * g⁻¹) ↔ BabyOrbit k r s :=
  babyOrbit_iff_of_mul (g := g) (by group)

theorem babyOrbit_comm {k : Fin 4} (r s : 𝔹) : BabyOrbit k s r ↔ BabyOrbit k r s :=
  babyOrbit_iff_of_mul (g := r⁻¹) (by group)

theorem orderOf_of_babyOrbit {k : Fin 4} {r s : 𝔹} (h : BabyOrbit k r s) :
    orderOf (r * s) = ![2, 2, 3, 4] k := by
  match k, h with
  | 0, h => exact h.1
  | 1, h => exact h.1
  | 2, h => exact h
  | 3, h => exact h.1

/-- The four orbit types are mutually exclusive. -/
theorem babyOrbit_unique {k k' : Fin 4} {r s : 𝔹} (h : BabyOrbit k r s) (h' : BabyOrbit k' r s) :
    k = k' := by
  have o := (orderOf_of_babyOrbit h).symm.trans (orderOf_of_babyOrbit h')
  match k, k', h, h' with
  | 0, 0, _, _ => rfl
  | 1, 1, _, _ => rfl
  | 2, 2, _, _ => rfl
  | 3, 3, _, _ => rfl
  | 0, 1, h, h' =>
    have e : babyCentOrder 1 = babyCentOrder 3 := (h : BabyInv 1 (r * s)).2.symm.trans h'.2
    norm_num [babyCentOrder] at e
  | 1, 0, h, h' =>
    have e : babyCentOrder 3 = babyCentOrder 1 := (h : BabyInv 3 (r * s)).2.symm.trans h'.2
    norm_num [babyCentOrder] at e
  | 0, 2, _, _ => simp at o
  | 0, 3, _, _ => simp at o
  | 1, 2, _, _ => simp at o
  | 1, 3, _, _ => simp at o
  | 2, 0, _, _ => simp at o
  | 2, 1, _, _ => simp at o
  | 2, 3, _, _ => simp at o
  | 3, 0, _, _ => simp at o
  | 3, 1, _, _ => simp at o
  | 3, 2, _, _ => simp at o

theorem not_babyOrbit_self {k : Fin 4} {r : 𝔹} (hr : r * r = 1) : ¬ BabyOrbit k r r := by
  intro h
  have o := orderOf_of_babyOrbit h
  rw [hr, orderOf_one] at o
  match k with
  | 0 => simp at o
  | 1 => simp at o
  | 2 => simp at o
  | 3 => simp at o

end CFSGOutside.HallPaige.B
