import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Pi.Lemmas

/-!
# Packed matrices over `𝔽₂`

Vectors in `𝔽₂ⁿ` are encoded as natural numbers (bit `j` is coordinate `j`) and `n × n` matrices
as lists of their rows. Matrix–vector and matrix–matrix products are computed with bit operations,
which the kernel evaluates quickly, and are proved to agree with `Matrix.mulVec` and `Matrix.mul`.
-/

namespace CFSGOutside.HallPaige.F2

/-- `b2z b` is `1 : ZMod 2` if `b` holds and `0` otherwise. -/
def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

theorem b2z_xor (a b : Bool) : b2z (a ^^ b) = b2z a + b2z b := by
  cases a <;> cases b <;> decide

theorem b2z_and (a b : Bool) : b2z (a && b) = b2z a * b2z b := by
  cases a <;> cases b <;> decide

/-- `xf g n = g 0 ^^ ⋯ ^^ g (n - 1)`. -/
def xf (g : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | k + 1 => xf g k ^^ g k

theorem sum_b2z (g : ℕ → Bool) (n : ℕ) : ∑ j : Fin n, b2z (g j) = b2z (xf g n) := by
  induction n with
  | zero => simp [xf, b2z]
  | succ k ih =>
    rw [Fin.sum_univ_castSucc, xf, b2z_xor, ← ih]
    simp

/-- The vector of `𝔽₂ⁿ` encoded by the bits of `x`. -/
def vecOf (n x : ℕ) : Fin n → ZMod 2 := fun j => b2z (x.testBit j)

/-- The matrix whose `i`-th row is encoded by `R.getD i 0`. -/
def matOf (n : ℕ) (R : List ℕ) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  Matrix.of fun i j => b2z ((R.getD i 0).testBit j)

/-- `pack f n` has bit `i` equal to `f i` for `i < n` and no other bits. -/
def pack (f : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | k + 1 => pack f k ||| (if f k then 2 ^ k else 0)

theorem testBit_pack (f : ℕ → Bool) (n i : ℕ) :
    (pack f n).testBit i = (decide (i < n) && f i) := by
  induction n with
  | zero => simp [pack]
  | succ k ih =>
    rw [pack, Nat.testBit_or, ih]
    by_cases hk : f k
    · simp only [hk, ↓reduceIte]
      rw [Nat.testBit_two_pow]
      by_cases hi : i = k
      · subst hi; simp [hk]
      · have : k ≠ i := fun h => hi h.symm
        simp only [this, decide_false, Bool.or_false]
        congr 1
        simp only [decide_eq_decide]
        omega
    · simp only [hk, Bool.false_eq_true, ↓reduceIte]
      rw [Nat.zero_testBit, Bool.or_false]
      by_cases hi : i = k
      · subst hi; simp [hk]
      · congr 1
        simp only [decide_eq_decide]
        omega

/-- Packed matrix–vector product. -/
def mv (n : ℕ) (R : List ℕ) (x : ℕ) : ℕ :=
  pack (fun i => xf (fun j => ((R.getD i 0) &&& x).testBit j) n) n

theorem mulVec_matOf (n : ℕ) (R : List ℕ) (x : ℕ) :
    (matOf n R).mulVec (vecOf n x) = vecOf n (mv n R x) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, matOf, Matrix.of_apply, vecOf, mv]
  rw [testBit_pack, decide_eq_true i.isLt, Bool.true_and, ← sum_b2z]
  simp only [← b2z_and, Nat.testBit_and]

/-- `xr n r S` is the xor of the rows `S.getD j 0` over the bits `j < n` of `r`. -/
def xr (n r : ℕ) (S : List ℕ) : ℕ :=
  match n with
  | 0 => 0
  | k + 1 => xr k r S ^^^ (if r.testBit k then S.getD k 0 else 0)

theorem testBit_xr (n r : ℕ) (S : List ℕ) (k : ℕ) :
    (xr n r S).testBit k = xf (fun j => r.testBit j && (S.getD j 0).testBit k) n := by
  induction n with
  | zero => simp [xr, xf]
  | succ m ih =>
    rw [xr, Nat.testBit_xor, ih, xf]
    congr 1
    split_ifs with h <;> simp [h]

/-- Packed matrix product. -/
def mm (n : ℕ) (R S : List ℕ) : List ℕ := (List.range n).map fun i => xr n (R.getD i 0) S

theorem getD_mm {n : ℕ} (R S : List ℕ) {i : ℕ} (hi : i < n) :
    (mm n R S).getD i 0 = xr n (R.getD i 0) S := by
  simp [mm, List.getD_eq_getElem?_getD, List.getElem?_range hi]

theorem matOf_mm (n : ℕ) (R S : List ℕ) : matOf n (mm n R S) = matOf n R * matOf n S := by
  ext i k
  simp only [matOf, Matrix.of_apply, Matrix.mul_apply]
  rw [getD_mm R S i.isLt, testBit_xr, ← sum_b2z]
  simp only [b2z_and]

/-- The packed identity matrix. -/
def idm (n : ℕ) : List ℕ := (List.range n).map (2 ^ ·)

theorem matOf_idm (n : ℕ) : matOf n (idm n) = 1 := by
  ext i j
  simp only [matOf, Matrix.of_apply, idm]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range i.isLt]
  simp only [Option.map_some, Option.getD_some]
  rw [Nat.testBit_two_pow, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp [b2z]
  · have : (i : ℕ) ≠ j := fun e => h (Fin.ext e)
    simp [b2z, h, this]

/-- Packed matrix power. -/
def mpow (n : ℕ) (R : List ℕ) : ℕ → List ℕ
  | 0 => idm n
  | k + 1 => mm n (mpow n R k) R

theorem matOf_mpow (n : ℕ) (R : List ℕ) (k : ℕ) : matOf n (mpow n R k) = matOf n R ^ k := by
  induction k with
  | zero => rw [mpow, matOf_idm, pow_zero]
  | succ k ih => rw [mpow, matOf_mm, ih, pow_succ]

theorem vecOf_add (n x y : ℕ) : vecOf n x + vecOf n y = vecOf n (x ^^^ y) := by
  funext j
  simp [vecOf, Nat.testBit_xor, b2z_xor]

theorem vecOf_two_pow (n : ℕ) (i : Fin n) : vecOf n (2 ^ (i : ℕ)) = Pi.single i 1 := by
  funext j
  simp only [vecOf, Nat.testBit_two_pow, Pi.single_apply]
  by_cases h : j = i
  · subst h; simp [b2z]
  · have : (i : ℕ) ≠ j := fun e => h (Fin.ext e).symm
    simp [b2z, h, this]

theorem vecOf_zero (n : ℕ) : vecOf n 0 = 0 := by
  funext j
  simp [vecOf, b2z]

theorem vecOf_injective {n x y : ℕ} (hx : x < 2 ^ n) (hy : y < 2 ^ n)
    (h : vecOf n x = vecOf n y) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · have := congrFun h ⟨i, hi⟩
    simp only [vecOf, b2z] at this
    cases hx' : x.testBit i <;> cases hy' : y.testBit i <;> simp only [hx', hy'] at this ⊢ <;>
      exact absurd this (by decide)
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hy (Nat.pow_le_pow_right (by norm_num) (by omega)))]

end CFSGOutside.HallPaige.F2
