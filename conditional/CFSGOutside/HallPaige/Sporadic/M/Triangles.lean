import CFSGOutside.HallPaige.Sporadic.M.Visible
import CFSGOutside.HallPaige.Sporadic.M.Assembly
import CFSGOutside.HallPaige.Sporadic.M.Keys1
import CFSGOutside.HallPaige.Sporadic.M.Keys2
import CFSGOutside.HallPaige.Sporadic.M.Keys3

/-!
# The `2B`, `4A` and `4B` triangles of the Monster

All in the Griess–Conway model, with `R`, `S`, `τ` of `Sporadic/M/Visible.lean`:

* `2B`: `R (F,0,191)`, `R (T,0,191)`, `R (F,63,191)`; the products are `xGriess`, `τ xGriess τ⁻¹` and
  `τ² xGriess τ⁻²` (the triality four-group `xB, yB, zB`);
* `4A`: `R (F,0,62)`, `R (F,63,191)`, `R (F,57,4)`, pairwise anticommuting short elements of `Q`:
  each product squares to `xGriess`;
* `4B` (`M_RESEARCH2.md`): `α = R (F,0,62)`, `β = S 1`, `γ = R (F,0,1) · S 6 · R (F,0,1)`. Pushing the
  sign letters to the right (`S_R`) and using `S 1 S 6 S 1 S 6 = τ xGriess τ⁻¹ = R (T,63,0)` (from
  `S a = τ R(xₐ) τ⁻¹`), the three squares are `R` of the short keys `49704`, `178`, `50024`.

Every vertex is conjugate to `tGriess`: an `R` of a short key by `isConj_tGriess_R`, a sign letter
because `S a = τ R(F,a,θ a) τ⁻¹`. The Pauli arithmetic is evaluated by `decide`, the keys in
`Sporadic/M/Keys*.lean`.
-/

namespace CFSGOutside.HallPaige.M

open CFSGOutside.Corpus.M CFSGOutside.Corpus.M.GriessModel CFSGOutside.Corpus.M.Monster.B

variable {d : GriessModel} [d.Facts]

theorem tA_0 : IsConj d.tGriess (R d (false, 0, 191)) :=
  isConj_tGriess_R (isShortCoord_of_key (p := 0) (by norm_num) keyAt_0) (by decide)
theorem tA_0' : IsConj d.tGriess (R d (true, 0, 191)) :=
  isConj_tGriess_R (isShortCoord_of_key (p := 0) (by norm_num) keyAt_0) (by decide)
theorem tA_1 : IsConj d.tGriess (R d (false, 63, 191)) :=
  isConj_tGriess_R (isShortCoord_of_key (p := 1) (by norm_num) keyAt_1) (by decide)
theorem tA_552 : IsConj d.tGriess (R d (false, 0, 62)) :=
  isConj_tGriess_R (isShortCoord_of_key (p := 552) (by norm_num) keyAt_552) (by decide)
theorem tA_628 : IsConj d.tGriess (R d (false, 57, 4)) :=
  isConj_tGriess_R (isShortCoord_of_key (p := 628) (by norm_num) keyAt_628) (by decide)

theorem tGriess_ne_one : d.tGriess ≠ 1 := by
  intro h
  have h0 := tA_0 (d := d)
  rw [h] at h0
  obtain ⟨g, hg⟩ := isConj_iff.1 h0
  rw [mul_one, mul_inv_cancel] at hg
  exact R_ne_one (isShortCoord_of_key (p := 0) (by norm_num) keyAt_0) hg.symm

theorem xGriess_ne_one : d.xGriess ≠ 1 := by
  intro h
  have := Facts.orderOf_xGriess (d := d)
  rw [h, orderOf_one] at this
  exact absurd this (by norm_num)

theorem xGriess_sq : d.xGriess * d.xGriess = 1 := by
  rw [← R_xGriess, R_mul]; exact (R_zero (d := d)) ▸ congrArg (R d) (by decide)

/-- An element whose square is `s ≠ 1` with `s * s = 1` has order `4`. -/
theorem orderOf_four {G : Type*} [Group G] {p s : G} (hp : p ^ 2 = s) (hs : s * s = 1)
    (hs1 : s ≠ 1) : orderOf p = 4 := by
  have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := p) (by rw [pow_one, hp]; exact hs1)
    (by rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, hp, sq, hs])
  simpa using h

theorem tri2B : TriP d.tGriess (IsConj d.xGriess) := by
  refine ⟨R d (false, 0, 191), R d (true, 0, 191), R d (false, 63, 191), tA_0, tA_0', tA_1, ?_, ?_, ?_⟩
  · rw [R_mul, show Model.Pauli.mul (true, 0, 191) (false, 0, 191) = (true, 0, 0) by decide,
      R_xGriess]
  · rw [R_mul, show Model.Pauli.mul (false, 63, 191) (true, 0, 191) = (true, 63, 0) by decide,
      R_yB]
    exact isConj_conj' _ _
  · rw [R_mul, show Model.Pauli.mul (false, 63, 191) (false, 0, 191) = (false, 63, 0) by decide,
      R_zB]
    exact isConj_conj' _ _

theorem sq4A {y w : Model.Pauli} (h : (w.mul y).mul (w.mul y) = (true, 0, 0)) :
    SqClass d.xGriess (R d y * R d w) := by
  have hp : (R d y * R d w) ^ 2 = d.xGriess := by rw [sq, R_mul, R_mul, h, R_xGriess]
  exact ⟨orderOf_four hp xGriess_sq xGriess_ne_one, hp ▸ IsConj.refl _⟩

theorem tri4A : TriP d.tGriess (SqClass d.xGriess) :=
  ⟨R d (false, 0, 62), R d (false, 63, 191), R d (false, 57, 4), tA_552, tA_1, tA_628,
    sq4A (by decide), sq4A (by decide), sq4A (by decide)⟩

theorem S_R' (a : ℕ) (y : Model.Pauli) (X : d.MGriess) :
    S d a * (R d y * X) = R d (Model.conjYN a y) * (S d a * X) := by
  rw [← mul_assoc, S_R, mul_assoc]

theorem R_mul' (y w : Model.Pauli) (X : d.MGriess) : R d y * (R d w * X) = R d (w.mul y) * X := by
  rw [← mul_assoc, R_mul]

theorem S_sq (a : ℕ) (h : Model.Pauli.mul (false, a, Model.thetaN a) (false, a, Model.thetaN a) =
    (false, 0, 0)) : S d a * S d a = 1 := by
  rw [S_eq]
  calc τ d * R d (false, a, Model.thetaN a) * (τ d)⁻¹ * (τ d * R d (false, a, Model.thetaN a) * (τ d)⁻¹)
      = τ d * (R d (false, a, Model.thetaN a) * R d (false, a, Model.thetaN a)) * (τ d)⁻¹ := by group
    _ = 1 := by rw [R_mul, h, R_zero]; group

theorem S1_sq : S d 1 * S d 1 = 1 := S_sq 1 (by decide)
theorem S6_sq : S d 6 * S d 6 = 1 := S_sq 6 (by decide)

theorem S1_sq' (X : d.MGriess) : S d 1 * (S d 1 * X) = X := by rw [← mul_assoc, S1_sq, one_mul]
theorem S6_sq' (X : d.MGriess) : S d 6 * (S d 6 * X) = X := by rw [← mul_assoc, S6_sq, one_mul]

theorem S16 : S d 1 * (S d 6 * (S d 1 * S d 6)) = R d (true, 63, 0) := by
  rw [S_eq 1, S_eq 6, R_yB]
  calc τ d * R d (false, 1, Model.thetaN 1) * (τ d)⁻¹ * (τ d * R d (false, 6, Model.thetaN 6) * (τ d)⁻¹ *
        (τ d * R d (false, 1, Model.thetaN 1) * (τ d)⁻¹ * (τ d * R d (false, 6, Model.thetaN 6) * (τ d)⁻¹)))
      = τ d * (R d (false, 1, Model.thetaN 1) * R d (false, 6, Model.thetaN 6) *
          R d (false, 1, Model.thetaN 1) * R d (false, 6, Model.thetaN 6)) * (τ d)⁻¹ := by group
    _ = τ d * d.xGriess * (τ d)⁻¹ := by
      rw [R_mul, R_mul, R_mul, ← R_xGriess]
      exact congrArg (fun t => τ d * R d t * (τ d)⁻¹) (by decide)

theorem S16' (X : d.MGriess) : S d 1 * (S d 6 * (S d 1 * (S d 6 * X))) = R d (true, 63, 0) * X := by
  rw [← S16]; simp only [mul_assoc]

/-- The square of a product, as `R d w`, gives the `4B` class when `w` is a short key. -/
theorem sq4B {p : d.MGriess} {w : Model.Pauli} (hp : p ^ 2 = R d w)
    (hw : IsConj d.tGriess (R d w)) (hww : w.mul w = (false, 0, 0)) : SqClass d.tGriess p := by
  refine ⟨orderOf_four hp (by rw [R_mul, hww, R_zero]) ?_, hp ▸ hw⟩
  intro h1
  rw [h1] at hw
  exact tGriess_ne_one (isConj_one_right.1 hw.symm)

theorem tA_S (a : ℕ) (h : IsConj d.tGriess (R d (false, a, Model.thetaN a))) : IsConj d.tGriess (S d a) := by
  rw [S_eq]; exact h.trans (isConj_conj' _ _)

theorem tri4B : TriP d.tGriess (SqClass d.tGriess) := by
  have hS1 : IsConj d.tGriess (S d 1) := tA_S 1 (isConj_tGriess_R
    (isShortCoord_of_key (p := 49704) (by norm_num) (keyAt_49704.trans (by decide))) (by decide))
  have hS6 : IsConj d.tGriess (S d 6) := tA_S 6 (isConj_tGriess_R
    (isShortCoord_of_key (p := 50024) (by norm_num) (keyAt_50024.trans (by decide))) (by decide))
  have hv : R d (false, 0, 1) * R d (false, 0, 1) = 1 := by rw [R_mul]; exact (congrArg (R d) (by decide)).trans R_zero
  have hγ : IsConj d.tGriess (R d (false, 0, 1) * S d 6 * R d (false, 0, 1)) := by
    have : R d (false, 0, 1) * S d 6 * R d (false, 0, 1) = R d (false, 0, 1) * S d 6 * (R d (false, 0, 1))⁻¹ := by
      conv_rhs => rw [← eq_inv_of_mul_eq_one_left hv]
    rw [this]; exact hS6.trans (isConj_conj' _ _)
  refine ⟨R d (false, 0, 62), S d 1, R d (false, 0, 1) * S d 6 * R d (false, 0, 1), tA_552, hS1, hγ, ?_, ?_, ?_⟩
  · refine sq4B (w := (false, 1, 0)) ?_ (isConj_tGriess_R
      (isShortCoord_of_key (p := 49704) (by norm_num) keyAt_49704) (by decide)) (by decide)
    rw [sq]; simp only [mul_assoc, S_R', R_mul', S1_sq', S1_sq, S_R, R_mul]
    exact congrArg (R d) (by decide)
  · refine sq4B (w := (true, 0, 6)) ?_ (isConj_tGriess_R
      (isShortCoord_of_key (p := 178) (by norm_num) keyAt_178) (by decide)) (by decide)
    rw [sq]; simp only [mul_assoc, S_R', R_mul', S16', S16, S_R, R_mul]
    exact congrArg (R d) (by decide)
  · refine sq4B (w := (false, 6, 57)) ?_ (isConj_tGriess_R
      (isShortCoord_of_key (p := 50024) (by norm_num) keyAt_50024) (by decide)) (by decide)
    rw [sq]; simp only [mul_assoc, S_R', R_mul', S6_sq', S6_sq, S_R, R_mul]
    exact congrArg (R d) (by decide)

end CFSGOutside.HallPaige.M
