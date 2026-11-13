import CFSGOutside.Corpus.HallPaige.M

/-!
# The visible elements of `MGriess` used for the Monster triangles

In the Griess–Conway model `MGriess = AutO` (a `GriessModel` satisfying the corpus facts,
`Corpus/HallPaige/M.lean`), `R y = ρ(pauliQ y)` is the element of the extraspecial group `Q` with Pauli
coordinates `y` (a triple `(sign, code, cocode)` of numbers), `S a` the sign letter of the Golay
codeword `a`, and `τ` the triality. From the corpus facts:

* `R y * R w = R (w.mul y)` (`rhoEquiv_mul`, `pauliQ_mul`);
* `S a * R y * (S a)⁻¹ = R (conjYN a y)` (`thetaEquiv_conj_rhoEquiv`, `conjQ_sign_toQ`);
* `S a = τ * R (false, a, θ a) * τ⁻¹` (`thetaEquiv_signLiftPair`, `XQ_eq`, `thetaD_toC`);
* `R (true, 0, 0) = xGriess`, `R (true, 63, 0) = τ xGriess τ⁻¹`, `R (false, 63, 0) = τ² xGriess τ⁻²`;
* `R y` is conjugate to `tGriess` when `y` is a short key (`key_short`, `trace_rho_short`,
  `shapeSix_isConj_tGriess_of_trace`).

All Pauli arithmetic is evaluated by `decide`.
-/

namespace CFSGOutside.HallPaige.M

open CFSGOutside.Corpus.M CFSGOutside.Corpus.M.GriessModel CFSGOutside.Corpus.M.Monster.AxisCount
  CFSGOutside.Corpus.M.Monster.B

variable (d : GriessModel)

/-- `ρ(r)` as an element of `MGriess`. -/
noncomputable def Rq [d.Facts] (r : d.Q) : d.MGriess := ⟨d.rhoEquiv r, Facts.rhoEquiv_mem_AutO r⟩

/-- `ρ(pauliQ y)`. -/
noncomputable def R [d.Facts] (y : Model.Pauli) : d.MGriess := Rq d (d.pauliQ y)

/-- The visible pair of the sign letter `a` (corpus `signPair a`, `signLiftPair ⟨toC a, 0⟩`). -/
def P (a : ℕ) : d.Pvis := d.signLiftPair (d.parker (d.toC a) 0)

/-- The sign letter `a`. -/
noncomputable def S [d.Facts] (a : ℕ) : d.MGriess := ⟨d.thetaEquiv (P d a), Facts.thetaEquiv_mem_AutO _⟩

/-- The triality `τ`. -/
noncomputable def τ [d.Facts] : d.MGriess := ⟨d.tauB, Facts.tauB_mem_AutO⟩

variable {d} [d.Facts]

theorem Rq_mul (r r' : d.Q) : Rq d r * Rq d r' = Rq d (r' * r) :=
  Subtype.ext (Facts.rhoEquiv_mul r' r).symm

theorem R_mul (y w : Model.Pauli) : R d y * R d w = R d (w.mul y) := by
  rw [R, R, Rq_mul, R, Facts.pauliQ_mul]

theorem Rq_one : Rq d 1 = 1 := by
  have h := Rq_mul (d := d) 1 1
  rw [one_mul] at h
  calc Rq d 1 = Rq d 1 * Rq d 1 * (Rq d 1)⁻¹ := by group
    _ = 1 := by rw [h]; group

theorem R_zero : R d (false, 0, 0) = 1 := by
  rw [R, Facts.pauliQ_zero, Rq_one]

theorem S_conj (a : ℕ) (y : Model.Pauli) : S d a * R d y * (S d a)⁻¹ = R d (Model.conjYN a y) := by
  apply Subtype.ext
  show d.thetaEquiv (P d a) * d.rhoEquiv (d.pauliQ y) * (d.thetaEquiv (P d a))⁻¹ = d.rhoEquiv (d.pauliQ _)
  rw [Facts.thetaEquiv_conj_rhoEquiv, P, Facts.conjQ_sign_toQ]

theorem S_R (a : ℕ) (y : Model.Pauli) : S d a * R d y = R d (Model.conjYN a y) * S d a := by
  rw [← S_conj]; group

theorem XQ_toC (a : ℕ) : d.XQ (d.parker (d.toC a) 0) = d.pauliQ (false, a, Model.thetaN a) := by
  rw [Facts.XQ_eq, pauliQ, toSC, ← Facts.thetaD_toC]
  rfl

theorem S_eq (a : ℕ) : S d a = τ d * R d (false, a, Model.thetaN a) * (τ d)⁻¹ := by
  apply Subtype.ext
  show d.thetaEquiv (d.signLiftPair (d.parker (d.toC a) 0)) = d.tauB * d.rhoEquiv (d.pauliQ _) * d.tauB⁻¹
  rw [Facts.thetaEquiv_signLiftPair, XQ_toC]

theorem zQ_eq : d.pauliQ (true, 0, 0) = d.zQ := by
  unfold pauliQ zQ
  congr 1
  simp [toSC, boolZ, Model.Pauli.s, Model.Pauli.a, Model.Pauli.d, Facts.toC_zero, Facts.toD_zero]

theorem wQ_eq : d.wQ = d.pauliQ (false, 63, Model.thetaN 63) := by
  rw [wQ, Facts.ΩC_eq_toC, XQ_toC]

theorem R_xGriess : R d (true, 0, 0) = d.xGriess := by
  apply Subtype.ext
  show d.rhoEquiv (d.pauliQ (true, 0, 0)) = (d.xGriess : d.SpaceB ≃ₗ[ℚ] d.SpaceB)
  rw [zQ_eq, Facts.coe_xGriess]; rfl

theorem theta63 : Model.thetaN 63 = 0 := by decide

theorem R_yB : R d (true, 63, 0) = τ d * d.xGriess * (τ d)⁻¹ := by
  apply Subtype.ext
  show d.rhoEquiv (d.pauliQ (true, 63, 0)) =
    d.tauB * (d.xGriess : d.SpaceB ≃ₗ[ℚ] d.SpaceB) * d.tauB⁻¹
  have e : d.pauliQ (true, 63, 0) = d.zQ * d.wQ := by
    rw [← zQ_eq, wQ_eq, theta63, ← Facts.pauliQ_mul]
    rfl
  rw [e, Facts.rhoEquiv_zQ_wQ, Facts.coe_xGriess, Facts.xmat_eq_xB]
  rfl

theorem R_zB : R d (false, 63, 0) = τ d ^ 2 * d.xGriess * (τ d ^ 2)⁻¹ := by
  apply Subtype.ext
  show d.rhoEquiv (d.pauliQ (false, 63, 0)) =
    d.tauB ^ 2 * (d.xGriess : d.SpaceB ≃ₗ[ℚ] d.SpaceB) * (d.tauB ^ 2)⁻¹
  have e : d.pauliQ (false, 63, 0) = d.wQ := by rw [wQ_eq, theta63]
  rw [e, Facts.rhoEquiv_wQ, Facts.coe_xGriess, Facts.xmat_eq_xB]
  rfl

theorem isShortCoord_of_key {y : Model.Pauli} {p : ℕ} (hp : p < 98280)
    (hk : Native.keyAt (Native.thetaTab ()) p = (y.2.1, y.2.2)) :
    d.IsShortCoord (d.coordOf (d.pauliQ y)) := by
  have h := Facts.key_short (d := d) p hp
  rw [Facts.keyOf_eq p hp, hk] at h
  rw [Facts.coordOf_pauliQ]
  exact h

theorem R_ne_one {y : Model.Pauli} (hy : d.IsShortCoord (d.coordOf (d.pauliQ y))) : R d y ≠ 1 := by
  intro h
  apply Facts.ne_one_of_isShortCoord hy
  apply Facts.rhoEquiv_injective (d := d)
  have h1 : d.rhoEquiv (1 : d.Q) = 1 := congrArg Subtype.val (Rq_one (d := d))
  rw [h1]
  exact congrArg Subtype.val h

/-- A short `R y` is conjugate to `tGriess`. -/
theorem isConj_tGriess_R {y : Model.Pauli} (hy : d.IsShortCoord (d.coordOf (d.pauliQ y)))
    (hsq : y.mul y = (false, 0, 0)) : IsConj d.tGriess (R d y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine Facts.shapeSix_isConj_tGriess_of_trace ?_ (Facts.trace_rho_short hy)
  refine orderOf_eq_prime ?_ (R_ne_one hy)
  rw [sq, R_mul, hsq, R_zero]

theorem isConj_conj' {G : Type*} [Group G] (g x : G) : IsConj x (g * x * g⁻¹) :=
  isConj_iff.2 ⟨g, rfl⟩

end CFSGOutside.HallPaige.M
