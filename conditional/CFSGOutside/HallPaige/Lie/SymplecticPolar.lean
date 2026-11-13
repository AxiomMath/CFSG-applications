import CFSGOutside.HallPaige.Lie.Symplectic
import CFSGOutside.HallPaige.Lie.TypeA
import CFSGOutside.HallPaige.Sporadic.GoodOfKlein

/-!
# The projective symplectic groups acting on points

`PSp_{2n}(K)` acts on the points of `ℙ(K^{2n})` (all isotropic for the alternating form). For
`n ≥ 2` the action has rank three, with the perpendicularity relation, and satisfies the
hypotheses of the polar-space criterion `CFSGOutside.HallPaige.wilcoxCriterion_of_polar`
(`CFSGOutside.HallPaige.Symplectic.wilcoxCriterion_PSp`), apart from the goodness of the point stabilizer.
-/

namespace CFSGOutside.HallPaige.Symplectic

open Matrix MulAction Corpus.Lie
open scoped LinearAlgebra.Projectivization

variable {n : ℕ} {K : Type} [Field K]

/-- Perpendicularity of points of `ℙ(K^{2n})`. -/
def perp (x y : ℙ K (Fin n ⊕ Fin n → K)) : Prop := form x.rep y.rep = 0

theorem form_eq_zero_iff_of_smul {u w : Fin n ⊕ Fin n → K} (a b : Kˣ) :
    form (a • u) (b • w) = 0 ↔ form u w = 0 := by
  rw [Units.smul_def, Units.smul_def, form_smul_left, form_smul_right]
  simp [a.ne_zero, b.ne_zero]

theorem perp_mk {u w : Fin n ⊕ Fin n → K} (hu : u ≠ 0) (hw : w ≠ 0) :
    perp (Projectivization.mk K u hu) (Projectivization.mk K w hw) ↔ form u w = 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep K u hu
  obtain ⟨b, hb⟩ := Projectivization.exists_smul_eq_mk_rep K w hw
  rw [perp, ← ha, ← hb, form_eq_zero_iff_of_smul]

theorem perp_refl (x : ℙ K (Fin n ⊕ Fin n → K)) : perp x x := form_self _

/-- `Sp` acts on points through its action on vectors. -/
theorem sp_smul_mk (g : StatedSp n K) {u : Fin n ⊕ Fin n → K} (hu : u ≠ 0) :
    g • Projectivization.mk K u hu =
      Projectivization.mk K (g • u) (fun h => hu (by simpa using congrArg (g⁻¹ • ·) h)) := by
  rw [Subgroup.smul_def, Projectivization.smul_mk]
  rfl

theorem perp_sp_smul (g : StatedSp n K) (x y : ℙ K (Fin n ⊕ Fin n → K)) :
    perp (g • x) (g • y) ↔ perp x y := by
  induction x using Projectivization.ind with
  | h u hu =>
  induction y using Projectivization.ind with
  | h w hw =>
  rw [sp_smul_mk, sp_smul_mk, perp_mk, perp_mk, form_smul]

/-- The action of `PSp` on points. -/
noncomputable def pspHom : StatedProj (StatedSp n K) →* Equiv.Perm (ℙ K (Fin n ⊕ Fin n → K)) :=
  QuotientGroup.lift _ (MulAction.toPermHom (StatedSp n K) (ℙ K (Fin n ⊕ Fin n → K))) (by
    intro g hg
    rw [MonoidHom.mem_ker]
    obtain ⟨c, hc⟩ := (Subgroup.mem_subgroupOf.1 hg)
    ext x
    induction x using Projectivization.ind with
    | h u hu =>
    change g • Projectivization.mk K u hu = Projectivization.mk K u hu
    rw [sp_smul_mk, Projectivization.mk_eq_mk_iff]
    refine ⟨c, ?_⟩
    change _ = ((g : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ u
    rw [← hc]
    simp [Matrix.GeneralLinearGroup.scalar, Units.smul_def])

noncomputable instance : MulAction (StatedProj (StatedSp n K)) (ℙ K (Fin n ⊕ Fin n → K)) :=
  MulAction.compHom _ pspHom

theorem psp_smul (g : StatedSp n K) (x : ℙ K (Fin n ⊕ Fin n → K)) :
    (g : StatedProj (StatedSp n K)) • x = g • x := rfl

theorem perp_psp_smul (g : StatedProj (StatedSp n K)) (x y : ℙ K (Fin n ⊕ Fin n → K)) :
    perp (g • x) (g • y) ↔ perp x y := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
  rw [psp_smul, psp_smul]
  exact perp_sp_smul g x y

section Criterion

variable (n K) in
/-- The base point `[e₀]`. -/
noncomputable def basePt (hn : 1 ≤ n) : ℙ K (Fin n ⊕ Fin n → K) :=
  Projectivization.mk K (Pi.single (.inl ⟨0, hn⟩) 1) (by simp)

theorem ne_smul_single_of_ne {i₀ : Fin n} {w : Fin n ⊕ Fin n → K} (hw : w ≠ 0)
    (h : Projectivization.mk K w hw ≠ Projectivization.mk K (Pi.single (.inl i₀) 1) (by simp)) :
    ∀ c : K, w ≠ c • Pi.single (.inl i₀) 1 := by
  intro c hc
  apply h
  rw [Projectivization.mk_eq_mk_iff]
  have hc0 : c ≠ 0 := by rintro rfl; simp at hc; exact hw hc
  exact ⟨Units.mk0 c hc0, hc.symm⟩

/-- `PSp` is transitive on points. -/
theorem psp_exists_smul_eq (hn : 1 ≤ n) (y : ℙ K (Fin n ⊕ Fin n → K)) :
    ∃ g : StatedProj (StatedSp n K), g • basePt n K hn = y := by
  induction y using Projectivization.ind with
  | h w hw =>
  obtain ⟨g, hg⟩ := exists_smul_eq (n := n) (K := K) (u := Pi.single (.inl ⟨0, hn⟩) 1) (by simp) hw
  refine ⟨g, ?_⟩
  rw [psp_smul, basePt, sp_smul_mk]
  congr

/-- **Hall–Paige data for `PSp_{2n}(K)`, `n ≥ 2`**: the polar-space criterion holds as soon as
the point stabilizer is good. -/
theorem wilcoxCriterion_PSp [Finite K] (hn : 2 ≤ n)
    (hgood : IsGood (stabilizer (StatedProj (StatedSp n K)) (basePt n K (by omega)))) :
    WilcoxCriterion (StatedProj (StatedSp n K)) := by
  have hn1 : 1 ≤ n := by omega
  set i₀ : Fin n := ⟨0, hn1⟩
  set i₁ : Fin n := ⟨1, hn⟩
  set e : Fin n ⊕ Fin n → K := Pi.single (.inl i₀) 1 with he
  have he0 : e ≠ 0 := by simp [e]
  have hx₀ : basePt n K hn1 = Projectivization.mk K e he0 := rfl
  refine wilcoxCriterion_of_polar perp (basePt n K hn1) perp_refl perp_psp_smul
    (psp_exists_smul_eq hn1) ?_ ?_ ?_ ?_ hgood
  · intro y y' hy hy' hRy hRy'
    induction y using Projectivization.ind with
    | h w hw =>
    induction y' using Projectivization.ind with
    | h w' hw' =>
    rw [hx₀, perp_mk] at hRy hRy'
    rw [hx₀] at hy hy'
    obtain ⟨g, hg1, hg2⟩ := exists_smul_eq_of_form_eq_zero i₀ hRy hRy'
      (ne_smul_single_of_ne hw hy) (ne_smul_single_of_ne hw' hy')
    refine ⟨g, ?_, ?_⟩
    · rw [psp_smul, hx₀, sp_smul_mk]; congr
    · rw [psp_smul, sp_smul_mk]; congr
  · intro y y' hRy hRy'
    induction y using Projectivization.ind with
    | h w hw =>
    induction y' using Projectivization.ind with
    | h w' hw' =>
    rw [hx₀, perp_mk] at hRy hRy'
    set a := form e w
    set a' := form e w'
    have hw1 : form e (a⁻¹ • w) = 1 := by rw [form_smul_right, inv_mul_cancel₀ hRy]
    have hw1' : form e (a'⁻¹ • w') = 1 := by rw [form_smul_right, inv_mul_cancel₀ hRy']
    obtain ⟨g, hg1, hg2⟩ := exists_smul_eq_of_form_eq_one i₀ hw1 hw1'
    have hmk : ∀ (v : Fin n ⊕ Fin n → K) (hv : v ≠ 0) (c : K) (hc : c ≠ 0),
        Projectivization.mk K (c • v) (smul_ne_zero hc hv) = Projectivization.mk K v hv :=
      fun v hv c hc => (Projectivization.mk_eq_mk_iff _ _ _ _ _).2 ⟨Units.mk0 c hc, by
        simp [Units.smul_def]⟩
    refine ⟨g, ?_, ?_⟩
    · rw [psp_smul, hx₀, sp_smul_mk]; congr
    · rw [psp_smul, ← hmk w hw a⁻¹ (inv_ne_zero hRy), sp_smul_mk, ← hmk w' hw' a'⁻¹ (inv_ne_zero hRy')]
      congr
  · -- three mutually perpendicular points `[e₀], [e₁], [e₀ + e₁]`
    set e₁ : Fin n ⊕ Fin n → K := Pi.single (.inl i₁) 1
    have hi : (Sum.inl i₀ : Fin n ⊕ Fin n) ≠ .inl i₁ := by simp [i₀, i₁, Fin.ext_iff]
    have he₁ : e₁ ≠ 0 := by simp [e₁]
    have he₀₁ : e + e₁ ≠ 0 := by
      intro h; have := congrFun h (.inl i₀); simp [e, e₁, Pi.single_apply, hi] at this
    refine ⟨Projectivization.mk K e₁ he₁, Projectivization.mk K (e + e₁) he₀₁, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hx₀, Ne, Projectivization.mk_eq_mk_iff]
      rintro ⟨a, ha⟩
      have := congrFun ha (.inl i₁)
      simp [e, e₁, Units.smul_def, Pi.single_apply, hi.symm] at this
    · rw [hx₀, Ne, Projectivization.mk_eq_mk_iff]
      rintro ⟨a, ha⟩
      have := congrFun ha (.inl i₁)
      simp [e, e₁, Units.smul_def, Pi.single_apply, hi.symm] at this
    · rw [Ne, Projectivization.mk_eq_mk_iff]
      rintro ⟨a, ha⟩
      have := congrFun ha (.inl i₀)
      simp [e, e₁, Units.smul_def, Pi.single_apply, hi] at this
    · rw [hx₀, perp_mk, form_single_inl]; simp [e₁]
    · rw [hx₀, perp_mk, form_single_inl]; simp [e, e₁]
    · rw [perp_mk, form_single_inl]; simp [e, e₁]
  · -- three mutually non-perpendicular points `[e₀], [f₀], [e₀ + f₀]`
    set f₀ : Fin n ⊕ Fin n → K := Pi.single (.inr i₀) 1
    have hf₀ : f₀ ≠ 0 := by simp [f₀]
    have hef : e + f₀ ≠ 0 := by
      intro h; have := congrFun h (.inl i₀); simp [e, f₀, Pi.single_apply] at this
    refine ⟨Projectivization.mk K f₀ hf₀, Projectivization.mk K (e + f₀) hef, ?_, ?_, ?_⟩
    · rw [hx₀, perp_mk, form_single_inl]; simp [f₀]
    · rw [hx₀, perp_mk, form_single_inl]; simp [e, f₀]
    · rw [perp_mk, form_add_right, form_self, add_zero, form_swap, form_single_inl]; simp [f₀]

end Criterion

section Good

/-- The number of points of `ℙ(K^{2n})`. -/
theorem index_stabilizer_basePt [Finite K] (hn : 1 ≤ n) :
    (stabilizer (StatedProj (StatedSp n K)) (basePt n K hn)).index =
      ∑ i ∈ Finset.range (n + n), Nat.card K ^ i := by
  rw [index_stabilizer, ← Projectivization.card_of_finrank K (Fin n ⊕ Fin n → K) (by simp)]
  have horb : orbit (StatedProj (StatedSp n K)) (basePt n K hn) = Set.univ :=
    Set.eq_univ_of_forall fun y => psp_exists_smul_eq hn y
  rw [horb, Set.ncard_univ]

/-- For `q` even the point stabilizer has odd index, hence is good. -/
theorem isGood_stabilizer_basePt_of_even [Finite K] (hn : 1 ≤ n) (hq : Even (Nat.card K))
    (hG : IsGood (StatedProj (StatedSp n K))) :
    IsGood (stabilizer (StatedProj (StatedSp n K)) (basePt n K hn)) :=
  isGood_of_index_odd hG _ (by rw [index_stabilizer_basePt]; exact odd_sum_range_pow_of_even hq (by omega))

/-- The sign vector `-1` on the `i`-th hyperbolic plane. -/
def planeSign (i : Fin n) : Fin n ⊕ Fin n → K :=
  fun j => if j = .inl i ∨ j = .inr i then -1 else 1

theorem planeSign_mul_self (i : Fin n) : planeSign (K := K) i * planeSign i = 1 := by
  funext j; simp only [planeSign, Pi.mul_apply, Pi.one_apply]; split_ifs <;> simp

theorem form_planeSign (i : Fin n) (u w : Fin n ⊕ Fin n → K) :
    form (diagonal (planeSign i) *ᵥ u) (diagonal (planeSign i) *ᵥ w) = form u w := by
  rw [form_eq, form_eq]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [mulVec_diagonal, planeSign]
  by_cases hk : k = i
  · subst hk; simp
  · simp [hk]

/-- The sign element of `Sp`. -/
def planeSignSp (i : Fin n) : StatedSp n K :=
  ⟨⟨diagonal (planeSign i), diagonal (planeSign i), by
      rw [diagonal_mul_diagonal', ← diagonal_one]; congr 1; funext j
      exact congrFun (planeSign_mul_self i) j,
    by rw [diagonal_mul_diagonal', ← diagonal_one]; congr 1; funext j
       exact congrFun (planeSign_mul_self i) j⟩,
    (mem_statedSp_iff _).2 (form_planeSign i)⟩

theorem coe_planeSignSp (i : Fin n) :
    (((planeSignSp (K := K) i : StatedSp n K) : GL (Fin n ⊕ Fin n) K) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = diagonal (planeSign i) := rfl

theorem planeSignSp_mul_self (i : Fin n) : planeSignSp (K := K) i * planeSignSp i = 1 := by
  apply Subtype.ext; apply Units.ext
  change diagonal (planeSign (K := K) i) * diagonal (planeSign i) = 1
  rw [diagonal_mul_diagonal', ← diagonal_one]; congr 1; funext j
  exact congrFun (planeSign_mul_self i) j

theorem planeSignSp_comm (i j : Fin n) :
    planeSignSp (K := K) i * planeSignSp j = planeSignSp j * planeSignSp i := by
  apply Subtype.ext; apply Units.ext
  change diagonal (planeSign (K := K) i) * diagonal (planeSign j) =
    diagonal (planeSign j) * diagonal (planeSign i)
  rw [diagonal_mul_diagonal', diagonal_mul_diagonal']; congr 1; funext k; exact mul_comm _ _

/-- An element of `Sp` with two distinct diagonal entries is not a scalar. -/
theorem mk_ne_one_of_diag_ne (g : StatedSp n K) {a b : Fin n ⊕ Fin n}
    (h : ((g : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) a a ≠
      ((g : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) b b) :
    (g : StatedProj (StatedSp n K)) ≠ 1 := by
  rw [Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  rintro ⟨c, hc⟩
  apply h
  rw [← hc]
  simp [Matrix.GeneralLinearGroup.scalar]

theorem planeSignSp_smul_basePt (hn : 1 ≤ n) (i : Fin n) (hi : i ≠ ⟨0, hn⟩) :
    (planeSignSp (K := K) i : StatedProj (StatedSp n K)) • basePt n K hn = basePt n K hn := by
  rw [psp_smul, basePt, sp_smul_mk]
  congr 1
  change diagonal (planeSign i) *ᵥ _ = _
  funext j
  rw [mulVec_diagonal]
  by_cases hj : j = .inl ⟨0, hn⟩
  · subst hj; simp [planeSign, Ne.symm hi]
  · simp [Pi.single_apply, hj]

/-- **The Klein four-group of plane signs.** For `q` odd and `n ≥ 3` the point stabilizer is
good. -/
theorem isGood_stabilizer_basePt_of_three_le [Finite K] (hn : 3 ≤ n) (hK : (-1 : K) ≠ 1) :
    IsGood (stabilizer (StatedProj (StatedSp n K)) (basePt n K (by omega))) := by
  have hn1 : 1 ≤ n := by omega
  set i₀ : Fin n := ⟨0, hn1⟩
  set i₁ : Fin n := ⟨1, by omega⟩
  set i₂ : Fin n := ⟨2, hn⟩
  have h10 : i₁ ≠ i₀ := by simp [i₀, i₁, Fin.ext_iff]
  have h20 : i₂ ≠ i₀ := by simp [i₀, i₂, Fin.ext_iff]
  have h12 : i₁ ≠ i₂ := by simp [i₁, i₂, Fin.ext_iff]
  set u := planeSignSp (K := K) i₁
  set v := planeSignSp (K := K) i₂
  have hu : (u : StatedProj (StatedSp n K)) ≠ 1 := mk_ne_one_of_diag_ne u (a := .inl i₁)
    (b := .inl i₀) (by simp [u, coe_planeSignSp, planeSign, h10]; exact ⟨fun h => h10 h.symm, hK⟩)
  have hv : (v : StatedProj (StatedSp n K)) ≠ 1 := mk_ne_one_of_diag_ne v (a := .inl i₂)
    (b := .inl i₀) (by simp [v, coe_planeSignSp, planeSign, h20]; exact ⟨fun h => h20 h.symm, hK⟩)
  have huv : (u : StatedProj (StatedSp n K)) ≠ v := by
    rw [Ne, QuotientGroup.eq]
    have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right (planeSignSp_mul_self _)
    rw [hu']
    refine fun h => (mk_ne_one_of_diag_ne (u * v) (a := .inl i₁) (b := .inl i₀) ?_)
      ((QuotientGroup.eq_one_iff _).2 h)
    change (diagonal (planeSign (K := K) i₁) * diagonal (planeSign i₂) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (.inl i₁) (.inl i₁) ≠
      (diagonal (planeSign (K := K) i₁) * diagonal (planeSign i₂) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (.inl i₀) (.inl i₀)
    have e1 : planeSign (K := K) i₁ (.inl i₁) = -1 := by simp [planeSign]
    have e2 : planeSign (K := K) i₂ (.inl i₁) = 1 := by simp [planeSign, h12]
    have e3 : planeSign (K := K) i₁ (.inl i₀) = 1 := by simp [planeSign, Ne.symm h10]
    have e4 : planeSign (K := K) i₂ (.inl i₀) = 1 := by simp [planeSign, Ne.symm h20]
    rw [diagonal_mul_diagonal', diagonal_apply_eq, diagonal_apply_eq, e1, e2, e3, e4]
    simpa using hK
  refine Subgroup.isGood_of_commuting_involutions _ (u := (u : StatedProj (StatedSp n K)))
    (v := v) (planeSignSp_smul_basePt hn1 i₁ h10) (planeSignSp_smul_basePt hn1 i₂ h20)
    ?_ ?_ ?_ hu hv huv
  · rw [sq, ← QuotientGroup.mk_mul, planeSignSp_mul_self, QuotientGroup.mk_one]
  · rw [sq, ← QuotientGroup.mk_mul, planeSignSp_mul_self, QuotientGroup.mk_one]
  · rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, planeSignSp_comm]

end Good

end CFSGOutside.HallPaige.Symplectic
