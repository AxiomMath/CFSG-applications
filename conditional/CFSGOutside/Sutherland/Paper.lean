import CFSGOutside.Corpus.DicksonGlTwo
import CFSGOutside.Corpus.Uc22s2112r34PglTameCasesIso
import CFSGOutside.Corpus.Defs.ClassicalModel
import CFSGOutside.Sutherland.Matrix
import CFSGOutside.Sutherland.Exist

/-!
# Subgroups of `GL₂(𝔽_ℓ)`, after Sutherland's Proposition `prop:maximal`

A. V. Sutherland, *Computing images of Galois representations attached to elliptic curves*, Forum
Math. Sigma 4 (2016), e4, §5. The lemmas of that proposition's proof that the small-`ℓ` result
(`SutherlandSmallEll`) uses; `χ(g)` is the Legendre symbol of `tr(g)² - 4 det(g)`.

The argument uses Dickson's classification (two corpus theorems): if `ℓ ∣ |G|`,
either `G ⊇ SL₂` or `G` has a normal subgroup of order `ℓ`, so it fixes a line and `χ ≠ -1` on
`G`; if `ℓ ∤ |G|`, the image of `G` in `PGL₂` is cyclic or dihedral (then `G` has an abelian
subgroup of index at most two and `χ` is constant on the elements of nonzero trace) or `A₄`,
`S₄`, `A₅` (then every element has a power of exponent at most `5` that is scalar).
-/

open Matrix
open scoped MatrixGroups

namespace CFSGOutside.Sutherland

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

theorem coe_det_ne_zero (g : GL (Fin 2) (ZMod ℓ)) :
    (g : Matrix (Fin 2) (Fin 2) (ZMod ℓ)).det ≠ 0 := by
  have := g.isUnit.map Matrix.detMonoidHom
  exact this.ne_zero

theorem SL2_le_iff (G : Subgroup (GL (Fin 2) (ZMod ℓ))) :
    CFSGOutside.Corpus.Open.StatedSL 2 (ZMod ℓ) ≤ G → SL2 ℓ ≤ G := by
  intro h
  rintro _ ⟨A, rfl⟩
  apply h
  apply Subgroup.subset_closure
  simp

/-! ### The Borel case -/

/-- The vectors fixed by a matrix group element: a subgroup of `GL₂`. -/
def fixer (w : Fin 2 → ZMod ℓ) : Subgroup (GL (Fin 2) (ZMod ℓ)) where
  carrier := {z | (z : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) *ᵥ w = w}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, Units.val_mul, ← Matrix.mulVec_mulVec] at ha hb ⊢
    rw [hb, ha]
  one_mem' := by simp only [Set.mem_setOf_eq, Units.val_one, Matrix.one_mulVec]
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at ha ⊢
    conv_lhs => rw [← ha]
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]

theorem chi_ne_neg_one_of_eigen {g : GL (Fin 2) (ZMod ℓ)} {w : Fin 2 → ZMod ℓ} (hw : w ≠ 0)
    {c : ZMod ℓ} (h : (g : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) *ᵥ w = c • w) : chi g ≠ -1 := by
  classical
  rw [chi, disc_eq_sq_of_eigen hw h]
  by_cases h0 : 2 * c - (g : Matrix (Fin 2) (Fin 2) (ZMod ℓ)).trace = 0
  · rw [h0]; simp
  · rw [quadraticChar_sq_one' h0]; decide

/-- If `G` has a normal Sylow `ℓ`-subgroup of order `ℓ`, then no element of `G` has `χ = -1`:
`G` fixes the line of fixed vectors of that subgroup. -/
theorem chi_ne_neg_one_of_normal_sylow (G : Subgroup (GL (Fin 2) (ZMod ℓ)))
    (P : Sylow ℓ G) (hPn : (P : Subgroup G).Normal) (hP : Nat.card P = ℓ)
    {g : GL (Fin 2) (ZMod ℓ)} (hg : g ∈ G) : chi g ≠ -1 := by
  classical
  set Q : Subgroup G := (P : Subgroup G)
  have hQ : Nat.card Q = ℓ := hP
  have : Nontrivial Q := Finite.one_lt_card_iff_nontrivial.mp (by rw [hQ]; exact hℓ.out.one_lt)
  have : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQ]; exact hℓ.out.ne_zero)
  obtain ⟨x, hx1⟩ := exists_ne (1 : Q)
  let ι : Q →* GL (Fin 2) (ZMod ℓ) := G.subtype.comp Q.subtype
  have hι : Function.Injective ι := G.subtype_injective.comp Q.subtype_injective
  set X : Matrix (Fin 2) (Fin 2) (ZMod ℓ) := ((ι x : GL (Fin 2) (ZMod ℓ)) : Matrix (Fin 2) (Fin 2) (ZMod ℓ))
  have hXℓ : X ^ ℓ = 1 := by
    have h1 : x ^ ℓ = 1 := by
      have h := pow_card_eq_one' (G := Q) (x := x)
      rwa [hQ] at h
    have h2 : (ι x) ^ ℓ = 1 := by rw [← map_pow, h1, map_one]
    have := congrArg Units.val h2
    simpa [X] using this
  have hX1 : X ≠ 1 := by
    intro h
    apply hx1
    apply hι
    rw [map_one]
    exact Units.ext h
  -- a nonzero fixed vector of `X`
  have hdet : (X - 1).det = 0 := by
    have h := sub_pow_char_of_commute (R := Matrix (Fin 2) (Fin 2) (ZMod ℓ)) ℓ
      (Commute.one_right X)
    rw [hXℓ, one_pow, sub_self] at h
    have := congrArg Matrix.det h
    rw [Matrix.det_pow, Matrix.det_zero] at this
    exact pow_eq_zero_iff hℓ.out.ne_zero |>.mp this
  obtain ⟨w, hw, hXw0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hXw : X *ᵥ w = w := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hXw0
    exact hXw0
  -- every element of `Q` fixes `w`
  have hQw : ∀ q : Q, ι q ∈ fixer w := by
    intro q
    have hq : q ∈ Subgroup.zpowers x := by
      rw [zpowers_eq_top_of_prime_card hQ hx1]; trivial
    have hle : Subgroup.zpowers x ≤ (fixer w).comap ι := by
      rw [Subgroup.zpowers_le]
      exact hXw
    exact hle hq
  -- `g` maps `w` to a fixed vector of `X`
  set gG : G := ⟨g, hg⟩
  have hy : gG⁻¹ * (x : G) * gG⁻¹⁻¹ ∈ Q := hPn.conj_mem _ x.2 gG⁻¹
  have hyw := hQw ⟨_, hy⟩
  simp only [ι, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype, inv_inv] at hyw
  change ((g⁻¹ * ((x : G) : GL (Fin 2) (ZMod ℓ)) * g : GL (Fin 2) (ZMod ℓ)) :
    Matrix (Fin 2) (Fin 2) (ZMod ℓ)) *ᵥ w = w at hyw
  have hXg : X *ᵥ ((g : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) *ᵥ w) =
      (g : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) *ᵥ w := by
    conv_rhs => rw [← hyw]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    congr 1
    simp only [X, ι, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      ← Units.val_mul]
    congr 1
    group
  obtain ⟨c, hc⟩ := eq_smul_of_fixed hX1 hw hXw hXg
  exact chi_ne_neg_one_of_eigen hw hc

/-! ### The case of an abelian subgroup of index at most two -/

theorem trace_conj (g c : GL (Fin 2) (ZMod ℓ)) :
    ((g * c * g⁻¹ : GL (Fin 2) (ZMod ℓ)) : Matrix (Fin 2) (Fin 2) (ZMod ℓ)).trace =
      (c : Matrix (Fin 2) (Fin 2) (ZMod ℓ)).trace := by
  rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_comm, ← mul_assoc, ← Units.val_mul,
    inv_mul_cancel, Units.val_one, one_mul]

theorem det_conj (g c : GL (Fin 2) (ZMod ℓ)) :
    ((g * c * g⁻¹ : GL (Fin 2) (ZMod ℓ)) : Matrix (Fin 2) (Fin 2) (ZMod ℓ)).det =
      (c : Matrix (Fin 2) (Fin 2) (ZMod ℓ)).det := by
  have h : (g : Matrix (Fin 2) (Fin 2) (ZMod ℓ)).det *
      ((g⁻¹ : GL (Fin 2) (ZMod ℓ)) : Matrix (Fin 2) (Fin 2) (ZMod ℓ)).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul]
  linear_combination (c : Matrix (Fin 2) (Fin 2) (ZMod ℓ)).det * h

theorem disc_eq_zero_of_isScalar {M : Matrix (Fin 2) (Fin 2) (ZMod ℓ)} (h : IsScalar M) :
    disc M = 0 := by
  obtain ⟨h01, h10, h00⟩ := h
  rw [disc, trace_two, det_two, h01, h10, h00]
  ring

/-! ### The exceptional case -/

theorem perm4_pow (σ : Equiv.Perm (Fin 4)) : σ ^ 2 = 1 ∨ σ ^ 3 = 1 ∨ σ ^ 4 = 1 := by
  revert σ
  decide

/-! ### From the projective image to an abelian subgroup of index at most two -/

theorem ker_le_center' (G : Subgroup (GL (Fin 2) (ZMod ℓ))) :
    (Matrix.ProjGenLinGroup.mk.subgroupMap G).ker ≤ Subgroup.center G := by
  intro x hx
  have hx' : Matrix.ProjGenLinGroup.mk (x : GL (Fin 2) (ZMod ℓ)) = 1 :=
    congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
  have hc : (x : GL (Fin 2) (ZMod ℓ)) ∈ Subgroup.center (GL (Fin 2) (ZMod ℓ)) :=
    (QuotientGroup.eq_one_iff _).1 hx'
  exact Subgroup.mem_center_iff.2 fun y => Subtype.ext (Subgroup.mem_center_iff.1 hc y)

theorem exists_C (G : Subgroup (GL (Fin 2) (ZMod ℓ))) (C₀ : Subgroup G)
    (hab : ∀ a ∈ C₀, ∀ b ∈ C₀, a * b = b * a) (hidx : C₀.index ∣ 2) :
    ∃ C : Subgroup (GL (Fin 2) (ZMod ℓ)), C ≤ G ∧ (∀ a ∈ C, ∀ b ∈ C, a * b = b * a) ∧
      (∀ g ∈ G, ∀ c ∈ C, g * c * g⁻¹ ∈ C) ∧ (∀ g ∈ G, g ^ 2 ∈ C) := by
  have hn : C₀.Normal ∧ ∀ g : G, g ^ 2 ∈ C₀ := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hidx with h | h
    · rw [Subgroup.index_eq_one] at h
      subst h
      exact ⟨inferInstance, fun _ => Subgroup.mem_top _⟩
    · exact ⟨Subgroup.normal_of_index_eq_two h, Subgroup.sq_mem_of_index_two h⟩
  refine ⟨C₀.map G.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [Subgroup.coe_subtype]
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hab a ha b hb]
  · rintro g hg _ ⟨c, hc, rfl⟩
    refine ⟨⟨g, hg⟩ * c * ⟨g, hg⟩⁻¹, hn.1.conj_mem c hc _, ?_⟩
    simp
  · intro g hg
    exact ⟨⟨g, hg⟩ ^ 2, hn.2 _, by simp⟩

/-! ### The main result -/

/-- The companion matrix `!![t, -1; 1, 0]` in `SL₂`. -/
def companion (t : ZMod ℓ) : Matrix.SpecialLinearGroup (Fin 2) (ZMod ℓ) :=
  ⟨!![t, -1; 1, 0], by rw [Matrix.det_fin_two_of]; simp; exact neg_neg _⟩

@[simp] theorem companion_coe (t : ZMod ℓ) :
    ((companion t : Matrix.SpecialLinearGroup (Fin 2) (ZMod ℓ)) :
      Matrix (Fin 2) (Fin 2) (ZMod ℓ)) = !![t, -1; 1, 0] := rfl

end CFSGOutside.Sutherland
