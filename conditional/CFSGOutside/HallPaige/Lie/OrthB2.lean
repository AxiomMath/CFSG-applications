import CFSGOutside.HallPaige.Lie.SymplecticCase
import CFSGOutside.HallPaige.Lie.Quaternion
import CFSGOutside.HallPaige.Lie.OrthEichler

/-!
# The catalogue case `B_2(q)`, `q` odd

The corpus identifies `B_2(q)` with `PSp_4(q)` for every `q`
(`CFSGOutside.Corpus.Lie.nonempty_mulEquiv_lie_B2_of_statedProj`). For `q` odd the stabilizer of a
point of `ℙ³(q)` in `PSp_4(q)` contains no Klein four-group when `q ≡ 3 (mod 4)`, but it contains
a quaternion group `Q₈ ≤ SL₂(q)` acting on the second hyperbolic plane:
`I = [[0, 1], [-1, 0]]`, `J = [[s, t], [t, -s]]` with `s² + t² = -1`. Hence it is good
(`CFSGOutside.HallPaige.isGood_of_quaternion`), and the polar-space criterion applies.
-/

namespace CFSGOutside.HallPaige.Symplectic

open Matrix MulAction Corpus.Lie Orth

variable {n : ℕ} {K : Type} [Field K]

/-- The matrix `[[a, b], [c, d]]` acting on the `i`-th hyperbolic plane (identity elsewhere). -/
def planeLin (i : Fin n) (a b c d : K) : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K) where
  toFun v := v + ((a - 1) * v (.inl i) + b * v (.inr i)) • Pi.single (.inl i) 1 +
    (c * v (.inl i) + (d - 1) * v (.inr i)) • Pi.single (.inr i) 1
  map_add' u v := by
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  map_smul' r v := by
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem planeLin_inl (i : Fin n) (a b c d : K) (v : Fin n ⊕ Fin n → K) :
    planeLin i a b c d v (.inl i) = a * v (.inl i) + b * v (.inr i) := by
  simp [planeLin, Pi.single_apply]; ring

theorem planeLin_inr (i : Fin n) (a b c d : K) (v : Fin n ⊕ Fin n → K) :
    planeLin i a b c d v (.inr i) = c * v (.inl i) + d * v (.inr i) := by
  simp [planeLin, Pi.single_apply]; ring

theorem planeLin_other (i : Fin n) (a b c d : K) (v : Fin n ⊕ Fin n → K) {k : Fin n ⊕ Fin n}
    (h1 : k ≠ .inl i) (h2 : k ≠ .inr i) : planeLin i a b c d v k = v k := by
  simp [planeLin, Pi.single_apply, h1, h2]

theorem planeLin_ext (i : Fin n) {a b c d a' b' c' d' : K} {u v : Fin n ⊕ Fin n → K}
    (h1 : a * v (.inl i) + b * v (.inr i) = a' * u (.inl i) + b' * u (.inr i))
    (h2 : c * v (.inl i) + d * v (.inr i) = c' * u (.inl i) + d' * u (.inr i))
    (h3 : ∀ k, k ≠ .inl i → k ≠ .inr i → v k = u k) :
    planeLin i a b c d v = planeLin i a' b' c' d' u := by
  funext k
  by_cases hk1 : k = .inl i
  · subst hk1; rw [planeLin_inl, planeLin_inl, h1]
  by_cases hk2 : k = .inr i
  · subst hk2; rw [planeLin_inr, planeLin_inr, h2]
  rw [planeLin_other _ _ _ _ _ _ hk1 hk2, planeLin_other _ _ _ _ _ _ hk1 hk2, h3 k hk1 hk2]

theorem planeLin_planeLin (i : Fin n) (a b c d a' b' c' d' : K) (v : Fin n ⊕ Fin n → K) :
    planeLin i a b c d (planeLin i a' b' c' d' v) =
      planeLin i (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') v := by
  apply planeLin_ext
  · rw [planeLin_inl, planeLin_inr]; ring
  · rw [planeLin_inl, planeLin_inr]; ring
  · intro k h1 h2; exact planeLin_other _ _ _ _ _ _ h1 h2

theorem planeLin_one (i : Fin n) (v : Fin n ⊕ Fin n → K) : planeLin i 1 0 0 1 v = v := by
  funext k; simp [planeLin]

theorem planeLin_eq_self (i : Fin n) {a b c d : K} (ha : a = 1) (hb : b = 0) (hc : c = 0)
    (hd : d = 1) (v : Fin n ⊕ Fin n → K) : planeLin i a b c d v = v := by
  subst ha hb hc hd; exact planeLin_one i v

/-- The plane element as an element of `GL`. -/
noncomputable def planeGL (i : Fin n) (a b c d : K) (h : a * d - b * c = 1) :
    GL (Fin n ⊕ Fin n) K :=
  glOfLin (planeLin i a b c d) (planeLin i d (-b) (-c) a)
    (fun v => by
      rw [planeLin_planeLin]
      exact planeLin_eq_self i (by linear_combination h) (by ring) (by ring)
        (by linear_combination h) v)
    (fun v => by
      rw [planeLin_planeLin]
      exact planeLin_eq_self i (by linear_combination h) (by ring) (by ring)
        (by linear_combination h) v)

theorem planeGL_smul (i : Fin n) (a b c d : K) (h : a * d - b * c = 1) (v : Fin n ⊕ Fin n → K) :
    planeGL i a b c d h • v = planeLin i a b c d v :=
  glOfLin_smul _ _ _ _ v

theorem planeGL_mul (i : Fin n) {a b c d a' b' c' d' : K} (h : a * d - b * c = 1)
    (h' : a' * d' - b' * c' = 1) (h'' : (a * a' + b * c') * (c * b' + d * d') -
      (a * b' + b * d') * (c * a' + d * c') = 1) :
    planeGL i a b c d h * planeGL i a' b' c' d' h' =
      planeGL i (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') h'' :=
  gl_ext fun v => by rw [mul_smul, planeGL_smul, planeGL_smul, planeGL_smul, planeLin_planeLin]

theorem planeGL_congr (i : Fin n) {a b c d a' b' c' d' : K} (h : a * d - b * c = 1)
    (h' : a' * d' - b' * c' = 1) (ha : a = a') (hb : b = b') (hc : c = c') (hd : d = d') :
    planeGL i a b c d h = planeGL i a' b' c' d' h' := by
  subst ha hb hc hd; rfl

theorem planeGL_mem (i : Fin n) (a b c d : K) (h : a * d - b * c = 1) :
    planeGL i a b c d h ∈ StatedSp n K := by
  rw [mem_statedSp_iff]
  intro u w
  change form (planeGL i a b c d h • u) (planeGL i a b c d h • w) = form u w
  rw [planeGL_smul, planeGL_smul, form_eq, form_eq]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : k = i
  · subst hk
    rw [planeLin_inl, planeLin_inl, planeLin_inr, planeLin_inr]
    linear_combination (u (.inl k) * w (.inr k) - u (.inr k) * w (.inl k)) * h
  · have h1 : (Sum.inl k : Fin n ⊕ Fin n) ≠ .inl i := fun e => hk (Sum.inl_injective e)
    have h2 : (Sum.inr k : Fin n ⊕ Fin n) ≠ .inr i := fun e => hk (Sum.inr_injective e)
    rw [planeLin_other _ _ _ _ _ _ h1 Sum.inl_ne_inr, planeLin_other _ _ _ _ _ _ h1 Sum.inl_ne_inr,
      planeLin_other _ _ _ _ _ _ Sum.inr_ne_inl h2, planeLin_other _ _ _ _ _ _ Sum.inr_ne_inl h2]

/-- The plane element as an element of `Sp`. -/
noncomputable def planeSp (i : Fin n) (a b c d : K) (h : a * d - b * c = 1) : StatedSp n K :=
  ⟨planeGL i a b c d h, planeGL_mem i a b c d h⟩

theorem planeSp_mul (i : Fin n) {a b c d a' b' c' d' : K} (h : a * d - b * c = 1)
    (h' : a' * d' - b' * c' = 1) (h'' : (a * a' + b * c') * (c * b' + d * d') -
      (a * b' + b * d') * (c * a' + d * c') = 1) :
    planeSp i a b c d h * planeSp i a' b' c' d' h' =
      planeSp i (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') h'' :=
  Subtype.ext (planeGL_mul i h h' h'')

theorem planeSp_congr (i : Fin n) {a b c d a' b' c' d' : K} (h : a * d - b * c = 1)
    (h' : a' * d' - b' * c' = 1) (ha : a = a') (hb : b = b') (hc : c = c') (hd : d = d') :
    planeSp i a b c d h = planeSp i a' b' c' d' h' :=
  Subtype.ext (planeGL_congr i h h' ha hb hc hd)

theorem planeSp_one (i : Fin n) (h : (1 : K) * 1 - 0 * 0 = 1) : planeSp i 1 0 0 1 h = 1 := by
  apply Subtype.ext
  refine gl_ext fun (v : Fin n ⊕ Fin n → K) => ?_
  change planeGL i 1 0 0 1 h • v = (1 : GL (Fin n ⊕ Fin n) K) • v
  rw [planeGL_smul, planeLin_one, one_smul]

theorem coe_planeSp_apply (i : Fin n) (a b c d : K) (h : a * d - b * c = 1)
    (k l : Fin n ⊕ Fin n) :
    (((planeSp i a b c d h : StatedSp n K) : GL (Fin n ⊕ Fin n) K) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) k l = planeLin i a b c d (Pi.single l 1) k :=
  LinearMap.toMatrix'_apply _ _ _

theorem planeSp_smul_basePt (hn : 1 ≤ n) (i : Fin n) (hi : i ≠ ⟨0, hn⟩) (a b c d : K)
    (h : a * d - b * c = 1) :
    (planeSp i a b c d h : StatedProj (StatedSp n K)) • basePt n K hn = basePt n K hn := by
  rw [psp_smul, basePt, sp_smul_mk]
  congr 1
  change planeGL i a b c d h • (Pi.single (.inl ⟨0, hn⟩) 1 : Fin n ⊕ Fin n → K) = _
  rw [planeGL_smul]
  funext k
  simp [planeLin, Pi.single_apply, Ne.symm hi]

/-- `s² + t² = -1` is solvable in every finite field. -/
theorem exists_sq_add_sq_eq_neg_one [Finite K] : ∃ s t : K, s ^ 2 + t ^ 2 = -1 := by
  set p := ringChar K
  have : CharP K p := ringChar.charP K
  have hp : p.Prime := (CharP.char_is_prime_or_zero K p).resolve_right
    (CharP.char_ne_zero_of_finite K p)
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, b, hab⟩ := ZMod.sq_add_sq p (-1)
  refine ⟨ZMod.castHom (dvd_refl p) K a, ZMod.castHom (dvd_refl p) K b, ?_⟩
  have hab' : a ^ 2 + b ^ 2 + 1 = 0 := by rw [hab]; exact neg_add_cancel 1
  have := congrArg (ZMod.castHom (dvd_refl p) K) hab'
  rw [map_add, map_add, map_pow, map_pow, map_one, map_zero] at this
  linear_combination this

/-- **The quaternion group in the point stabilizer of `PSp₄(q)`, `q` odd.** -/
theorem isGood_stabilizer_basePt_two [Finite K] (hK : (-1 : K) ≠ 1) :
    IsGood (stabilizer (StatedProj (StatedSp 2 K)) (basePt 2 K (by omega))) := by
  obtain ⟨s, t, hst⟩ := exists_sq_add_sq_eq_neg_one (K := K)
  set i₀ : Fin 2 := ⟨0, by omega⟩
  set i₁ : Fin 2 := ⟨1, by omega⟩
  have h10 : i₁ ≠ i₀ := by simp [i₀, i₁, Fin.ext_iff]
  have hI : (0 : K) * 0 - 1 * (-1) = 1 := by ring
  have hJ : s * (-s) - t * t = 1 := by linear_combination -hst
  have hI2 : (0 * 0 + 1 * (-1) : K) * ((-1) * 1 + 0 * 0) - (0 * 1 + 1 * 0) * ((-1) * 0 + 0 * (-1))
      = 1 := by ring
  have hm' : (-1 : K) * (-1) - 0 * 0 = 1 := by ring
  have hP1 : t * (-t) - (-s) * (-s) = 1 := by linear_combination -hst
  set I := planeSp i₁ (0 : K) 1 (-1) 0 hI
  set J := planeSp i₁ s t t (-s) hJ
  set m := planeSp i₁ (-1 : K) 0 0 (-1) hm'
  have hII : I * I = m := by
    rw [planeSp_mul i₁ hI hI hI2]; exact planeSp_congr i₁ _ _ (by ring) (by ring) (by ring) (by ring)
  have hmm : m * m = 1 := by
    rw [planeSp_mul i₁ hm' hm' (by ring), ← planeSp_one i₁ (by ring)]
    exact planeSp_congr i₁ _ _ (by ring) (by ring) (by ring) (by ring)
  have hJJ : J * J = m := by
    rw [planeSp_mul i₁ hJ hJ (by linear_combination (s ^ 2 + t ^ 2 - 1) * hst)]
    exact planeSp_congr i₁ _ _ (by linear_combination hst) (by ring) (by ring)
      (by linear_combination hst)
  have hIJ1 : I * J = planeSp i₁ t (-s) (-s) (-t) hP1 := by
    rw [planeSp_mul i₁ hI hJ (by linear_combination -hst)]
    exact planeSp_congr i₁ _ _ (by ring) (by ring) (by ring) (by ring)
  have hIJ : I * J * I = J := by
    rw [hIJ1, planeSp_mul i₁ hP1 hI (by linear_combination -hst)]
    exact planeSp_congr i₁ _ _ (by ring) (by ring) (by ring) (by ring)
  set I' : StatedProj (StatedSp 2 K) := QuotientGroup.mk I
  set J' : StatedProj (StatedSp 2 K) := QuotientGroup.mk J
  have hsq : I' ^ 2 = (m : StatedProj (StatedSp 2 K)) := by
    rw [_root_.sq, ← QuotientGroup.mk_mul, hII]
  have hm1 : (m : StatedProj (StatedSp 2 K)) ≠ 1 := by
    refine mk_ne_one_of_diag_ne m (a := .inl i₁) (b := .inl i₀) ?_
    rw [coe_planeSp_apply, coe_planeSp_apply, planeLin_inl,
      planeLin_other _ _ _ _ _ _ (by simp [Ne.symm h10]) (by simp)]
    simpa [Pi.single_apply, h10] using hK
  refine Subgroup.isGood_of_quaternion' _ (I := I') (J := J')
    (planeSp_smul_basePt (by omega) i₁ h10 _ _ _ _ hI)
    (planeSp_smul_basePt (by omega) i₁ h10 _ _ _ _ hJ) ?_ (by rw [hsq]; exact hm1) ?_ ?_
  · rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hsq, _root_.sq, ← QuotientGroup.mk_mul, hmm,
      QuotientGroup.mk_one]
  · rw [hsq, _root_.sq, ← QuotientGroup.mk_mul, hJJ]
  · -- `I J = J I⁻¹` from `I J I = J`
    rw [eq_mul_inv_iff_mul_eq, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hIJ]

end CFSGOutside.HallPaige.Symplectic

namespace CFSGOutside.HallPaige

open Symplectic Corpus.Lie TauCeti

section
variable [h0 : Corpus.Lie.SymplecticEquivs]
include h0

/-- **Hall–Paige for `B_2(q)`, `q` odd**: the minimal-counterexample step. -/
theorem catalogueCase_B2_odd (q : PrimePower) (hv : (LieTypeIndex.B 2 q).Valid) (hq : q.p ≠ 2) :
    CatalogueCase (.lie ⟨.B 2 q, hv⟩) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  intro hG hP
  obtain ⟨e⟩ := Corpus.Lie.SymplecticEquivs.nonempty_mulEquiv_lie_B2_of_statedProj hv (card_galoisField_primePower q)
  have hodd : Odd (Nat.card (GaloisField q.p q.exponent)) := by
    rw [card_galoisField_primePower, PrimePower.card]
    exact (q.prime_p.odd_of_ne_two hq).pow
  refine HasCompleteMapping.of_mulEquiv e (hasCompleteMapping_of_wilcoxCriterion cosetStatement
    (wilcoxCriterion_PSp le_rfl ?_) (ProperSubgroupsAdmissible.of_mulEquiv e.symm hP))
  exact isGood_stabilizer_basePt_two (neg_one_ne_one_of_odd_card hodd)

end

end CFSGOutside.HallPaige
