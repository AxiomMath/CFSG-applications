import Mathlib

/-!
# A mod-p spanning lemma

Let a group `P` act transitively on a finite set `X` so that every element acts with order a power of
the prime `p`. If a family of integer vectors on `X` is stable under the action and one of its members
has coordinate sum prime to `p`, then the family spans `X → ℂ` over `ℂ`.

(Used in Gagola 1974, proof of Theorem 3.5: the permutation module `𝔽_p[X]` of a transitive `p`-group
has the augmentation submodule as its unique maximal submodule.)
-/

namespace CFSGOutside.Gagola

open scoped BigOperators
open Classical

noncomputable section

theorem exists_ne_zero_ann {K : Type*} [Field K] {X : Type*} [Fintype X]
    (W : Submodule K (X → K)) (hne : W ≠ ⊤) :
    ∃ c : X → K, c ≠ 0 ∧ ∀ w ∈ W, ∑ x, c x * w x = 0 := by
  have hlt : W < ⊤ := lt_top_iff_ne_top.2 hne
  have hproj : Module.Projective K ((X → K) ⧸ W) := inferInstance
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hlt hproj
  have hexp : ∀ v : X → K,
      f v = ∑ x, (f fun j => if x = j then 1 else 0) * v x := by
    intro v
    rw [LinearMap.pi_apply_eq_sum_univ f v]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [smul_eq_mul, mul_comm]
  refine ⟨fun x => f fun j => if x = j then 1 else 0, ?_, ?_⟩
  · intro h
    apply hf0
    refine LinearMap.ext fun v => ?_
    rw [hexp v]
    have hc : ∀ x, (f fun j => if x = j then 1 else 0) = 0 := fun x => congrFun h x
    simp [hc]
  · intro w hw
    have h1 : f w = 0 := by
      have h2 : f w ∈ Submodule.map f W := Submodule.mem_map_of_mem hw
      rw [hf, Submodule.mem_bot] at h2
      exact h2
    rw [← hexp w]
    exact h1

theorem eq_top_of_modp {p : ℕ} [hp : Fact p.Prime] {K : Type*} [Field K] [Fintype K]
    (hK : p ∣ Fintype.card K) {Q X : Type*} [Group Q] [MulAction Q X]
    [Fintype X] [MulAction.IsPretransitive Q X] (hQ : IsPGroup p Q)
    (W : Submodule K (X → K))
    (hW : ∀ (g : Q) (v : X → K), v ∈ W → (fun x => v (g⁻¹ • x)) ∈ W)
    (hsum : ∃ w ∈ W, ∑ x, w x ≠ 0) : W = ⊤ := by
  by_contra hne
  obtain ⟨c0, hc0, hc0S⟩ := exists_ne_zero_ann W hne
  let S : Submodule K (X → K) :=
    { carrier := {c | ∀ w ∈ W, ∑ x, c x * w x = 0}
      add_mem' := by
        intro a b ha hb w hw
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, ha w hw, hb w hw, add_zero]
      zero_mem' := by intro w hw; simp
      smul_mem' := by
        intro r a ha w hw
        simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, ha w hw, mul_zero] }
  have hSstab : ∀ (g : Q) (c : X → K), c ∈ S → (fun x => c (g⁻¹ • x)) ∈ S := by
    intro g c hc w hw
    have h1 := hc _ (hW g⁻¹ w hw)
    rw [← h1]
    simp only [inv_inv]
    calc ∑ x, c (g⁻¹ • x) * w x = ∑ x, c (g⁻¹ • g • x) * w (g • x) :=
          (Equiv.sum_comp (MulAction.toPerm g) (fun y => c (g⁻¹ • y) * w y)).symm
      _ = ∑ x, c x * w (g • x) := by simp
  letI : MulAction Q S :=
    { smul := fun g c => ⟨fun x => c.1 (g⁻¹ • x), hSstab g c.1 c.2⟩
      one_smul := by
        intro c; apply Subtype.ext; funext x
        show c.1 ((1 : Q)⁻¹ • x) = c.1 x
        simp
      mul_smul := by
        intro g h c; apply Subtype.ext; funext x
        show c.1 ((g * h)⁻¹ • x) = c.1 (h⁻¹ • g⁻¹ • x)
        simp [mul_smul] }
  haveI : Fintype S := Fintype.ofFinite S
  have hmod := hQ.card_modEq_card_fixedPoints S
  haveI hSnt : Nontrivial S :=
    ⟨⟨⟨c0, hc0S⟩, 0, fun h => hc0 (congrArg Subtype.val h)⟩⟩
  have hpS : p ∣ Nat.card S := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := K) (V := S)]
    exact dvd_pow hK (Module.finrank_pos (R := K) (M := S)).ne'
  have hfp : p ∣ Nat.card (MulAction.fixedPoints Q S) :=
    Nat.modEq_zero_iff_dvd.1 (hmod.symm.trans (Nat.modEq_zero_iff_dvd.2 hpS))
  let z : MulAction.fixedPoints Q S :=
    ⟨0, MulAction.mem_fixedPoints.2 fun g => by
      apply Subtype.ext; funext x; rfl⟩
  haveI : Nonempty (MulAction.fixedPoints Q S) := ⟨z⟩
  have hpos : 0 < Nat.card (MulAction.fixedPoints Q S) := Nat.card_pos
  have hge : p ≤ Nat.card (MulAction.fixedPoints Q S) := Nat.le_of_dvd hpos hfp
  have hnt : Nontrivial (MulAction.fixedPoints Q S) :=
    Finite.one_lt_card_iff_nontrivial.1 (lt_of_lt_of_le hp.out.one_lt hge)
  obtain ⟨y, hy⟩ := exists_ne z
  have hinv : ∀ (g : Q) x, y.1.1 (g • x) = y.1.1 x := by
    intro g x
    have h1 : (g⁻¹ • y.1).1 x = y.1.1 x := by
      rw [MulAction.mem_fixedPoints.1 y.2 g⁻¹]
    have h2 : y.1.1 (g⁻¹⁻¹ • x) = y.1.1 x := h1
    simpa using h2
  have hy0 : y.1.1 ≠ 0 := fun h => hy (Subtype.ext (Subtype.ext h))
  obtain ⟨x0, hx0⟩ : ∃ x0, y.1.1 x0 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hy0 (funext hcon)
  have hconst : ∀ x, y.1.1 x = y.1.1 x0 := by
    intro x
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Q x0 x
    rw [← hg, hinv]
  obtain ⟨w, hw, hws⟩ := hsum
  have h3 : ∑ x, y.1.1 x * w x = y.1.1 x0 * ∑ x, w x := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by rw [hconst x]
  have h4 := y.1.2 w hw
  rw [h3] at h4
  rcases mul_eq_zero.1 h4 with h | h
  · exact hx0 h
  · exact hws h

theorem span_eq_top_of_modp {p : ℕ} [hp : Fact p.Prime] {P X ι : Type*} [Group P] [MulAction P X]
    [Fintype X] [Fintype ι] [MulAction.IsPretransitive P X]
    (hP : ∀ g : P, ∃ k : ℕ, ∀ x : X, (g ^ p ^ k) • x = x)
    (t : ι → X → ℤ)
    (hstab : ∀ (g : P) (i : ι), ∃ j : ι, ∀ x : X, t j x = t i (g⁻¹ • x))
    (hsum : ∃ i : ι, ¬ (p : ℤ) ∣ ∑ x, t i x) :
    Submodule.span ℂ (Set.range fun i : ι => fun x : X => (t i x : ℂ)) = ⊤ := by
  let tb : ι → X → ZMod p := fun i x => (t i x : ZMod p)
  let W : Submodule (ZMod p) (X → ZMod p) := Submodule.span (ZMod p) (Set.range tb)
  have hWP : ∀ (g : P) (v : X → ZMod p), v ∈ W → (fun x => v (g⁻¹ • x)) ∈ W := by
    intro g v hv
    let L : (X → ZMod p) →ₗ[ZMod p] (X → ZMod p) :=
      LinearMap.funLeft (ZMod p) (ZMod p) (fun x => g⁻¹ • x)
    have hle : W ≤ Submodule.comap L W := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      obtain ⟨j, hj⟩ := hstab g i
      have hLj : L (tb i) = tb j := by
        funext x
        simp [L, tb, hj x]
      show L (tb i) ∈ W
      rw [hLj]
      exact Submodule.subset_span ⟨j, rfl⟩
    exact hle hv
  let Q := (MulAction.toPermHom P X).range
  have hQp : IsPGroup p Q := by
    intro q
    obtain ⟨g, hg⟩ := q.2
    obtain ⟨k, hk⟩ := hP g
    refine ⟨k, ?_⟩
    apply Subtype.ext
    apply Equiv.ext
    intro x
    show (q.1 ^ p ^ k) x = x
    rw [← hg, ← map_pow]
    exact hk x
  haveI : MulAction.IsPretransitive Q X :=
    ⟨fun x y => by
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq P x y
      exact ⟨⟨MulAction.toPermHom P X g, g, rfl⟩, hg⟩⟩
  have hWQ : ∀ (q : Q) (v : X → ZMod p), v ∈ W → (fun x => v (q⁻¹ • x)) ∈ W := by
    intro q v hv
    obtain ⟨g, hg⟩ := q.2
    have hx : ∀ x : X, q⁻¹ • x = g⁻¹ • x := by
      intro x
      show (q⁻¹ : Q).1 x = _
      rw [Subgroup.coe_inv, ← hg]
      simp [map_inv]
    have e : (fun x => v (q⁻¹ • x)) = fun x => v (g⁻¹ • x) := funext fun x => by rw [hx x]
    rw [e]
    exact hWP g v hv
  obtain ⟨i0, hi0⟩ := hsum
  have hsum' : ∃ w ∈ W, ∑ x, w x ≠ 0 := by
    refine ⟨tb i0, Submodule.subset_span ⟨i0, rfl⟩, ?_⟩
    intro h
    apply hi0
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    exact h
  have hWtop : W = ⊤ :=
    eq_top_of_modp (K := ZMod p) (by rw [ZMod.card]) hQp W hWQ hsum'
  have hex : ∀ x, ∃ a : ι → ZMod p, ∑ i, a i • tb i = Pi.single x 1 := by
    intro x
    have hmem : (Pi.single x 1 : X → ZMod p) ∈ W := by rw [hWtop]; trivial
    exact (Submodule.mem_span_range_iff_exists_fun (ZMod p)).1 hmem
  choose a ha using hex
  let A : X → ι → ℤ := fun x i => ((a x i).val : ℤ)
  let M : Matrix X X ℤ := fun x y => ∑ i, A x i * t i y
  have hM : (Int.castRingHom (ZMod p)).mapMatrix M = 1 := by
    ext x y
    have h1 := congrFun (ha x) y
    have h2 : ((M x y : ℤ) : ZMod p) = (Pi.single x 1 : X → ZMod p) y := by
      rw [← h1]
      simp [M, A, tb, Finset.sum_apply]
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, eq_intCast, Matrix.one_apply]
    rw [h2, Pi.single_apply]
    by_cases hxy : x = y
    · simp [hxy]
    · simp [hxy, Ne.symm hxy]
  have hdet : (M.det : ZMod p) = 1 := by
    have h := RingHom.map_det (Int.castRingHom (ZMod p)) M
    rw [hM, Matrix.det_one] at h
    simpa using h
  have hdet0 : M.det ≠ 0 := fun h => by rw [h] at hdet; simp at hdet
  let N : Matrix X X ℂ := (Int.castRingHom ℂ).mapMatrix M
  have hNdet : N.det = (M.det : ℂ) := by
    have h := RingHom.map_det (Int.castRingHom ℂ) M
    rw [eq_intCast] at h
    exact h.symm
  have hN : IsUnit N.det := by
    rw [hNdet]
    exact isUnit_iff_ne_zero.2 (by exact_mod_cast hdet0)
  have hNu : IsUnit N := (Matrix.isUnit_iff_isUnit_det N).2 hN
  have hrow : ∀ x, (fun y => N x y) ∈
      Submodule.span ℂ (Set.range fun i : ι => fun x : X => (t i x : ℂ)) := by
    intro x
    have : (fun y => N x y) = ∑ i, (A x i : ℂ) • (fun y : X => (t i y : ℂ)) := by
      funext y
      have hNxy : N x y = ∑ i, (A x i : ℂ) * (t i y : ℂ) := by
        have h0 : N x y = ((M x y : ℤ) : ℂ) := rfl
        rw [h0]
        simp only [M]
        push_cast
        rfl
      rw [hNxy]
      simp [Finset.sum_apply]
    rw [this]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  rw [eq_top_iff]
  intro v _
  have hv : v = Matrix.vecMul (Matrix.vecMul v N⁻¹) N := by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hN, Matrix.vecMul_one]
  rw [hv]
  have hsumrow : Matrix.vecMul (Matrix.vecMul v N⁻¹) N =
      ∑ x, (Matrix.vecMul v N⁻¹) x • (fun y => N x y) := by
    funext y
    simp [Matrix.vecMul, dotProduct, Finset.sum_apply]
  rw [hsumrow]
  exact Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ (hrow x)

end

end CFSGOutside.Gagola
