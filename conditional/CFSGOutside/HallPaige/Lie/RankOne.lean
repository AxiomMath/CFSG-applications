import CFSGOutside.HallPaige.Cosets
import CFSGOutside.HallPaige.Lie.Basic
import CFSGOutside.HallPaige.Lie.Good
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.ZMod.Basic

/-!
# Rank-one groups with a torus of even order (Wilcox, Lemmas 21–23)

Let `G` be a finite group with subgroups `U` (of odd order) and `T` normalizing `U`, and an
element `n` with `n² = 1`, such that `G = B ⊔ UnB` with unique expressions (`B = TU`) and
`T n ⊆ UnUnU`. If `T` is cyclic of even order, `G` has a complete mapping
(`CFSGOutside.HallPaige.hasCompleteMapping_of_rankOne_split`). This is the argument of Wilcox, Lemmas 21–23:
Proposition 14 is applied to the left cosets of `U`, which are `tU` and `untU`; the cosets `untU`
are handled by Lemma 21 and the cosets `tU` by a near complete mapping of `T` (Lemma 22,
`CFSGOutside.HallPaige.exists_nearComplete_of_isCyclic`), with a tweak at three cosets.

No goodness of `G` and no hypothesis on proper subgroups is needed. When `|U|` is even instead,
`TU` has odd index `1 + |U|` and the rank-one criterion applies
(`CFSGOutside.HallPaige.wilcoxCriterion_of_rankOne_split_even`).
-/

namespace CFSGOutside.HallPaige

section NearComplete

/-- The index function of Wilcox's Lemma 22: `0 ↦ k`, `i ↦ i` for `0 < i < k`, `i ↦ i + 1` for
`k ≤ i < 2k` (read modulo `2k`). -/
def nearAlpha (k i : ℕ) : ℕ :=
  if i = 0 then k else if i < k then i else if i + 1 = 2 * k then 0 else i + 1

/-- `i ↦ 2i` for `i < k`, `i ↦ 2i + 1 - 2k` for `k ≤ i < 2k`. -/
def nearBeta (k i : ℕ) : ℕ :=
  if i < k then 2 * i else 2 * i + 1 - 2 * k

theorem nearAlpha_lt {k i : ℕ} (hk : 0 < k) (hi : i < 2 * k) : nearAlpha k i < 2 * k := by
  unfold nearAlpha; split_ifs <;> omega

theorem nearBeta_lt {k i : ℕ} (hi : i < 2 * k) : nearBeta k i < 2 * k := by
  unfold nearBeta; split_ifs <;> omega

theorem nearAlpha_inj {k i j : ℕ} (hi : i < 2 * k) (hj : j < 2 * k)
    (h : nearAlpha k i = nearAlpha k j) : i = j := by
  unfold nearAlpha at h; split_ifs at h <;> omega

theorem nearBeta_inj {k i j : ℕ} (hi : i < 2 * k) (hj : j < 2 * k)
    (h : nearBeta k i = nearBeta k j) : i = j := by
  unfold nearBeta at h; split_ifs at h <;> omega

theorem nearAlpha_add {k i : ℕ} (hi0 : i ≠ 0) (hi : i < 2 * k) :
    (i + nearAlpha k i) % (2 * k) = nearBeta k i := by
  have key : i + nearAlpha k i = nearBeta k i ∨ i + nearAlpha k i = nearBeta k i + 2 * k := by
    unfold nearAlpha nearBeta; split_ifs <;> omega
  have hlt := nearBeta_lt (k := k) hi
  rcases key with h | h <;> rw [h]
  · exact Nat.mod_eq_of_lt hlt
  · rw [Nat.add_mod_right]; exact Nat.mod_eq_of_lt hlt

/-- **Wilcox, Lemma 22** for `ZMod (2k)`. -/
theorem exists_nearComplete_zmod (m k : ℕ) (hm : m = 2 * k) (hk : 0 < k) :
    ∃ α β : ZMod m ≃ ZMod m, β 0 = 0 ∧ α 0 ≠ 0 ∧ ∀ c, c ≠ 0 → c + α c = β c := by
  subst hm
  haveI : NeZero (2 * k) := ⟨by omega⟩
  let fα : ZMod (2 * k) → ZMod (2 * k) := fun c => ((nearAlpha k c.val : ℕ) : ZMod (2 * k))
  let fβ : ZMod (2 * k) → ZMod (2 * k) := fun c => ((nearBeta k c.val : ℕ) : ZMod (2 * k))
  have hvα : ∀ c, (fα c).val = nearAlpha k c.val := fun c => by
    simp only [fα, ZMod.val_natCast]
    exact Nat.mod_eq_of_lt (nearAlpha_lt hk (ZMod.val_lt c))
  have hvβ : ∀ c, (fβ c).val = nearBeta k c.val := fun c => by
    simp only [fβ, ZMod.val_natCast]
    exact Nat.mod_eq_of_lt (nearBeta_lt (ZMod.val_lt c))
  have hα : Function.Injective fα := fun c c' h => by
    have := congrArg ZMod.val h
    rw [hvα, hvα] at this
    exact ZMod.val_injective _ (nearAlpha_inj (ZMod.val_lt c) (ZMod.val_lt c') this)
  have hβ : Function.Injective fβ := fun c c' h => by
    have := congrArg ZMod.val h
    rw [hvβ, hvβ] at this
    exact ZMod.val_injective _ (nearBeta_inj (ZMod.val_lt c) (ZMod.val_lt c') this)
  refine ⟨Equiv.ofBijective fα hα.bijective_of_finite,
    Equiv.ofBijective fβ hβ.bijective_of_finite, ?_, ?_, ?_⟩
  · apply ZMod.val_injective
    change (fβ 0).val = (0 : ZMod (2 * k)).val
    rw [hvβ, ZMod.val_zero]
    simp [nearBeta, hk]
  · intro h
    have := congrArg ZMod.val h
    change (fα 0).val = (0 : ZMod (2 * k)).val at this
    rw [hvα, ZMod.val_zero] at this
    simp [nearAlpha] at this
    omega
  · intro c hc
    apply ZMod.val_injective
    change (c + fα c).val = (fβ c).val
    rw [ZMod.val_add, hvα, hvβ]
    exact nearAlpha_add (fun h => hc ((ZMod.val_eq_zero c).1 h)) (ZMod.val_lt c)

/-- **Wilcox, Lemma 22.** A finite cyclic group `C` of even order has permutations `α`, `β` with
`c * α c = β c` for `c ≠ 1`, `β 1 = 1` and `α 1 ≠ 1`. -/
theorem exists_nearComplete_of_isCyclic {C : Type*} [Group C] [Finite C] (hC : IsCyclic C)
    (heven : Even (Nat.card C)) :
    ∃ α β : C ≃ C, β 1 = 1 ∧ α 1 ≠ 1 ∧ ∀ c, c ≠ 1 → c * α c = β c := by
  obtain ⟨k, hk⟩ := heven
  have hk0 : 0 < k := by
    have := Nat.card_pos (α := C)
    omega
  obtain ⟨α, β, hβ0, hα0, hαβ⟩ := exists_nearComplete_zmod (Nat.card C) k (by omega) hk0
  let e := zmodCyclicMulEquiv hC
  let toZ : C ≃ ZMod (Nat.card C) := e.symm.toEquiv.trans Multiplicative.toAdd
  refine ⟨toZ.trans (α.trans toZ.symm), toZ.trans (β.trans toZ.symm), ?_, ?_, ?_⟩
  · change e (Multiplicative.ofAdd (β (Multiplicative.toAdd (e.symm 1)))) = 1
    rw [map_one, toAdd_one, hβ0, ofAdd_zero, map_one]
  · change e (Multiplicative.ofAdd (α (Multiplicative.toAdd (e.symm 1)))) ≠ 1
    rw [map_one, toAdd_one, Ne, ← map_one e, e.injective.eq_iff]
    exact hα0
  · intro c hc
    change c * e (Multiplicative.ofAdd (α (Multiplicative.toAdd (e.symm c)))) =
      e (Multiplicative.ofAdd (β (Multiplicative.toAdd (e.symm c))))
    have hc' : Multiplicative.toAdd (e.symm c) ≠ 0 := by
      intro h
      apply hc
      have : e.symm c = 1 := by
        rw [← ofAdd_toAdd (e.symm c), h, ofAdd_zero]
      simpa using congrArg e this
    rw [← hαβ _ hc', ofAdd_add, ofAdd_toAdd, map_mul, MulEquiv.apply_symm_apply]

end NearComplete

section Split

universe u

variable {G : Type u} [Group G]

/-- The set `TU`, a subgroup when `T` normalizes `U`. -/
def borelOf (U T : Subgroup G) (hTU : ∀ t ∈ T, ∀ u ∈ U, t * u * t⁻¹ ∈ U) : Subgroup G where
  carrier := {g | ∃ t ∈ T, ∃ u ∈ U, g = t * u}
  mul_mem' := by
    rintro _ _ ⟨t, ht, u, hu, rfl⟩ ⟨t', ht', u', hu', rfl⟩
    refine ⟨t * t', T.mul_mem ht ht', t'⁻¹ * u * t' * u', U.mul_mem ?_ hu', by group⟩
    simpa using hTU t'⁻¹ (T.inv_mem ht') u hu
  one_mem' := ⟨1, T.one_mem, 1, U.one_mem, by simp⟩
  inv_mem' := by
    rintro _ ⟨t, ht, u, hu, rfl⟩
    refine ⟨t⁻¹, T.inv_mem ht, t * u⁻¹ * t⁻¹, hTU t ht _ (U.inv_mem hu), by group⟩

variable (U T : Subgroup G) (hTU : ∀ t ∈ T, ∀ u ∈ U, t * u * t⁻¹ ∈ U)

theorem le_borelOf_left : T ≤ borelOf U T hTU := fun t ht => ⟨t, ht, 1, U.one_mem, by simp⟩

theorem le_borelOf_right : U ≤ borelOf U T hTU := fun u hu => ⟨1, T.one_mem, u, hu, by simp⟩

/-- The coset map `T ⊕ (T × U) → G ⧸ U`, `t ↦ tU`, `(t, u) ↦ untU`. -/
def rankOneCosetMap (n : G) : T ⊕ (T × U) → G ⧸ U
  | .inl t => ((t : G) : G ⧸ U)
  | .inr (t, u) => (((u : G) * n * t : G) : G ⧸ U)

variable {U T hTU}

omit hTU in
theorem coset_eq_of_mem {g w : G} (hw : w ∈ U) : ((g * w : G) : G ⧸ U) = (g : G ⧸ U) := by
  rw [QuotientGroup.eq]
  simpa using U.inv_mem hw

/-- With unique Bruhat expressions, the coset map is a bijection. -/
theorem rankOneCosetMap_bijective [Finite G] (n : G) (hn2 : n * n = 1)
    (hUT : ∀ u ∈ U, u ∈ T → u = 1) (hnB : n ∉ borelOf U T hTU)
    (hV : ∀ u ∈ U, n * u * n ∈ borelOf U T hTU → u = 1)
    (hcover : ∀ g : G, g ∈ borelOf U T hTU ∨ ∃ u ∈ U, ∃ t ∈ T, ∃ u' ∈ U, g = u * n * t * u') :
    Function.Bijective (rankOneCosetMap U T n) := by
  have hninv : n⁻¹ = n := inv_eq_of_mul_eq_one_right hn2
  have hT := le_borelOf_left U T hTU
  have hU := le_borelOf_right U T hTU
  constructor
  · rintro (t | ⟨t, u⟩) (t' | ⟨t', u'⟩) h <;> simp only [rankOneCosetMap, QuotientGroup.eq] at h
    · congr 1
      have h1 := hUT _ h (T.mul_mem (T.inv_mem t.2) t'.2)
      exact Subtype.ext (by simpa [inv_mul_eq_one] using h1)
    · exfalso
      apply hnB
      have : n = (u' : G)⁻¹ * t * ((t : G)⁻¹ * (u' * n * t')) * (t' : G)⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hU (U.inv_mem u'.2))
        (hT t.2)) (hU h)) (hT (T.inv_mem t'.2))
    · exfalso
      apply hnB
      have : n = (u : G)⁻¹ * t' * ((u * n * t)⁻¹ * t')⁻¹ * (t : G)⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hU (U.inv_mem u.2))
        (hT t'.2)) (hU (U.inv_mem h))) (hT (T.inv_mem t.2))
    · have hu : (u : G)⁻¹ * u' = 1 := by
        refine hV _ (U.mul_mem (U.inv_mem u.2) u'.2) ?_
        have : n * ((u : G)⁻¹ * u') * n =
            (t : G) * ((u * n * t)⁻¹ * (u' * n * t')) * (t' : G)⁻¹ := by
          rw [show (t : G) * ((u * n * t)⁻¹ * (u' * n * t')) * (t' : G)⁻¹ =
            n⁻¹ * ((u : G)⁻¹ * u') * n by group, hninv]
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hT t.2) (hU h)) (hT (T.inv_mem t'.2))
      have huu : u = u' := Subtype.ext (by rw [← inv_mul_eq_one]; exact hu)
      subst huu
      have ht : (t : G)⁻¹ * t' ∈ U := by
        have : (t : G)⁻¹ * t' = ((u * n * t)⁻¹ * (u * n * t')) := by
          group
        rw [this]; exact h
      have h1 := hUT _ ht (T.mul_mem (T.inv_mem t.2) t'.2)
      have htt : t = t' := Subtype.ext (by simpa [inv_mul_eq_one] using h1)
      rw [htt]
  · intro c
    induction c using QuotientGroup.induction_on with
    | H g =>
      rcases hcover g with ⟨t, ht, u, hu, rfl⟩ | ⟨u, hu, t, ht, u', hu', rfl⟩
      · exact ⟨.inl ⟨t, ht⟩, (coset_eq_of_mem hu).symm⟩
      · exact ⟨.inr (⟨t, ht⟩, ⟨u, hu⟩), (coset_eq_of_mem hu').symm⟩

/-- **Wilcox, Lemma 21** (the case used). If `t n ∈ UnUnU`, then `nt ∈ v n t U n t U` for some
`v ∈ U`. -/
theorem exists_mul_of_mem_UnUnU {n t a b c : G} (hn2 : n * n = 1)
    (h : t * n = a * n * b * n * c) :
    n * t = b⁻¹ * n * t * (t⁻¹ * a⁻¹ * t) * n * t * (t⁻¹ * c⁻¹ * t) := by
  have e1 : b⁻¹ * n * t * (t⁻¹ * a⁻¹ * t) * n * t * (t⁻¹ * c⁻¹ * t) =
      b⁻¹ * n * a⁻¹ * (t * n) * c⁻¹ * t := by group
  rw [e1, h]
  have e2 : b⁻¹ * n * a⁻¹ * (a * n * b * n * c) * c⁻¹ * t = b⁻¹ * (n * n) * b * n * t := by group
  rw [e2, hn2]
  group

/-- **Wilcox, Lemma 23** (abstract form). Let `U`, `T ≤ G` with `U` of odd order, `T` cyclic of
even order normalizing `U`, `U ∩ T = 1`, and let `n` satisfy `n² = 1`, such that
`G = TU ⊔ UnTU` with unique expressions (`n ∉ TU`, `nUn ∩ TU = 1`) and `tn ∈ UnUnU` for every
`t ∈ T`. Then `G` has a complete mapping. -/
theorem hasCompleteMapping_of_rankOne_split [Finite G] (n : G) (hUodd : Odd (Nat.card U))
    (hn2 : n * n = 1)
    (hUT : ∀ u ∈ U, u ∈ T → u = 1) (hnB : n ∉ borelOf U T hTU)
    (hV : ∀ u ∈ U, n * u * n ∈ borelOf U T hTU → u = 1)
    (hcover : ∀ g : G, g ∈ borelOf U T hTU ∨ ∃ u ∈ U, ∃ t ∈ T, ∃ u' ∈ U, g = u * n * t * u')
    (hTn : ∀ t ∈ T, ∃ a ∈ U, ∃ b ∈ U, ∃ c ∈ U, t * n = a * n * b * n * c)
    (hcyc : IsCyclic T) (heven : Even (Nat.card T)) : HasCompleteMapping G := by
  classical
  have hUcm : HasCompleteMapping U := hasCompleteMapping_of_odd hUodd
  -- the coset bijection
  let Φ : T ⊕ (T × U) ≃ G ⧸ U := Equiv.ofBijective _
    (rankOneCosetMap_bijective (hTU := hTU) n hn2 hUT hnB hV hcover)
  have hΦl : ∀ t : T, Φ (.inl t) = ((t : G) : G ⧸ U) := fun _ => rfl
  have hΦr : ∀ (t : T) (u : U), Φ (.inr (t, u)) = (((u : G) * n * t : G) : G ⧸ U) :=
    fun _ _ => rfl
  -- the elements `v t` of Lemma 21
  have hv : ∀ t : T, ∃ v w w' : U, n * t = v * n * t * w * n * t * w' := by
    intro t
    obtain ⟨a, ha, b, hb, c, hc, h⟩ := hTn t t.2
    refine ⟨⟨b⁻¹, U.inv_mem hb⟩, ⟨(t : G)⁻¹ * a⁻¹ * t, ?_⟩, ⟨(t : G)⁻¹ * c⁻¹ * t, ?_⟩,
      exists_mul_of_mem_UnUnU hn2 h⟩
    · simpa using hTU _ (T.inv_mem t.2) _ (U.inv_mem ha)
    · simpa using hTU _ (T.inv_mem t.2) _ (U.inv_mem hc)
  choose v w w' hvw using hv
  -- the near complete mapping of `T`
  obtain ⟨α, β, hβ1, hα1, hαβ⟩ := exists_nearComplete_of_isCyclic hcyc heven
  set ζ : T := (α 1)⁻¹ with hζ
  have hζ1 : ζ ≠ 1 := by rw [hζ, Ne, inv_eq_one]; exact hα1
  -- permutations of the index set
  let σx : T ⊕ (T × U) ≃ T ⊕ (T × U) :=
    Equiv.sumCongr (Equiv.refl _) (Equiv.prodShear (Equiv.refl _) fun t => Equiv.mulRight (v t))
  let σy : T ⊕ (T × U) ≃ T ⊕ (T × U) := Equiv.sumCongr α (Equiv.refl _)
  let σz : T ⊕ (T × U) ≃ T ⊕ (T × U) := Equiv.sumCongr β (Equiv.refl _)
  let i₀ : T ⊕ (T × U) := .inl 1
  let i₁ : T ⊕ (T × U) := .inr (1, v ζ)
  let i₂ : T ⊕ (T × U) := .inr (ζ, 1)
  have h01 : i₀ ≠ i₁ := Sum.inl_ne_inr
  have h02 : i₀ ≠ i₂ := Sum.inl_ne_inr
  have h12 : i₁ ≠ i₂ := fun h => hζ1 (congrArg Prod.fst (Sum.inr_injective h)).symm
  let cyc : T ⊕ (T × U) ≃ T ⊕ (T × U) := (Equiv.swap i₀ i₁).trans (Equiv.swap i₀ i₂)
  let x := (cyc.trans σx).trans Φ
  let y := ((Equiv.swap i₀ i₁).trans σy).trans Φ
  let z := σz.trans Φ
  refine hasCompleteMapping_of_cosets U hUcm x y z fun i => ?_
  have hx : ∀ i, x i = Φ (σx (cyc i)) := fun _ => rfl
  have hy : ∀ i, y i = Φ (σy (Equiv.swap i₀ i₁ i)) := fun _ => rfl
  have hz : ∀ i, z i = Φ (σz i) := fun _ => rfl
  rw [hx, hy, hz]
  by_cases hi0 : i = i₀
  · subst hi0
    have hc : cyc i₀ = i₁ := by
      simp only [cyc, Equiv.trans_apply, Equiv.swap_apply_left]
      exact Equiv.swap_apply_of_ne_of_ne h01.symm h12
    rw [hc, Equiv.swap_apply_left]
    refine ⟨(v ζ : G) * v 1 * n * (v ζ : G)⁻¹, (v ζ : G) * n, ?_, ?_, ?_⟩
    · change _ = Φ (.inr (1, v ζ * v 1))
      rw [hΦr, coset_eq_of_mem (U.inv_mem (v ζ).2)]
      simp
    · change _ = Φ (.inr (1, v ζ))
      rw [hΦr]; simp
    · change _ = Φ (.inl (β 1))
      rw [hΦl, hβ1]
      have : (v ζ : G) * v 1 * n * (v ζ : G)⁻¹ * (v ζ * n) = 1 * (v ζ * v 1) := by
        rw [one_mul, show (v ζ : G) * v 1 * n * (v ζ : G)⁻¹ * (v ζ * n) =
          (v ζ : G) * v 1 * (n * n) by group, hn2, mul_one]
      rw [this, coset_eq_of_mem (U.mul_mem (v ζ).2 (v 1).2)]
      simp
  by_cases hi1 : i = i₁
  · subst hi1
    have hc : cyc i₁ = i₂ := by
      simp only [cyc, Equiv.trans_apply, Equiv.swap_apply_right, Equiv.swap_apply_left]
    rw [hc, Equiv.swap_apply_right]
    refine ⟨(v ζ : G) * n * ζ, α 1, ?_, ?_, ?_⟩
    · change _ = Φ (.inr (ζ, 1 * v ζ))
      rw [hΦr]; simp
    · change _ = Φ (.inl (α 1))
      rw [hΦl]
    · change _ = Φ (.inr (1, v ζ))
      rw [hΦr]
      congr 1
      rw [hζ]
      simp [mul_assoc]
  by_cases hi2 : i = i₂
  · subst hi2
    have hc : cyc i₂ = i₀ := by
      simp only [cyc, Equiv.trans_apply]
      rw [Equiv.swap_apply_of_ne_of_ne h02.symm h12.symm, Equiv.swap_apply_right]
    rw [hc, Equiv.swap_apply_of_ne_of_ne h02.symm h12.symm]
    refine ⟨1, n * ζ, ?_, ?_, ?_⟩
    · change _ = Φ (.inl 1)
      rw [hΦl]; simp
    · change _ = Φ (.inr (ζ, 1))
      rw [hΦr]; simp
    · change _ = Φ (.inr (ζ, 1))
      rw [hΦr]; simp
  -- generic indices
  have hc : cyc i = i := by
    simp only [cyc, Equiv.trans_apply]
    rw [Equiv.swap_apply_of_ne_of_ne hi0 hi1, Equiv.swap_apply_of_ne_of_ne hi0 hi2]
  rw [hc, Equiv.swap_apply_of_ne_of_ne hi0 hi1]
  rcases i with t | ⟨t, u⟩
  · have ht1 : t ≠ 1 := fun h => hi0 (by rw [h])
    refine ⟨t, α t, ?_, ?_, ?_⟩
    · change _ = Φ (.inl t)
      rw [hΦl]
    · change _ = Φ (.inl (α t))
      rw [hΦl]
    · change _ = Φ (.inl (β t))
      rw [hΦl, ← hαβ t ht1]
      rfl
  · refine ⟨(u : G) * v t * n * t * w t * (u : G)⁻¹, (u : G) * n * t * w' t, ?_, ?_, ?_⟩
    · change _ = Φ (.inr (t, u * v t))
      rw [hΦr, show (u : G) * v t * n * t * w t * (u : G)⁻¹ =
        (u : G) * v t * n * t * (w t * (u : G)⁻¹) by group,
        coset_eq_of_mem (U.mul_mem (w t).2 (U.inv_mem u.2))]
      simp [mul_assoc]
    · change _ = Φ (.inr (t, u))
      rw [hΦr, coset_eq_of_mem (w' t).2]
    · change _ = Φ (.inr (t, u))
      rw [hΦr]
      congr 1
      conv_rhs => rw [mul_assoc, hvw t]
      group

/-- `|TU| = |T| |U|` when `U ∩ T = 1`. -/
theorem card_borelOf (hUT : ∀ u ∈ U, u ∈ T → u = 1) :
    Nat.card (borelOf U T hTU) = Nat.card T * Nat.card U := by
  rw [← Nat.card_prod]
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun p : T × U => (⟨p.1 * p.2, p.1, p.1.2, p.2, p.2.2,
    rfl⟩ : borelOf U T hTU)) ⟨?_, ?_⟩)
  · rintro ⟨t, u⟩ ⟨t', u'⟩ h
    have h' : (t : G) * u = t' * u' := congrArg Subtype.val h
    have h1 : (t' : G)⁻¹ * t = u' * (u : G)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h', mul_inv_cancel_right]
    have hU' : (t' : G)⁻¹ * t ∈ U := by rw [h1]; exact U.mul_mem u'.2 (U.inv_mem u.2)
    have h2 := hUT _ hU' (T.mul_mem (T.inv_mem t'.2) t.2)
    have ht : t = t' := Subtype.ext (by rw [inv_mul_eq_one] at h2; exact h2.symm)
    subst ht
    have hu : u = u' := Subtype.ext (mul_left_cancel h')
    rw [hu]
  · rintro ⟨g, t, ht, u, hu, rfl⟩
    exact ⟨(⟨t, ht⟩, ⟨u, hu⟩), rfl⟩

/-- `[G : TU] = 1 + |U|` for a rank-one split structure. -/
theorem index_borelOf [Finite G] (n : G) (hn2 : n * n = 1)
    (hUT : ∀ u ∈ U, u ∈ T → u = 1) (hnB : n ∉ borelOf U T hTU)
    (hV : ∀ u ∈ U, n * u * n ∈ borelOf U T hTU → u = 1)
    (hcover : ∀ g : G, g ∈ borelOf U T hTU ∨ ∃ u ∈ U, ∃ t ∈ T, ∃ u' ∈ U, g = u * n * t * u') :
    (borelOf U T hTU).index = 1 + Nat.card U := by
  have h1 : Nat.card G = Nat.card (G ⧸ U) * Nat.card U :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup U
  have h2 : Nat.card (G ⧸ U) = Nat.card T + Nat.card T * Nat.card U := by
    rw [← Nat.card_congr (Equiv.ofBijective _
      (rankOneCosetMap_bijective (hTU := hTU) n hn2 hUT hnB hV hcover)), Nat.card_sum,
      Nat.card_prod]
  have h3 := (borelOf U T hTU).index_mul_card
  rw [card_borelOf hUT, h1, h2] at h3
  have hpos : 0 < Nat.card T * Nat.card U := Nat.mul_pos Nat.card_pos Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h3]
  ring

/-- **Rank one, `|U|` even** (e.g. characteristic two): `TU` has odd index, hence is good, and
the rank-one criterion applies. -/
theorem wilcoxCriterion_of_rankOne_split_even [Finite G] (hG : IsGood G) (n : G)
    (hUeven : Even (Nat.card U)) (hn2 : n * n = 1)
    (hUT : ∀ u ∈ U, u ∈ T → u = 1) (hnB : n ∉ borelOf U T hTU)
    (hV : ∀ u ∈ U, n * u * n ∈ borelOf U T hTU → u = 1)
    (hcover : ∀ g : G, g ∈ borelOf U T hTU ∨ ∃ u ∈ U, ∃ t ∈ T, ∃ u' ∈ U, g = u * n * t * u') :
    WilcoxCriterion G := by
  have hU := le_borelOf_right U T hTU
  have hT := le_borelOf_left U T hTU
  obtain ⟨u₀, hu₀, hu₀1⟩ : ∃ u ∈ U, u ≠ 1 := by
    by_contra h
    push Not at h
    have : U = ⊥ := (Subgroup.eq_bot_iff_forall U).2 h
    rw [this, Subgroup.card_bot] at hUeven
    exact Nat.not_even_one hUeven
  refine wilcoxCriterion_of_rankOne (borelOf U T hTU) n hnB (fun g hg => ?_) u₀ (hU hu₀)
    (fun h => hu₀1 (hV u₀ hu₀ h)) (isGood_of_index_odd hG _ ?_)
  · rcases hcover g with h | ⟨u, hu, t, ht, u', hu', rfl⟩
    · exact absurd h hg
    · exact DoubleCoset.mem_doubleCoset.2 ⟨u, hU hu, t * u', Subgroup.mul_mem _ (hT ht) (hU hu'),
        by group⟩
  · rw [index_borelOf n hn2 hUT hnB hV hcover]
    exact Even.one_add hUeven

end Split

end CFSGOutside.HallPaige
