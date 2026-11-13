import CFSGOutside.HallPaige.Sporadic.Co1Data
import CFSGOutside.HallPaige.Sporadic.GoodOfKlein
import CFSGOutside.HallPaige.DoubleCosets
/-!
# The Wilcox criterion for `Co₁`

`Co₁` acts on the orbit of `v₂` in `𝔽₂²⁴` (98280 points); the point stabilizer `H ≅ Co₂` has four
orbits, the classes `cls j` of the corpus (`j < 4`), distinguished by the `Co₁`-orbit of `v₂ + y`
(`{0}`, the orbits of `v₄`, `v₃`, `v₂`). By the corpus theorem `cls_trans` these are exactly the
`H`-orbits. For each class an explicit word `a` in the two generators has `a • v₂` and
`a² • v₂` in that class, and two explicit commuting involutions lie in `H`. All the word
computations are checked by the kernel with packed `𝔽₂`-matrices (`CFSGOutside.HallPaige.Sporadic.F2Packed`).

## Main results

* `CFSGOutside.HallPaige.Co1.wilcoxCriterion_of_mulEquiv`: any group isomorphic to the native model satisfies
  `WilcoxCriterion`.
* `CFSGOutside.HallPaige.Co1.wilcoxCriterion`: `WilcoxCriterion TauCeti.SporadicName.Co1.Group`.
-/

namespace CFSGOutside.HallPaige.Co1

open CFSGOutside.Corpus.Co1 CFSGOutside.HallPaige.F2

attribute [local irreducible] decode Co1Seed1 Co1Seed2

/-! ### The vectors `v₂`, `v₃`, `v₄` and the type of a vector -/

theorem v_ne_zero (i : Fin 3) : reps i ≠ 0 := by
  have h0 : vecOf 24 0 = 0 := vecOf_zero 24
  fin_cases i
  · change v₂ ≠ 0
    rw [v₂_eq, ← h0]; exact vecOf_ne (by norm_num) (by norm_num) (by norm_num)
  · change v₃ ≠ 0
    rw [v₃_eq, ← h0]; exact vecOf_ne (by norm_num) (by norm_num) (by norm_num)
  · change v₄ ≠ 0
    rw [v₄_eq, ← h0]; exact vecOf_ne (by norm_num) (by norm_num) (by norm_num)

theorem smul_zero' (g : Co1) : g • (0 : Vec24) = 0 := by
  rw [smul_def, Matrix.mulVec_zero]

theorem smul_add' (g : Co1) (a b : Vec24) : g • (a + b) = g • a + g • b := by
  rw [smul_def, smul_def, smul_def, Matrix.mulVec_add]

theorem ne_zero_of_mem_range {i : Fin 3} {z : Vec24}
    (h : z ∈ Set.range fun g : Co1 => co1Act g (reps i)) : z ≠ 0 := by
  obtain ⟨g, rfl⟩ := h
  intro h0
  apply v_ne_zero i
  have h1 : g⁻¹ • (g • reps i) = g⁻¹ • (0 : Vec24) := congrArg (g⁻¹ • ·) h0
  rwa [inv_smul_smul, smul_zero'] at h1

section
variable [h0 : Corpus.Co1.Orbits]
include h0

/-- The class index of a vector `z`: `0` for `z = 0`, then `1`, `2`, `3` for the orbits of `v₄`,
`v₃`, `v₂` (the indexing of `tyOrbC`). -/
@[irreducible] noncomputable def typ (z : Vec24) : Fin 4 :=
  if h : z = 0 then 0 else ![3, 2, 1] (Corpus.Co1.Orbits.co1_exists_unique_orbit h).exists.choose

end

/-- `tyOrbC (![3, 2, 1] i)` is the orbit of `reps i`. -/
theorem tyOrbC_idx (i : Fin 3) :
    tyOrbC ((![3, 2, 1] : Fin 3 → Fin 4) i).val =
      Set.range fun g : Co1 => co1Act g (reps i) := by
  fin_cases i <;> rfl

section
variable [h0 : Corpus.Co1.Orbits]
include h0

theorem typ_spec (z : Vec24) : z ∈ tyOrbC (typ z).val := by
  unfold typ
  split_ifs with h
  · exact h
  · rw [tyOrbC_idx]
    exact (Corpus.Co1.Orbits.co1_exists_unique_orbit h).exists.choose_spec

end

theorem tyOrbC_one : tyOrbC 1 = Set.range fun g : Co1 => co1Act g (reps 2) := tyOrbC_idx 2

theorem tyOrbC_two : tyOrbC 2 = Set.range fun g : Co1 => co1Act g (reps 1) := tyOrbC_idx 1

theorem tyOrbC_three : tyOrbC 3 = Set.range fun g : Co1 => co1Act g (reps 0) := tyOrbC_idx 0

section
variable [h0 : Corpus.Co1.Orbits]
include h0

theorem typ_of_mem_range {z : Vec24} {i : Fin 3}
    (h : z ∈ Set.range fun g : Co1 => co1Act g (reps i)) : typ z = ![3, 2, 1] i := by
  have hz := ne_zero_of_mem_range h
  unfold typ
  simp only [hz, ↓reduceDIte]
  congr 1
  exact (Corpus.Co1.Orbits.co1_exists_unique_orbit hz).unique (Corpus.Co1.Orbits.co1_exists_unique_orbit hz).exists.choose_spec h

theorem typ_eq_of_mem {z : Vec24} {j : Fin 4} (h : z ∈ tyOrbC j.val) : typ z = j := by
  obtain ⟨j, hj⟩ := j
  interval_cases j
  · change z = 0 at h
    unfold typ
    simp only [h, ↓reduceDIte]
    rfl
  · rw [tyOrbC_one] at h
    rw [typ_of_mem_range h]
    rfl
  · rw [tyOrbC_two] at h
    rw [typ_of_mem_range h]
    rfl
  · rw [tyOrbC_three] at h
    rw [typ_of_mem_range h]
    rfl

end

theorem tyOrbC_smul (g : Co1) {j : Fin 4} {z : Vec24} (hz : z ∈ tyOrbC j.val) :
    g • z ∈ tyOrbC j.val := by
  fin_cases j
  · change z = 0 at hz
    change g • z = 0
    rw [hz, smul_zero']
  all_goals
    obtain ⟨h, rfl⟩ := hz
    exact ⟨g * h, mul_smul g h _⟩

section
variable [h0 : Corpus.Co1.Orbits]
include h0

theorem typ_smul (g : Co1) (z : Vec24) : typ (g • z) = typ z :=
  typ_eq_of_mem (tyOrbC_smul g (typ_spec z))

theorem typ_word {a w : List ℕ} {x : ℕ} {j : Fin 4} (hx : vecOf 24 x = (match j.val with
    | 1 => v₄ | 2 => v₃ | _ => v₂)) (hj : j ≠ 0) (h : wv w x = 2 ^^^ wv a 2) :
    typ (v₂ + wordE a • v₂) = j := by
  apply typ_eq_of_mem
  have hv : v₂ + wordE a • v₂ = wordE w • vecOf 24 x := by
    rw [v₂_eq, wordE_smul, wordE_smul, vecOf_add, h]
  rw [hv, hx]
  fin_cases j
  · exact absurd rfl hj
  all_goals exact ⟨wordE w, rfl⟩

end

/-! ### The criterion -/

instance : Finite Co1 :=
  Finite.of_injective (fun u : Co1 => ((u : S) : Matrix (Fin 24) (Fin 24) (ZMod 2)))
    fun _ _ h => Units.ext (Subtype.ext h)

section
variable [h0 : Corpus.Co1.Orbits]
include h0

/-- Words `a` with `a • v₂` and `a² • v₂` in the class `j`. -/
theorem exists_sq_word (j : Fin 4) :
    ∃ a : List ℕ, typ (v₂ + wordE a • v₂) = j ∧ typ (v₂ + wordE (a ++ a) • v₂) = j := by
  fin_cases j
  · have h0 : v₂ + v₂ = 0 := by rw [v₂_eq, vecOf_add, Nat.xor_self, vecOf_zero]
    have ht : typ 0 = 0 := by unfold typ; simp only [↓reduceDIte]
    refine ⟨[], ?_, ?_⟩
    · rw [show wordE [] = 1 from rfl, one_smul, h0, ht]; rfl
    · rw [show wordE ([] ++ []) = 1 from rfl, one_smul, h0, ht]; rfl
  · exact ⟨[1], typ_word (w := [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1]) v₄_eq.symm (by decide) (by decide +kernel),
      typ_word (w := [0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1]) v₄_eq.symm (by decide) (by decide +kernel)⟩
  · exact ⟨[0, 1], typ_word (w := [1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0]) v₃_eq.symm (by decide) (by decide +kernel),
      typ_word (w := [0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0]) v₃_eq.symm (by decide) (by decide +kernel)⟩
  · exact ⟨[1, 1, 0, 1, 0, 1, 0, 1, 0], typ_word (w := [0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1]) v₂_eq.symm (by decide) (by decide +kernel),
      typ_word (w := [0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0]) v₂_eq.symm (by decide) (by decide +kernel)⟩

theorem mem_cls_typ (g : Co1) : g • v₂ ∈ cls (typ (v₂ + g • v₂)).val :=
  ⟨⟨g, rfl⟩, typ_spec _⟩

theorem mem_cls_of_typ_eq {g g' : Co1} (h : typ (v₂ + g • v₂) = typ (v₂ + g' • v₂)) :
    g' • v₂ ∈ cls (typ (v₂ + g • v₂)).val := by
  rw [h]
  exact mem_cls_typ g'

theorem typ_add_smul {k : Co1} (hk : k • v₂ = v₂) (z : Vec24) :
    typ (v₂ + k • z) = typ (v₂ + z) := by
  rw [← typ_smul k (v₂ + z), smul_add', hk]

end

theorem gB_smul_ne : gB • v₂ ≠ v₂ := by
  rw [v₂_eq, show gB = wordE [1] from (mul_one gB).symm, wordE_smul]
  exact vecOf_ne (by decide +kernel) (by norm_num) (by decide +kernel)

section
variable [h0 : Corpus.Co1.Orbits]
include h0

/-- **Wilcox criterion for `Co₁`**, for any group isomorphic to the native model. -/
theorem wilcoxCriterion_of_mulEquiv {G : Type} [Group G] (e : G ≃* Co1) : WilcoxCriterion G := by
  let _ : MulAction G Vec24 := MulAction.compHom Vec24 (e : G →* Co1)
  have : Finite G := Finite.of_equiv _ e.symm.toEquiv
  let x₀ : MulAction.orbit G v₂ := ⟨v₂, MulAction.mem_orbit_self v₂⟩
  have hcoe : ∀ (g : G) (y : MulAction.orbit G v₂), ((g • y : MulAction.orbit G v₂) : Vec24) =
      e g • (y : Vec24) := fun _ _ => rfl
  have hx : ∀ g : G, ((g • x₀ : MulAction.orbit G v₂) : Vec24) = e g • v₂ := fun _ => rfl
  have hstab : ∀ h : G, h ∈ MulAction.stabilizer G x₀ ↔ e h • v₂ = v₂ := fun h => by
    rw [MulAction.mem_stabilizer_iff, Subtype.ext_iff, hx]
  have hall : ∀ y : MulAction.orbit G v₂, ∃ g : G, g • x₀ = y := by
    rintro ⟨y, g, rfl⟩
    exact ⟨g, rfl⟩
  refine wilcoxCriterion_of_labelling_sq x₀ hall (fun y => typ (v₂ + (y : Vec24))) ?_ ?_ ?_ ?_
  · intro y y'
    obtain ⟨gy, rfl⟩ := hall y
    obtain ⟨gy', rfl⟩ := hall y'
    simp only [hx]
    constructor
    · intro hl
      obtain ⟨g, hg, hgy⟩ := Corpus.Co1.Orbits.cls_trans (typ _).isLt (mem_cls_typ (e gy)) (mem_cls_of_typ_eq hl)
      refine ⟨e.symm g, (hstab _).2 (by rw [MulEquiv.apply_symm_apply]; exact hg), ?_⟩
      apply Subtype.ext
      rw [hcoe, hx, hx, MulEquiv.apply_symm_apply]
      exact hgy
    · rintro ⟨h, hh, hhy⟩
      rw [hstab] at hh
      have h1 := congrArg Subtype.val hhy
      rw [hcoe, hx, hx] at h1
      rw [← h1, typ_add_smul hh]
  · intro j
    obtain ⟨a, h1, h2⟩ := exists_sq_word j
    refine ⟨e.symm (wordE a), ?_, ?_⟩
    · simp only [hx, MulEquiv.apply_symm_apply]
      exact h1
    · simp only [hx, map_mul, MulEquiv.apply_symm_apply, ← wordE_append]
      exact h2
  · apply Subgroup.isGood_of_commuting_involutions (u := e.symm uE) (v := e.symm cE)
    · rw [hstab, MulEquiv.apply_symm_apply]; exact uE_fix
    · rw [hstab, MulEquiv.apply_symm_apply]; exact cE_fix
    · rw [← map_pow, uE_sq, map_one]
    · rw [← map_pow, cE_sq, map_one]
    · rw [← map_mul, ← map_mul, uE_cE]
    · rw [Ne, map_eq_one_iff _ e.symm.injective]; exact uE_ne_one
    · rw [Ne, map_eq_one_iff _ e.symm.injective]; exact cE_ne_one
    · exact fun h => uE_ne_cE (e.symm.injective h)
  · refine ⟨e.symm gB • x₀, fun h => gB_smul_ne ?_⟩
    have h1 := congrArg Subtype.val h
    rwa [hx, MulEquiv.apply_symm_apply] at h1

/-- **Wilcox criterion for the Conway group `Co₁`.** -/
theorem wilcoxCriterion : WilcoxCriterion TauCeti.SporadicName.Co1.Group :=
  wilcoxCriterion_of_mulEquiv Corpus.Co1.Orbits.nonempty_mulEquiv.some.symm

end

end CFSGOutside.HallPaige.Co1
