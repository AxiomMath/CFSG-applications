import CFSGOutside.MilnorK2.Paper

/-!
# `K₂` as Milnor defines it

Milnor (*Introduction to Algebraic K-theory*, §5) defines `St(R)` as the direct limit of the groups
`St(n, R)` along the maps `St(n, R) → St(n + 1, R)`, `GL(R)` as the union of the `GL(n, R)`, and
`K₂ R` as the kernel of `St(R) → GL(R)`. `CFSGOutside.MilnorK2.Defs` instead presents `St(R)`
directly on the generators `x_ij(a)`, `i ≠ j` in `ℕ`, and lets it act on `ℕ → R`. This file checks
that the two agree:

* `exists_unique_lift`: `Steinberg ℕ R` with the maps `incl n` is the direct limit of the
  `Steinberg (Fin n) R` along `stab n` (the universal property of the colimit);
* `stToMatrix_X`: `St(n, R) → GL(n, R)` sends `x_ij(a)` to the matrix `1 + a E_ij`;
* `incl_mem_K₂_iff`: an element of `St(n, R)` lies in `K₂ R` (after stabilisation) exactly when its
  image in the matrix group `GL(n, R)` is `1`. So `K₂ R` is the kernel of Milnor's `St(R) → GL(R)`.

The headline `K₂_eq_bot` is then restated in matrix form as `stToMatrix_injective` (for every
`n ≥ 3`) and `incl_eq_one_of_stToMatrix_eq_one` (Milnor's stable statement, for every `n`).
-/

namespace CFSGOutside.MilnorK2

open scoped commutatorElement

section Functorial

variable {R : Type*} [CommRing R]

/-- `St_ι(R) → St_κ(R)` along an injection `ι ↪ κ`, `x_ij(a) ↦ x_{e i, e j}(a)`. -/
noncomputable def mapIdx {ι κ : Type*} (e : ι ↪ κ) : Steinberg ι R →* Steinberg κ R :=
  PresentedGroup.toGroup (f := fun g => X (e.injective.ne g.1.2) g.2) (by
    rintro r ((⟨p, a, b, rfl⟩ | ⟨i, j, l, hij, hjl, hil, a, b, rfl⟩) |
      ⟨i, j, k, l, hij, hkl, hjk, hil, a, b, rfl⟩)
    · simp only [map_mul, map_inv, FreeGroup.lift_apply_of, X_mul, mul_inv_cancel]
    · simp only [gen, map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of]
      rw [X_comm_B _ _ (e.injective.ne hil), mul_inv_cancel]
    · simp only [gen, map_commutatorElement, FreeGroup.lift_apply_of]
      exact X_comm_C _ _ (e.injective.ne hjk) (e.injective.ne hil) a b)

lemma mapIdx_X {ι κ : Type*} (e : ι ↪ κ) {i j : ι} (h : i ≠ j) (a : R) :
    mapIdx e (X h a) = X (e.injective.ne h) a :=
  PresentedGroup.toGroup.of _

lemma mapIdx_comp {ι κ μ : Type*} (e : ι ↪ κ) (e' : κ ↪ μ) :
    (mapIdx (R := R) e').comp (mapIdx e) = mapIdx (e.trans e') := by
  apply PresentedGroup.ext
  rintro ⟨⟨⟨i, j⟩, hij⟩, a⟩
  change mapIdx e' (mapIdx e (X hij a)) = mapIdx (e.trans e') (X hij a)
  rw [mapIdx_X, mapIdx_X, mapIdx_X]
  rfl

/-- Milnor's stabilisation map `St(n, R) → St(n + 1, R)`. -/
noncomputable def stab (n : ℕ) : Steinberg (Fin n) R →* Steinberg (Fin (n + 1)) R :=
  mapIdx Fin.castSuccEmb

/-- `St(m, R) → St(n, R)` for `m ≤ n`, the composite of the stabilisation maps. -/
noncomputable def stabLE {m n : ℕ} (h : m ≤ n) : Steinberg (Fin m) R →* Steinberg (Fin n) R :=
  mapIdx (Fin.castLEEmb h)

lemma stabLE_succ {m n : ℕ} (h : m ≤ n) :
    (stab n).comp (stabLE h) = stabLE (R := R) (h.trans n.le_succ) := by
  rw [stab, stabLE, stabLE, mapIdx_comp]
  rfl

/-- A family `f n : St(n, R) → G` compatible with stabilisation is compatible with every `stabLE`. -/
lemma comp_stabLE {G : Type*} [Group G] (f : ∀ n, Steinberg (Fin n) R →* G)
    (hf : ∀ n, (f (n + 1)).comp (stab n) = f n) {m n : ℕ} (h : m ≤ n) :
    (f n).comp (stabLE h) = f m := by
  induction n, h using Nat.le_induction with
  | base =>
    have : stabLE (R := R) (le_refl m) = MonoidHom.id _ := by
      apply PresentedGroup.ext
      rintro ⟨⟨⟨i, j⟩, hij⟩, a⟩
      change mapIdx _ (X hij a) = X hij a
      rw [mapIdx_X]
      rfl
    rw [this, MonoidHom.comp_id]
  | succ n hmn ih =>
    rw [← stabLE_succ hmn, ← MonoidHom.comp_assoc, hf, ih]

/-- **`St(R)` is Milnor's direct limit of the `St(n, R)`.** Every family of homomorphisms
`f n : St(n, R) → G` compatible with stabilisation factors uniquely through `St(R)`. -/
theorem exists_unique_lift {G : Type*} [Group G] (f : ∀ n, Steinberg (Fin n) R →* G)
    (hf : ∀ n, (f (n + 1)).comp (stab n) = f n) :
    ∃! φ : Steinberg ℕ R →* G, ∀ n, φ.comp (incl n) = f n := by
  -- the value of `x_ij(a)` computed in any `St(N, R)` with `i, j < N`
  have hval : ∀ (N N' : ℕ) (i j : ℕ) (hij : i ≠ j) (hi : i < N) (hj : j < N) (hi' : i < N')
      (hj' : j < N') (a : R),
      f N (X (i := ⟨i, hi⟩) (j := ⟨j, hj⟩) (fun e => hij (Fin.mk.inj e)) a) =
        f N' (X (i := ⟨i, hi'⟩) (j := ⟨j, hj'⟩) (fun e => hij (Fin.mk.inj e)) a) := by
    intro N N' i j hij hi hj hi' hj' a
    have key : ∀ (M M' : ℕ) (hMM : M ≤ M') (hi : i < M) (hj : j < M) (hi' : i < M')
        (hj' : j < M'),
        f M (X (i := ⟨i, hi⟩) (j := ⟨j, hj⟩) (fun e => hij (Fin.mk.inj e)) a) =
          f M' (X (i := ⟨i, hi'⟩) (j := ⟨j, hj'⟩) (fun e => hij (Fin.mk.inj e)) a) := by
      intro M M' hMM hi hj hi' hj'
      rw [← comp_stabLE f hf hMM, MonoidHom.comp_apply, stabLE, mapIdx_X]
      rfl
    rcases le_total N N' with h | h
    · exact key N N' h hi hj hi' hj'
    · exact (key N' N h hi' hj' hi hj).symm
  let g : OffDiag ℕ × R → G := fun x =>
    f (max x.1.1.1 x.1.1.2 + 1)
      (X (i := ⟨x.1.1.1, by omega⟩) (j := ⟨x.1.1.2, by omega⟩)
        (fun e => x.1.2 (Fin.mk.inj e)) x.2)
  -- `g` agrees with the value computed in any large enough `St(N, R)`
  have hg : ∀ (N : ℕ) (i j : ℕ) (hij : i ≠ j) (hi : i < N) (hj : j < N) (a : R),
      g (⟨(i, j), hij⟩, a) =
        f N (X (i := ⟨i, hi⟩) (j := ⟨j, hj⟩) (fun e => hij (Fin.mk.inj e)) a) := by
    intro N i j hij hi hj a
    exact hval _ _ i j hij _ _ hi hj a
  have hrels : ∀ r ∈ stRels ℕ R, FreeGroup.lift g r = 1 := by
    rintro r ((⟨⟨⟨i, j⟩, hij⟩, a, b, rfl⟩ | ⟨i, j, l, hij, hjl, hil, a, b, rfl⟩) |
      ⟨i, j, k, l, hij, hkl, hjk, hil, a, b, rfl⟩)
    · have hi : i < max i j + 1 := by omega
      have hj : j < max i j + 1 := by omega
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      rw [hg _ i j hij hi hj, hg _ i j hij hi hj, hg _ i j hij hi hj, ← map_mul, X_mul,
        mul_inv_cancel]
    · set N := max (max i j) l + 1
      have hi : i < N := by omega
      have hj : j < N := by omega
      have hl : l < N := by omega
      simp only [gen, map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of]
      rw [hg N i j hij hi hj, hg N j l hjl hj hl, hg N i l hil hi hl, ← map_commutatorElement,
        X_comm_B, mul_inv_cancel]
      exact fun e => hil (Fin.mk.inj e)
    · set N := max (max i j) (max k l) + 1
      have hi : i < N := by omega
      have hj : j < N := by omega
      have hk : k < N := by omega
      have hl : l < N := by omega
      simp only [gen, map_commutatorElement, FreeGroup.lift_apply_of]
      rw [hg N i j hij hi hj, hg N k l hkl hk hl, ← map_commutatorElement, X_comm_C, map_one]
      · exact fun e => hjk (Fin.mk.inj e)
      · exact fun e => hil (Fin.mk.inj e)
  let φ : Steinberg ℕ R →* G := PresentedGroup.toGroup (f := g) hrels
  have hφ : ∀ n, φ.comp (incl n) = f n := by
    intro n
    apply PresentedGroup.ext
    rintro ⟨⟨⟨i, j⟩, hij⟩, a⟩
    change φ (incl n (X hij a)) = f n (X hij a)
    rw [incl_X]
    exact (PresentedGroup.toGroup.of _).trans (hg n i.1 j.1 _ i.2 j.2 a)
  refine ⟨φ, hφ, fun ψ hψ => ?_⟩
  apply MonoidHom.ext
  intro s
  obtain ⟨m, -, t, rfl⟩ := exists_mem_range_incl (R := R) s
  rw [← MonoidHom.comp_apply, ← MonoidHom.comp_apply, hψ, hφ]

end Functorial

section Matrix

variable {R : Type*} [CommRing R]

/-- The linear automorphisms of `Fin n → R` are the matrix group `GL(n, R)`. -/
noncomputable def autEquivGL (n : ℕ) : ((Fin n → R) ≃ₗ[R] (Fin n → R)) ≃* GL (Fin n) R :=
  (Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _)).symm

/-- Milnor's `St(n, R) → GL(n, R)`, valued in invertible matrices. -/
noncomputable def stToMatrix (n : ℕ) : Steinberg (Fin n) R →* GL (Fin n) R :=
  (autEquivGL n).toMonoidHom.comp (stToGL (Fin n) R)

lemma coe_autEquivGL_apply_mulVec {n : ℕ} (e : (Fin n → R) ≃ₗ[R] (Fin n → R)) (v : Fin n → R) :
    ((autEquivGL n e : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).mulVec v = e v := by
  have : Matrix.GeneralLinearGroup.toLin (autEquivGL n e) =
      (LinearMap.GeneralLinearGroup.generalLinearEquiv R (Fin n → R)).symm e := by
    simp [autEquivGL]
  have h2 := congrArg (fun u : LinearMap.GeneralLinearGroup R (Fin n → R) => u.1 v) this
  have h3 : ((LinearMap.GeneralLinearGroup.generalLinearEquiv R (Fin n → R)).symm e).1 v = e v := by
    conv_rhs => rw [← (LinearMap.GeneralLinearGroup.generalLinearEquiv R (Fin n → R)).apply_symm_apply e]
    rw [LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv]
  rw [← h3]
  simpa [Matrix.GeneralLinearGroup.coe_toLin, Matrix.toLin'_apply] using h2

/-- `x_ij(a) ↦ 1 + a E_ij`, the elementary matrix (Milnor, §5). -/
lemma stToMatrix_X {n : ℕ} {i j : Fin n} (h : i ≠ j) (a : R) :
    ((stToMatrix n (X h a) : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = Matrix.transvection i j a := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, stToMatrix, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, coe_autEquivGL_apply_mulVec, stToGL_X]
  ext k
  rw [elem_apply]
  simp only [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply,
    Matrix.single_mulVec_eq, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  split_ifs with hk
  · subst hk
    simp [Matrix.add_mulVec, Matrix.single_mulVec_eq]
  · simp [Matrix.add_mulVec, Matrix.single_mulVec_eq, Pi.single_apply, hk]

lemma stToMatrix_eq_one_iff {n : ℕ} (t : Steinberg (Fin n) R) :
    stToMatrix n t = 1 ↔ stToGL (Fin n) R t = 1 := by
  rw [stToMatrix, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]

/-- **`K₂ R` is the kernel of Milnor's `St(R) → GL(R)`.** An element of `St(n, R)` lies in `K₂ R`
after stabilisation exactly when its image in the matrix group `GL(n, R)` is `1`. -/
theorem incl_mem_K₂_iff {n : ℕ} (t : Steinberg (Fin n) R) :
    incl n t ∈ K₂ R ↔ stToMatrix n t = 1 := by
  rw [stToMatrix_eq_one_iff]
  constructor
  · intro hs
    have h1 : stToGL ℕ R (incl n t) = 1 := hs
    ext w k
    have := stToGL_incl_zeroExt n t w
    rw [h1] at this
    exact congrFun (zeroExt_injective n this.symm) k
  · intro ht
    change stToGL ℕ R (incl n t) = 1
    ext v k
    -- split `v` into its first `n` coordinates and the rest, which `incl n t` fixes
    let w : Fin n → R := fun i => v i
    let u : ℕ → R := fun k => if k < n then 0 else v k
    have hv : v = zeroExt n w + u := by
      ext k
      simp only [zeroExt, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, w, u]
      split_ifs <;> simp
    have hu : stToGL ℕ R (incl n t) u = u := by
      let S : Subgroup (Steinberg (Fin n) R) :=
        { carrier := {t | stToGL ℕ R (incl n t) u = u}
          one_mem' := by simp
          mul_mem' := fun {a b} ha hb => by
            simp only [Set.mem_setOf_eq, map_mul, LinearEquiv.mul_apply] at *
            rw [hb, ha]
          inv_mem' := fun {a} ha => by
            simp only [Set.mem_setOf_eq, map_inv] at *
            apply (stToGL ℕ R (incl n a)).injective
            rw [aut_apply_inv, ha] }
      have hS : S = ⊤ := by
        rw [eq_top_iff, ← PresentedGroup.closure_range_of, Subgroup.closure_le]
        rintro _ ⟨⟨⟨⟨i, j⟩, hij⟩, a⟩, rfl⟩
        change stToGL ℕ R (incl n (X hij a)) u = u
        rw [incl_X, stToGL_X]
        ext k
        rw [elem_apply]
        simp [u, j.2]
      exact (hS ▸ Subgroup.mem_top t : t ∈ S)
    rw [hv, map_add, hu, stToGL_incl_zeroExt, ht]
    rfl

end Matrix

section FiniteField

variable {F : Type} [Field F]

/-- `K₂(F) = 1` in matrix form, Milnor's stable statement: for a finite field `F`, an element of
`St(n, F)` that maps to the identity matrix in `GL(n, F)` becomes trivial in `St(F)`. -/
theorem incl_eq_one_of_stToMatrix_eq_one [CFSGOutside.Corpus.ExistsSteinbergSLRelsEquiv] [Finite F]
    {n : ℕ} (t : Steinberg (Fin n) F) (ht : stToMatrix n t = 1) : incl n t = 1 := by
  have h := (incl_mem_K₂_iff t).2 ht
  rw [K₂_eq_bot] at h
  exact h

/-- The unstable form (Steinberg): `St(n, F) → GL(n, F)` is injective for `n ≥ 3`. -/
theorem stToMatrix_injective [CFSGOutside.Corpus.ExistsSteinbergSLRelsEquiv] [Finite F] {n : ℕ}
    (hn : 3 ≤ n) : Function.Injective (stToMatrix (R := F) n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [stToMatrix, MonoidHom.coe_comp]
  exact (autEquivGL _).injective.comp (stToGL_fin_injective (by omega))

end FiniteField

end CFSGOutside.MilnorK2
