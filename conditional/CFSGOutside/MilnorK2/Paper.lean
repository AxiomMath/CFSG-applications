import CFSGOutside.MilnorK2.Defs
import CFSGOutside.Corpus.ExistsSteinbergSLRelsEquiv

/-!
# `K₂` of a finite field is trivial

J. Milnor, *Introduction to Algebraic K-theory*, Annals of Mathematics Studies 72, Princeton University
Press, 1971, DOI 10.1515/9781400881796 (Steinberg's theorem `K₂(F_q) = 1`; see also Weibel, *The K-book*,
Corollary III.6.1.1). The definitions are in `CFSGOutside.MilnorK2.Defs`.

The proof reduces to the injectivity of `St_{m+1}(F) → GL_{m+1}(F)` for `m ≥ 2`, which follows from the
corpus Steinberg presentation of `SL_{m+1}(F)`, `CFSGOutside.Corpus.ExistsSteinbergSLRelsEquiv`. That
presentation is Milnor's with the derived relation `[x_ij(a), x_ki(b)] = x_kj(-ab)` and `x_ii = 1` added;
`toCorpus` and `fromCorpus` show the two presented groups are isomorphic.
-/

namespace CFSGOutside.MilnorK2

open scoped commutatorElement
open CFSGOutside.Corpus.Open (steinbergSLRels)

section Steinberg

variable {ι R : Type*} [CommRing R]

lemma lift_of_eq_one {α : Type*} {rels : Set (FreeGroup α)} {r : FreeGroup α}
    (hr : r ∈ rels) : FreeGroup.lift (PresentedGroup.of (rels := rels)) r = 1 := by
  have : FreeGroup.lift (PresentedGroup.of (rels := rels)) = PresentedGroup.mk rels :=
    FreeGroup.ext_hom _ _ fun x => rfl
  rw [this]
  exact (QuotientGroup.eq_one_iff r).2 (Subgroup.subset_normalClosure hr)

lemma X_mul {i j : ι} (h : i ≠ j) (a b : R) : X h a * X h b = X h (a + b) := by
  have := lift_of_eq_one (rels := stRels ι R) (Or.inl (Or.inl ⟨⟨(i, j), h⟩, a, b, rfl⟩))
  simp only [map_mul, map_inv, FreeGroup.lift_apply_of] at this
  exact mul_inv_eq_one.1 this

lemma X_zero {i j : ι} (h : i ≠ j) : X h (0 : R) = 1 := by
  have := X_mul h (0 : R) 0
  rw [add_zero] at this
  exact mul_eq_left.1 this

lemma X_neg {i j : ι} (h : i ≠ j) (a : R) : X h (-a) = (X h a)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, X_mul, neg_add_cancel, X_zero]

lemma X_comm_B {i j l : ι} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) (a b : R) :
    ⁅X hij a, X hjl b⁆ = X hil (a * b) := by
  have := lift_of_eq_one (rels := stRels ι R)
    (Or.inl (Or.inr ⟨i, j, l, hij, hjl, hil, a, b, rfl⟩))
  simp only [gen, map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of] at this
  exact mul_inv_eq_one.1 this

lemma X_comm_C {i j k l : ι} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (hil : i ≠ l) (a b : R) :
    ⁅X hij a, X hkl b⁆ = 1 := by
  have := lift_of_eq_one (rels := stRels ι R)
    (Or.inr ⟨i, j, k, l, hij, hkl, hjk, hil, a, b, rfl⟩)
  simp only [gen, map_commutatorElement, FreeGroup.lift_apply_of] at this
  exact this

/-- The derived relation `[x_ij(a), x_ki(b)] = x_kj(-ab)` (`j ≠ k`). -/
lemma X_comm_D {i j k : ι} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) (a b : R) :
    ⁅X hij a, X hki b⁆ = X hkj (-(a * b)) := by
  rw [mul_comm a b, X_neg, ← X_comm_B hki hij hkj b a, commutatorElement_inv]

end Steinberg

section Stable

variable {R : Type*} [CommRing R]

/-- The stabilization map `St_n(R) → St(R)`. -/
noncomputable def incl (n : ℕ) : Steinberg (Fin n) R →* Steinberg ℕ R :=
  PresentedGroup.toGroup (f := fun g => X (Fin.val_injective.ne g.1.2) g.2) (by
    rintro r ((⟨p, a, b, rfl⟩ | ⟨i, j, l, hij, hjl, hil, a, b, rfl⟩) |
      ⟨i, j, k, l, hij, hkl, hjk, hil, a, b, rfl⟩)
    · simp only [map_mul, map_inv, FreeGroup.lift_apply_of, X_mul, mul_inv_cancel]
    · simp only [gen, map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of]
      rw [X_comm_B _ _ (Fin.val_injective.ne hil), mul_inv_cancel]
    · simp only [gen, map_commutatorElement, FreeGroup.lift_apply_of]
      exact X_comm_C _ _ (Fin.val_injective.ne hjk) (Fin.val_injective.ne hil) a b)

lemma incl_X {n : ℕ} {i j : Fin n} (h : i ≠ j) (a : R) :
    incl n (X h a) = X (Fin.val_injective.ne h) a :=
  PresentedGroup.toGroup.of _

lemma range_incl_mono {n n' : ℕ} (h : n ≤ n') :
    (incl (R := R) n).range ≤ (incl n').range := by
  rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
    Subgroup.closure_le]
  rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
  have hne : Fin.castLE h g.1.1.1 ≠ Fin.castLE h g.1.1.2 := fun e =>
    g.1.2 (Fin.castLE_injective h e)
  exact ⟨X hne g.2, by rw [incl_X]; rfl⟩

/-- Every element of `St(R)` comes from some `St_{m+1}(R)` with `m ≥ 2`. -/
lemma exists_mem_range_incl (s : Steinberg ℕ R) :
    ∃ m, 2 ≤ m ∧ s ∈ (incl (R := R) (m + 1)).range := by
  have hs : s ∈ Subgroup.closure (Set.range (PresentedGroup.of (rels := stRels ℕ R))) := by
    rw [PresentedGroup.closure_range_of]; exact Subgroup.mem_top s
  induction hs using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    obtain ⟨⟨⟨i, j⟩, hij⟩, a⟩ := g
    refine ⟨max i j + 2, by omega, ?_⟩
    have hi : i < max i j + 2 + 1 := by omega
    have hj : j < max i j + 2 + 1 := by omega
    have hne : (⟨i, hi⟩ : Fin _) ≠ ⟨j, hj⟩ := fun e => hij (Fin.mk.inj e)
    exact ⟨X hne a, by rw [incl_X]; rfl⟩
  | one => exact ⟨2, le_rfl, Subgroup.one_mem _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨m, hm, hxm⟩ := hx
    obtain ⟨m', hm', hym⟩ := hy
    refine ⟨max m m', le_max_of_le_left hm, Subgroup.mul_mem _ ?_ ?_⟩
    · exact range_incl_mono (by omega) hxm
    · exact range_incl_mono (by omega) hym
  | inv x _ hx =>
    obtain ⟨m, hm, hxm⟩ := hx
    exact ⟨m, hm, Subgroup.inv_mem _ hxm⟩

lemma aut_apply_inv {M : Type*} [AddCommGroup M] [Module R M] (e : M ≃ₗ[R] M) (x : M) :
    e (e⁻¹ x) = x := by
  rw [← LinearEquiv.mul_apply, mul_inv_cancel]; rfl

/-- Extension by zero `(Fin n → R) → (ℕ → R)`. -/
def zeroExt (n : ℕ) : (Fin n → R) →ₗ[R] (ℕ → R) where
  toFun w k := if h : k < n then w ⟨k, h⟩ else 0
  map_add' v w := by ext k; split_ifs <;> simp [*]
  map_smul' c v := by ext k; split_ifs <;> simp [*]

lemma zeroExt_injective (n : ℕ) : Function.Injective (zeroExt (R := R) n) := by
  intro v w h
  ext ⟨k, hk⟩
  have := congrFun h k
  simpa [zeroExt, hk] using this

/-- `St(R) → GL(ℕ → R)` restricted to `St_n(R)` is `St_n(R) → GL_n(R)`, extended by the
identity. -/
lemma stToGL_incl_zeroExt (n : ℕ) (t : Steinberg (Fin n) R) (w : Fin n → R) :
    stToGL ℕ R (incl n t) (zeroExt n w) = zeroExt n (stToGL (Fin n) R t w) := by
  let S : Subgroup (Steinberg (Fin n) R) :=
    { carrier := {t | ∀ w, stToGL ℕ R (incl n t) (zeroExt n w) =
        zeroExt n (stToGL (Fin n) R t w)}
      one_mem' := fun w => by simp
      mul_mem' := fun {a b} ha hb w => by
        simp only [Set.mem_setOf_eq, map_mul, LinearEquiv.mul_apply] at *
        rw [hb, ha]
      inv_mem' := fun {a} ha w => by
        simp only [Set.mem_setOf_eq, map_inv] at *
        apply (stToGL ℕ R (incl n a)).injective
        rw [ha, aut_apply_inv, aut_apply_inv] }
  have hS : S = ⊤ := by
    rw [eq_top_iff, ← PresentedGroup.closure_range_of, Subgroup.closure_le]
    rintro _ ⟨⟨⟨⟨i, j⟩, hij⟩, a⟩, rfl⟩ v
    change stToGL ℕ R (incl n (X hij a)) (zeroExt n v) = zeroExt n (stToGL (Fin n) R (X hij a) v)
    rw [incl_X, stToGL_X, stToGL_X]
    ext k
    simp only [elem_apply, zeroExt, LinearMap.coe_mk, AddHom.coe_mk, dif_pos j.2]
    by_cases hk : k < n
    · simp only [dif_pos hk, elem_apply, ← Fin.val_inj]
    · simp only [dif_neg hk, zero_add]
      rw [if_neg]
      rintro rfl
      exact hk i.2
  have ht : t ∈ S := hS ▸ Subgroup.mem_top t
  exact ht w

end Stable

section FiniteField

variable {F : Type} [Field F]

/-- `St_n(F)` → the corpus presented group, `x_ij(a) ↦ (i, j, a)`. -/
noncomputable def toCorpus (n : ℕ) : Steinberg (Fin n) F →* PresentedGroup (steinbergSLRels n F) :=
  PresentedGroup.toGroup (f := fun g => PresentedGroup.of (g.1.1.1, g.1.1.2, g.2)) (by
    rintro r ((⟨⟨⟨i, j⟩, hij⟩, a, b, rfl⟩ | ⟨i, j, l, hij, hjl, hil, a, b, rfl⟩) |
      ⟨i, j, k, l, hij, hkl, hjk, hil, a, b, rfl⟩)
    · have := lift_of_eq_one (rels := steinbergSLRels n F)
        (Or.inl (Or.inr ⟨i, j, a, b, hij, rfl⟩))
      simpa only [map_mul, map_inv, FreeGroup.lift_apply_of] using this
    · have := lift_of_eq_one (rels := steinbergSLRels n F)
        (Or.inr ⟨i, j, j, l, a, b, hij, hjl, fun h => hil h.2.symm, rfl⟩)
      simp only [map_mul, map_inv, ↓reduceIte, FreeGroup.lift_apply_of] at this
      simpa only [gen, map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of,
        commutatorElement_def] using this
    · have := lift_of_eq_one (rels := steinbergSLRels n F)
        (Or.inr ⟨i, j, k, l, a, b, hij, hkl, fun h => hjk h.1.symm, rfl⟩)
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of, if_neg hjk, if_neg hil, map_one,
        inv_one, mul_one] at this
      simpa only [gen, map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of,
        commutatorElement_def] using this)

/-- The value of a corpus generator in `St_n(F)`. -/
noncomputable def ofCorpusGen {n : ℕ} (g : Fin n × Fin n × F) : Steinberg (Fin n) F :=
  if h : g.1 ≠ g.2.1 then X h g.2.2 else 1

/-- The corpus presented group → `St_n(F)`. -/
noncomputable def fromCorpus (n : ℕ) :
    PresentedGroup (steinbergSLRels n F) →* Steinberg (Fin n) F :=
  PresentedGroup.toGroup (f := ofCorpusGen) (by
    rintro r ((⟨i, c, rfl⟩ | ⟨i, j, c, d, hij, rfl⟩) | ⟨i, j, k, l, c, d, hij, hkl, hex, rfl⟩)
    · simp [ofCorpusGen]
    · simp only [map_mul, map_inv, FreeGroup.lift_apply_of, ofCorpusGen, dif_pos hij, X_mul,
        mul_inv_cancel]
    · simp only [map_mul, map_inv, FreeGroup.lift_apply_of, ofCorpusGen, dif_pos hij,
        dif_pos hkl]
      by_cases hjk : j = k
      · subst hjk
        have hli : i ≠ l := fun h => hex ⟨rfl, h.symm⟩
        simp only [↓reduceIte, map_one, FreeGroup.lift_apply_of, ofCorpusGen, dif_pos hli]
        rw [← commutatorElement_def, X_comm_B hij hkl hli, mul_inv_cancel]
      · by_cases hil : i = l
        · subst hil
          have hkj : k ≠ j := fun h => hjk h.symm
          simp only [if_neg hjk, ↓reduceIte, FreeGroup.lift_apply_of, ofCorpusGen, dif_pos hkj]
          rw [← commutatorElement_def, X_comm_D hij hkl hkj, mul_inv_cancel]
        · simp only [if_neg hjk, if_neg hil, map_one, inv_one, mul_one]
          rw [← commutatorElement_def, X_comm_C hij hkl hjk hil])

lemma fromCorpus_comp_toCorpus (n : ℕ) :
    (fromCorpus (F := F) n).comp (toCorpus n) = MonoidHom.id _ := by
  apply PresentedGroup.ext
  rintro ⟨⟨⟨i, j⟩, hij⟩, a⟩
  simp only [MonoidHom.comp_apply, MonoidHom.id_apply, toCorpus, fromCorpus,
    PresentedGroup.toGroup.of, ofCorpusGen, dif_pos hij]
  rfl

lemma toCorpus_injective (n : ℕ) : Function.Injective (toCorpus (F := F) n) := by
  intro s t h
  have := congrArg (fromCorpus n) h
  simpa only [← MonoidHom.comp_apply, fromCorpus_comp_toCorpus, MonoidHom.id_apply] using this

/-- **Steinberg (via the corpus):** `St_{m+1}(F) → GL_{m+1}(F)` is injective for `m ≥ 2`. -/
lemma stToGL_fin_injective [CFSGOutside.Corpus.ExistsSteinbergSLRelsEquiv] [Finite F] {m : ℕ}
    (hm : 2 ≤ m) :
    Function.Injective (stToGL (Fin (m + 1)) F) := by
  obtain ⟨φ, hφ⟩ := CFSGOutside.Corpus.ExistsSteinbergSLRelsEquiv.exists_steinbergSLRels_equiv (F := F) hm
  have heq : stToGL (Fin (m + 1)) F =
      (Matrix.SpecialLinearGroup.toLin').comp (φ.toMonoidHom.comp (toCorpus (m + 1))) := by
    apply PresentedGroup.ext
    rintro ⟨⟨⟨i, j⟩, hij⟩, a⟩
    change stToGL _ F (X hij a) = _
    rw [stToGL_X]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, toCorpus,
      PresentedGroup.toGroup.of]
    ext v k
    rw [Matrix.SpecialLinearGroup.toLin'_apply, hφ i j a hij, elem_apply]
    simp only [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply,
      Matrix.single_mulVec_eq, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    split_ifs with hk
    · subst hk
      (try rw [Matrix.toLin'_apply])
      simp [Matrix.add_mulVec, Matrix.single_mulVec_eq]
    · (try rw [Matrix.toLin'_apply])
      simp [Matrix.add_mulVec, Matrix.single_mulVec_eq, Pi.single_apply, hk]
  rw [heq]
  exact Matrix.SpecialLinearGroup.toLin'_injective.comp (φ.injective.comp (toCorpus_injective _))

/-- **K₂ of finite fields.** For every finite field F the group K₂(F) is trivial. Equivalently, the natural map from the
Steinberg group St(F) to GL(F) is injective, where St(F) is generated by symbols x_ij(a), for distinct indices i, j
and a ∈ F, subject to x_ij(a)x_ij(b) = x_ij(a+b), [x_ij(a), x_jl(b)] = x_il(ab) for i ≠ l, and [x_ij(a), x_kl(b)] =
1 for j ≠ k and i ≠ l, and the map sends x_ij(a) to the elementary matrix 1 + aE_ij.

Source: J. Milnor, Introduction to Algebraic K-theory, Ann. of Math. Studies 72 (1971), Corollary 9.13 (finite
fields; due to R. Steinberg). https://doi.org/10.1515/9781400881796

This version takes the corpus theorems it uses as instance arguments; the version in `unconditional/` supplies them
from the CFSG corpus. -/
theorem K₂_eq_bot [CFSGOutside.Corpus.ExistsSteinbergSLRelsEquiv] [Finite F] : K₂ F = ⊥ := by
  rw [eq_bot_iff]
  intro s hs
  obtain ⟨m, hm, t, rfl⟩ := exists_mem_range_incl s
  have h1 : stToGL ℕ F (incl (m + 1) t) = 1 := hs
  have h2 : stToGL (Fin (m + 1)) F t = 1 := by
    ext w k
    have := stToGL_incl_zeroExt (m + 1) t w
    rw [h1] at this
    have := zeroExt_injective (m + 1) this.symm
    exact congrFun this k
  have : t = 1 := stToGL_fin_injective hm (h2.trans (map_one _).symm)
  rw [this, map_one]
  exact Subgroup.one_mem _

/-- Equivalently (Milnor 1971, §9; Steinberg), `St(F) → GL(F)` is injective for a finite field `F`. -/
theorem stToGL_injective [CFSGOutside.Corpus.ExistsSteinbergSLRelsEquiv] [Finite F] : Function.Injective (stToGL ℕ F) :=
  (MonoidHom.ker_eq_bot_iff _).1 K₂_eq_bot

end FiniteField

end CFSGOutside.MilnorK2
