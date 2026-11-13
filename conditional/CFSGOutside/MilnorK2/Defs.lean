import Mathlib

/-!
# The Steinberg group and `K₂`

J. Milnor, *Introduction to Algebraic K-theory*, Annals of Mathematics Studies 72, Princeton University
Press, 1971, DOI 10.1515/9781400881796, §5 (the Steinberg group `St(R)` and `K₂(R) = ker(St(R) → GL(R))`).
`St(R)` is the Steinberg group on generators `x_ij(a)` (`i ≠ j` in `ℕ`, `a ∈ R`) with Steinberg's relations,
and `GL(R)` acts on `ℕ → R`, each `GL_n(R)` acting on the first `n` coordinates.
-/

namespace CFSGOutside.MilnorK2

open scoped commutatorElement

section Steinberg

variable (ι R : Type*) [CommRing R]

/-- Off-diagonal index pairs `(i, j)`, `i ≠ j`. -/
abbrev OffDiag := {p : ι × ι // p.1 ≠ p.2}

variable {ι R}

/-- The free generator `x_ij(a)`. -/
def gen {i j : ι} (h : i ≠ j) (a : R) : FreeGroup (OffDiag ι × R) :=
  FreeGroup.of (⟨(i, j), h⟩, a)

variable (ι R)

/-- Steinberg's relations (Milnor, §5): `x_ij(a) x_ij(b) = x_ij(a + b)`;
`[x_ij(a), x_jl(b)] = x_il(ab)` for `i ≠ l`; `[x_ij(a), x_kl(b)] = 1` for `j ≠ k`, `i ≠ l`. -/
def stRels : Set (FreeGroup (OffDiag ι × R)) :=
  {r | ∃ (p : OffDiag ι) (a b : R),
      r = FreeGroup.of (p, a) * FreeGroup.of (p, b) * (FreeGroup.of (p, a + b))⁻¹} ∪
  {r | ∃ (i j l : ι) (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) (a b : R),
      r = ⁅gen hij a, gen hjl b⁆ * (gen hil (a * b))⁻¹} ∪
  {r | ∃ (i j k l : ι) (hij : i ≠ j) (hkl : k ≠ l) (_ : j ≠ k) (_ : i ≠ l) (a b : R),
      r = ⁅gen hij a, gen hkl b⁆}

/-- The Steinberg group `St_ι(R)` of Milnor, §5: `St_n(R) = Steinberg (Fin n) R` and
`St(R) = Steinberg ℕ R`, the direct limit of the `St_n(R)`. -/
abbrev Steinberg := PresentedGroup (stRels ι R)

variable {ι R}

/-- The generator `x_ij(a)` of the Steinberg group. -/
def X {i j : ι} (h : i ≠ j) (a : R) : Steinberg ι R := PresentedGroup.of (⟨(i, j), h⟩, a)

end Steinberg

section Action

variable {ι R : Type*} [CommRing R] [DecidableEq ι]

/-- The elementary transvection `e_ij(a) = 1 + a E_ij` acting on `ι → R`. -/
def elem {i j : ι} (h : i ≠ j) (a : R) : (ι → R) ≃ₗ[R] (ι → R) where
  toFun v := v + Pi.single i (a * v j)
  invFun v := v - Pi.single i (a * v j)
  map_add' v w := by
    simp only [Pi.add_apply, mul_add, Pi.single_add]; abel
  map_smul' c v := by
    ext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Pi.single_apply]
    split_ifs <;> ring
  left_inv v := by
    ext k
    simp only [Pi.add_apply, Pi.sub_apply, Pi.single_apply, if_neg h.symm]
    split_ifs <;> ring
  right_inv v := by
    ext k
    simp only [Pi.add_apply, Pi.sub_apply, Pi.single_apply, if_neg h.symm]
    split_ifs <;> ring

lemma elem_apply {i j : ι} (h : i ≠ j) (a : R) (v : ι → R) (k : ι) :
    elem h a v k = v k + if k = i then a * v j else 0 := by
  simp [elem, Pi.single_apply]

lemma comm_eq_of {G : Type*} [Group G] {a b c : G} (h : a * b = c * (b * a)) : ⁅a, b⁆ = c := by
  rw [commutatorElement_def, h]; group

variable (ι R)

/-- The map `St_ι(R) → GL(ι → R)`, `x_ij(a) ↦ e_ij(a)` (Milnor, §5). For `ι = ℕ` this is Milnor's
`St(R) → GL(R)`, with `GL(R)` embedded in the automorphisms of `ℕ → R`. -/
noncomputable def stToGL : Steinberg ι R →* ((ι → R) ≃ₗ[R] (ι → R)) :=
  PresentedGroup.toGroup (f := fun g => elem g.1.2 g.2) (by
    rintro r ((⟨p, a, b, rfl⟩ | ⟨i, j, l, hij, hjl, hil, a, b, rfl⟩) |
      ⟨i, j, k, l, hij, hkl, hjk, hil, a, b, rfl⟩)
    · simp only [map_mul, map_inv, FreeGroup.lift_apply_of, mul_inv_eq_one]
      ext v k
      simp only [LinearEquiv.mul_apply, elem_apply, if_neg p.2.symm]
      split_ifs <;> ring
    · simp only [gen, map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of,
        mul_inv_eq_one]
      refine comm_eq_of ?_
      ext v k
      simp only [LinearEquiv.mul_apply, elem_apply, if_neg hij.symm,
        if_neg hjl.symm, if_neg hil.symm, if_neg hij, if_neg hil, if_neg hjl]
      split_ifs <;> simp_all <;> ring
    · simp only [gen, map_commutatorElement, FreeGroup.lift_apply_of]
      rw [commutatorElement_eq_one_iff_mul_comm]
      ext v m
      simp only [LinearEquiv.mul_apply, elem_apply, if_neg hij.symm,
        if_neg hkl.symm, if_neg hjk, if_neg hil, if_neg (Ne.symm hjk), if_neg (Ne.symm hil)]
      split_ifs <;> simp_all <;> ring)

lemma stToGL_X {i j : ι} (h : i ≠ j) (a : R) : stToGL ι R (X h a) = elem h a :=
  PresentedGroup.toGroup.of _

/-- Milnor's `K₂(R) = ker(St(R) → GL(R))` (§5). -/
noncomputable def K₂ : Subgroup (Steinberg ℕ R) := (stToGL ℕ R).ker

end Action

end CFSGOutside.MilnorK2
