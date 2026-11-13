import CFSGOutside.AOVTame.Product

/-!
# AOV tameness: powers `ι → H` of a finite group

The Sylow subgroup `∏ S` of `ι → H`, the coordinate splittings `(ι → H) ≃* H × ({j // j ≠ i} → H)`,
and the permutation automorphisms.
-/

namespace AndersenOliverVentura.Tame

open Subgroup

variable {H : Type} [Group H] [Finite H] {p : ℕ} [hp : Fact p.Prime]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

section Sylow
variable (S : Sylow p H) (ι)

/-- `∏_i S`. -/
def piSub : Subgroup (ι → H) := Subgroup.pi Set.univ (fun _ => (S : Subgroup H))

lemma mem_piSub {x : ι → H} : x ∈ piSub ι S ↔ ∀ i, x i ∈ (S : Subgroup H) := by
  simp [piSub, mem_pi]

/-- The Sylow subgroup `∏_i S` of `ι → H`. -/
noncomputable def piSylow : Sylow p (ι → H) :=
  IsPGroup.toSylow (P := piSub ι S)
    (by
      intro x
      have hx : ∀ i, ∃ k : ℕ, (x : ι → H) i ^ (p ^ k) = 1 := fun i => by
        obtain ⟨k, hk⟩ := S.isPGroup' ⟨(x : ι → H) i, (mem_piSub ι S).1 x.2 i⟩
        exact ⟨k, congrArg Subtype.val hk⟩
      choose k hk using hx
      refine ⟨∑ i, k i, Subtype.ext (funext fun i => ?_)⟩
      have hdvd : p ^ k i ∣ p ^ (∑ j, k j) :=
        pow_dvd_pow p (Finset.single_le_sum (fun j _ => Nat.zero_le (k j)) (Finset.mem_univ i))
      obtain ⟨c, hc⟩ := hdvd
      change ((x : ι → H) ^ p ^ (∑ j, k j)) i = 1
      rw [Pi.pow_apply, hc, pow_mul, hk i, one_pow])
    (by
      rw [piSub, index_pi]
      intro h
      obtain ⟨i, -, hi⟩ := (Prime.dvd_finset_prod_iff (Nat.Prime.prime hp.out) _).1 h
      exact S.not_dvd_index hi)

@[simp] lemma coe_piSylow : (piSylow ι S : Subgroup (ι → H)) = piSub ι S := rfl

end Sylow

section Coord
variable (i : ι)

/-- `(ι → H) ≃* H × ({j // j ≠ i} → H)`. -/
def coordEquiv : (ι → H) ≃* H × ({j // j ≠ i} → H) where
  toFun g := (g i, fun j => g (j : ι))
  invFun x j := if hj : j = i then x.1 else x.2 ⟨j, hj⟩
  left_inv g := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  right_inv x := by
    ext j
    · simp
    · simp [j.2]
  map_mul' g g' := rfl

@[simp] lemma coordEquiv_apply (g : ι → H) :
    coordEquiv i g = (g i, fun j : {j // j ≠ i} => g (j : ι)) := rfl

lemma coordEquiv_symm_apply_self (x : H × ({j // j ≠ i} → H)) : (coordEquiv i).symm x i = x.1 := by
  simp [coordEquiv]

lemma coordEquiv_symm_apply_ne (x : H × ({j // j ≠ i} → H)) {j : ι} (hj : j ≠ i) :
    (coordEquiv i).symm x j = x.2 ⟨j, hj⟩ := by
  simp [coordEquiv, hj]

variable (S : Sylow p H)

lemma map_coordEquiv_piSylow :
    ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H)).map (coordEquiv i).toMonoidHom =
      ((prodSylow S (piSylow {j // j ≠ i} S) : Sylow p _) : Subgroup _) := by
  ext ⟨a, b⟩
  constructor
  · rintro ⟨g, hg, e⟩
    change (g i, fun j : {j // j ≠ i} => g (j : ι)) = (a, b) at e
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
    exact ⟨(mem_piSub ι S).1 hg i, (mem_piSub _ S).2 fun j => (mem_piSub ι S).1 hg j⟩
  · rintro ⟨ha, hb⟩
    refine ⟨(coordEquiv i).symm (a, b), (mem_piSub ι S).2 fun j => ?_, ?_⟩
    · by_cases hj : j = i
      · subst hj; rw [coordEquiv_symm_apply_self]; exact ha
      · rw [coordEquiv_symm_apply_ne i _ hj]; exact (mem_piSub _ S).1 hb _
    · exact (coordEquiv i).apply_symm_apply (a, b)

end Coord

section Perm
variable (σ : Equiv.Perm ι)

/-- The permutation automorphism `g ↦ g ∘ σ⁻¹` (so `(σ̂ g)(σ j) = g j`). -/
def permEquiv : (ι → H) ≃* (ι → H) where
  toFun g := g ∘ σ.symm
  invFun g := g ∘ σ
  left_inv g := by funext j; simp
  right_inv g := by funext j; simp
  map_mul' g g' := rfl

@[simp] lemma permEquiv_apply (g : ι → H) (j : ι) : permEquiv σ g j = g (σ.symm j) := rfl

lemma permEquiv_mul (σ τ : Equiv.Perm ι) :
    (permEquiv (σ * τ) : (ι → H) ≃* (ι → H)) = (permEquiv τ).trans (permEquiv σ) := by
  ext g j; simp [Equiv.Perm.mul_def]

variable (S : Sylow p H)

lemma map_permEquiv_piSylow :
    ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H)).map (permEquiv σ).toMonoidHom =
      (piSylow ι S : Sylow p (ι → H)) := by
  ext g
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (mem_piSub ι S).2 fun j => (mem_piSub ι S).1 hg _
  · intro hg
    refine ⟨(permEquiv σ).symm g, (mem_piSub ι S).2 fun j => (mem_piSub ι S).1 hg _, ?_⟩
    exact (permEquiv σ).apply_symm_apply g

end Perm

end AndersenOliverVentura.Tame
