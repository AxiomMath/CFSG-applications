import CFSGOutside.AOVTame.WreathEquiv

/-!
# AOV tameness: the permutation of an automorphism of `L(ι → H)`

Under the hypothesis that every `α ∈ Aut_typ^I(L(ι → H))` permutes the coordinate subgroups, `α`
determines a permutation `σ_α` (unique when `S ≠ 1`), `α ↦ σ_α` is multiplicative and
class-invariant, and `α σ̂_α⁻¹` preserves coordinates.
-/

namespace AndersenOliverVentura.Tame

open Subgroup CategoryTheory

variable {p : ℕ} [hp : Fact p.Prime]
variable {H : Type} [Group H] [Finite H] {ι : Type} [Fintype ι] [DecidableEq ι] {S : Sylow p H}

/-- `α` permutes the coordinates via `σ`. -/
def PermBy {α : LAut p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))}
    (hα : α ∈ autTypI p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))) (σ : Equiv.Perm ι) :
    Prop :=
  ∀ (i : ι) (x : H) (hx : x ∈ (S : Subgroup H)),
    ∃ y, betaPi hα (Pi.mulSingle i x) (mulSingle_mem_piSub hx) = Pi.mulSingle (σ i) y

section
variable {α α' : LAut p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))}
  {hα : α ∈ autTypI p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))}
  {hα' : α' ∈ autTypI p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))}

lemma PermBy.unique (hS : (S : Subgroup H) ≠ ⊥) {σ τ : Equiv.Perm ι} (h : PermBy hα σ)
    (h' : PermBy hα τ) : σ = τ := by
  obtain ⟨⟨x, hx⟩, hx1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hS
  have hx1 : x ≠ 1 := fun h => hx1' (Subtype.ext h)
  ext i
  obtain ⟨y, hy⟩ := h i x hx
  obtain ⟨y', hy'⟩ := h' i x hx
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [Pi.mulSingle_one] at hy
    have : betaFun hα ⟨Pi.mulSingle i x, mulSingle_mem_piSub hx⟩ = betaFun hα 1 := by
      apply Subtype.ext
      change betaPi hα _ _ = betaPi hα 1 (one_mem _)
      rw [hy, betaPi_one]
    have h2 := congrArg Subtype.val (betaFun_injective hα this)
    have := congrFun h2 i
    simp at this
    exact hx1 this
  by_contra hne
  have := congrFun (hy.symm.trans hy') (σ i)
  rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hne] at this
  exact hy1 this

lemma PermBy.mul {σ σ' : Equiv.Perm ι} (h : PermBy hα σ) (h' : PermBy hα' σ') :
    PermBy (mul_mem hα hα') (σ * σ') := by
  intro i x hx
  obtain ⟨y, hy⟩ := h' i x hx
  have hyS : y ∈ (S : Subgroup H) := by
    have := (mem_piSub ι S).1 (betaPi_mem hα' (mulSingle_mem_piSub (i := i) hx)) (σ' i)
    rw [hy] at this; simpa using this
  obtain ⟨z, hz⟩ := h (σ' i) y hyS
  refine ⟨z, ?_⟩
  rw [betaPi_mul_aut (hα := hα) (hα' := hα')]
  exact (betaPi_congr hα hy _ (mulSingle_mem_piSub hyS)).trans hz

lemma permBy_permEquiv (σ : Equiv.Perm ι) :
    PermBy (mapAut_mem p (permEquiv σ) (map_permEquiv_piSylow σ S)) σ := by
  intro i x hx
  refine ⟨x, ?_⟩
  unfold betaPi
  rw [betaFun_mapIso]
  exact permEquiv_mulSingle σ i x

lemma permBy_conj (n : ι → H)
    (hn : ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H)).map (MulAut.conj n).toMonoidHom =
      (piSylow ι S : Sylow p (ι → H))) :
    PermBy (mapAut_mem p (MulAut.conj n) hn) 1 := by
  intro i x hx
  refine ⟨n i * x * (n i)⁻¹, ?_⟩
  unfold betaPi
  rw [betaFun_mapIso]
  funext j
  change n j * (Pi.mulSingle i x : ι → H) j * (n j)⁻¹ =
    (Pi.mulSingle ((1 : Equiv.Perm ι) i) (n i * x * (n i)⁻¹) : ι → H) j
  rw [Equiv.Perm.one_apply]
  by_cases hj : j = i
  · subst hj; simp
  · simp [Pi.mulSingle_eq_of_ne hj]

end

lemma mapAut_permEquiv_mul (σ τ : Equiv.Perm ι) :
    mapAut p (permEquiv (H := H) (σ * τ)) (map_permEquiv_piSylow (σ * τ) S) =
      mapAut p (permEquiv (H := H) σ) (map_permEquiv_piSylow σ S) *
        mapAut p (permEquiv (H := H) τ) (map_permEquiv_piSylow τ S) := by
  apply LAut.ext_fn
  rw [LAut.fn_mul, mapAut_fn, mapAut_fn, mapAut_fn, mapFunctor_comp]
  exact mapFunctor_congr p (permEquiv_mul σ τ) _ _

lemma mapAut_permEquiv_one :
    mapAut p (permEquiv (H := H) (1 : Equiv.Perm ι)) (map_permEquiv_piSylow 1 S) = 1 := by
  apply LAut.ext_fn
  rw [mapAut_fn, LAut.fn_one]
  rw [mapFunctor_congr p (show (permEquiv (1 : Equiv.Perm ι) : (ι → H) ≃* (ι → H)) = MulEquiv.refl _
    from by ext g j; rfl) _ (map_refl _), mapFunctor_refl]

lemma mapAut_permEquiv_inv (σ : Equiv.Perm ι) :
    mapAut p (permEquiv (H := H) σ⁻¹) (map_permEquiv_piSylow σ⁻¹ S) =
      (mapAut p (permEquiv (H := H) σ) (map_permEquiv_piSylow σ S))⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← mapAut_permEquiv_mul, inv_mul_cancel, mapAut_permEquiv_one]

lemma permConj_eq (σ : Equiv.Perm ι) (α : LAut p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))) :
    permConj σ α = mapAut p (permEquiv σ) (map_permEquiv_piSylow σ S) * α *
      (mapAut p (permEquiv σ) (map_permEquiv_piSylow σ S))⁻¹ :=
  conjIso_eq_mul _ _ α

end AndersenOliverVentura.Tame
