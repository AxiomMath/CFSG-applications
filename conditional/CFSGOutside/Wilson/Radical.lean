import CFSGOutside.Common.Components
import CFSGOutside.Corpus.Defs.PSolvable

/-!
# Wilson, compact torsion groups: the `p`-soluble radical

**Paper.** J. S. Wilson, *On the structure of compact torsion groups*, Monatsh. Math. **96** (1983), 57–66,
proof of Lemma 4(ii) (p. 64).

For a finite group `Z` the `p`-soluble radical `O_{p-sol}(Z)` is the largest normal `p`-soluble subgroup
(`exists_pSolRad`). The quotient `Z/O_{p-sol}(Z)` has no nontrivial normal `p`-soluble subgroup (`quot_no_pSol`),
so its Fitting subgroup is trivial and each of its components has order divisible by `p`
(`dvd_card_component`).
-/

namespace CFSGOutside.Wilson

open Subgroup CFSGOutside.Corpus CFSGOutside.Corpus.LocalCores

section Radical

open scoped Pointwise

variable {p : ℕ} [hp : Fact p.Prime] {Z : Type} [Group Z] [Finite Z]

/-- The join of two normal `p`-soluble subgroups is `p`-soluble. -/
theorem isPSolvable_sup {M₁ M₂ : Subgroup Z} [hM₁ : M₁.Normal] [hM₂ : M₂.Normal]
    (h₁ : IsPSolvable p M₁) (h₂ : IsPSolvable p M₂) : IsPSolvable p ↥(M₁ ⊔ M₂) := by
  set S := M₁ ⊔ M₂
  set M₁' := M₁.subgroupOf S
  have hM₁' : IsPSolvable p M₁' :=
    isPSolvable_of_mulEquiv (Subgroup.subgroupOfEquivOfLe le_sup_left).symm h₁
  let f : M₂ →* S ⧸ M₁' := (QuotientGroup.mk' M₁').comp (Subgroup.inclusion le_sup_right)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨⟨s, hs⟩, rfl⟩ := QuotientGroup.mk_surjective q
    have hs' : s ∈ ((M₁ : Set Z) * (M₂ : Set Z)) := by
      rw [← Subgroup.normal_mul]; exact hs
    obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := hs'
    refine ⟨⟨m₂, hm₂⟩, ?_⟩
    show QuotientGroup.mk _ = QuotientGroup.mk _
    rw [QuotientGroup.eq, mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
    have : m₂⁻¹ * (m₁ * m₂) = m₂⁻¹ * m₁ * m₂⁻¹⁻¹ := by group
    rw [this]
    exact hM₁.conj_mem m₁ hm₁ m₂⁻¹
  have hQ : IsPSolvable p (S ⧸ M₁') :=
    isPSolvable_of_mulEquiv (QuotientGroup.quotientKerEquivOfSurjective f hf)
      (isPSolvable_quotient h₂ _)
  exact isPSolvable_of_normal M₁' hM₁' hQ

/-- Existence of the `p`-soluble radical `O_{p-sol}(Z)`: the largest normal `p`-soluble subgroup. -/
theorem exists_pSolRad (p : ℕ) [Fact p.Prime] (Z : Type) [Group Z] [Finite Z] :
    ∃ R : Subgroup Z, R.Normal ∧ IsPSolvable p R ∧
      ∀ M : Subgroup Z, M.Normal → IsPSolvable p M → M ≤ R := by
  classical
  have : Finite (Subgroup Z) :=
    Finite.of_injective (fun K : Subgroup Z => (K : Set Z)) SetLike.coe_injective
  obtain ⟨R, ⟨hRn, hRp⟩, hRmax⟩ := Set.Finite.exists_maximalFor
    (fun K : Subgroup Z => Nat.card K) {K : Subgroup Z | K.Normal ∧ IsPSolvable p K}
    (Set.toFinite _) ⟨⊥, inferInstance, isPSolvable_of_isSolvable inferInstance⟩
  refine ⟨R, hRn, hRp, fun M hM hMp => ?_⟩
  have hsup : (R ⊔ M).Normal := Subgroup.sup_normal R M
  have hsp : IsPSolvable p ↥(R ⊔ M) := isPSolvable_sup hRp hMp
  have := hRmax ⟨hsup, hsp⟩ (Subgroup.card_le_of_le le_sup_left)
  have heq : R = R ⊔ M := Subgroup.eq_of_le_of_card_ge le_sup_left this
  rw [heq]
  exact le_sup_right

/-- The `p`-soluble radical is characteristic. -/
theorem pSolRad_characteristic {R : Subgroup Z} (hRp : IsPSolvable p R)
    (hRmax : ∀ M : Subgroup Z, M.Normal → IsPSolvable p M → M ≤ R) [hRn : R.Normal] :
    R.Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro φ
  apply hRmax
  · exact hRn.map φ.toMonoidHom φ.surjective
  · exact isPSolvable_of_mulEquiv (R.equivMapOfInjective φ.toMonoidHom φ.injective) hRp

end Radical

section Quot

variable {p : ℕ} [hp : Fact p.Prime] {Z : Type} [Group Z] [Finite Z]

/-- The order of a join of pairwise commuting subgroups divides the product of the orders. -/
theorem card_sSup_dvd {G : Type} [Group G] [Finite G] : ∀ (𝒯 : Finset (Subgroup G)),
    (∀ T ∈ 𝒯, ∀ T' ∈ 𝒯, T ≠ T' → ∀ x ∈ T, ∀ y ∈ T', x * y = y * x) →
    Nat.card ↥(sSup (𝒯 : Set (Subgroup G))) ∣ ∏ T ∈ 𝒯, Nat.card T := by
  classical
  intro 𝒯
  induction 𝒯 using Finset.induction_on with
  | empty => intro _; simp
  | insert T 𝒯 hT ih =>
    intro hcomm
    rw [Finset.coe_insert, sSup_insert, Finset.prod_insert hT]
    set A := sSup (𝒯 : Set (Subgroup G))
    have hA := ih (fun S hS S' hS' => hcomm S (Finset.mem_insert_of_mem hS) S'
      (Finset.mem_insert_of_mem hS'))
    have hAT : A ≤ centralizer (T : Set G) := by
      refine sSup_le fun S hS => ?_
      intro y hy
      rw [mem_centralizer_iff]
      intro x hx
      have hS' : S ∈ 𝒯 := by exact_mod_cast hS
      exact hcomm T (Finset.mem_insert_self _ _) S (Finset.mem_insert_of_mem hS')
        (fun h => hT (h ▸ hS')) x hx y hy
    have hcomm' : ∀ (a : T) (b : A), Commute (T.subtype a) (A.subtype b) := fun a b =>
      (mem_centralizer_iff.1 (hAT b.2) a a.2)
    have hrange : (MonoidHom.noncommCoprod T.subtype A.subtype hcomm').range = T ⊔ A := by
      rw [MonoidHom.noncommCoprod_range, range_subtype, range_subtype]
    have hdvd : Nat.card ↥(T ⊔ A) ∣ Nat.card T * Nat.card A := by
      rw [← hrange, ← Nat.card_prod]
      exact Subgroup.card_range_dvd _
    exact hdvd.trans (Nat.mul_dvd_mul_left _ hA)

variable {R : Subgroup Z} [hRn : R.Normal] (hRp : IsPSolvable p R)
  (hRmax : ∀ M : Subgroup Z, M.Normal → IsPSolvable p M → M ≤ R)
include hRp hRmax

/-- `Z/O_{p-sol}(Z)` has no nontrivial normal `p`-soluble subgroup. -/
theorem quot_no_pSol : ∀ S : Subgroup (Z ⧸ R), S.Normal → IsPSolvable p S → S = ⊥ := by
  intro S hSn hSp
  set L := S.comap (QuotientGroup.mk' R)
  have hLn : L.Normal := hSn.comap _
  have hRL : R ≤ L := fun r hr => by
    show QuotientGroup.mk' R r ∈ S
    rw [show QuotientGroup.mk' R r = 1 from (QuotientGroup.eq_one_iff r).mpr hr]
    exact S.one_mem
  have hR' : IsPSolvable p (R.subgroupOf L) :=
    isPSolvable_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hRL).symm hRp
  let f : L →* S := ((QuotientGroup.mk' R).comp L.subtype).codRestrict S (fun x => x.2)
  have hf : Function.Surjective f := by
    rintro ⟨s, hs⟩
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective s
    exact ⟨⟨z, hs⟩, rfl⟩
  have hker : f.ker = R.subgroupOf L := by
    ext x
    simp only [f, MonoidHom.mem_ker, mem_subgroupOf]
    rw [Subtype.ext_iff]
    exact QuotientGroup.eq_one_iff (x : Z)
  have hQ : IsPSolvable p (L ⧸ R.subgroupOf L) :=
    isPSolvable_of_mulEquiv ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)).symm hSp
  have hLp : IsPSolvable p L := isPSolvable_of_normal (R.subgroupOf L) hR' hQ
  have hLR := hRmax L hLn hLp
  rw [eq_bot_iff]
  intro s hs
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective s
  exact (QuotientGroup.eq_one_iff z).mpr (hLR hs)

/-- `Z/O_{p-sol}(Z)` has trivial Fitting subgroup. -/
theorem fitting_quot_eq_bot : fittingSubgroup (Z ⧸ R) = ⊥ := by
  rw [fittingSubgroup, sSup_eq_bot]
  rintro N ⟨hN, hNnil⟩
  exact quot_no_pSol hRp hRmax N hN (isPSolvable_of_isSolvable inferInstance)

/-- Every component of `Z/O_{p-sol}(Z)` has order divisible by `p`. -/
theorem dvd_card_component {C : Subgroup (Z ⧸ R)} (hC : IsComponent C) : p ∣ Nat.card C := by
  classical
  have : Fintype (Z ⧸ R) := Fintype.ofFinite _
  have hF := fitting_quot_eq_bot hRp hRmax
  by_contra hpC
  set 𝒯 : Finset (Subgroup (Z ⧸ R)) := Finset.univ.image fun y => C.map (MulAut.conj y).toMonoidHom
  have hmem : ∀ D ∈ 𝒯, ∃ y : Z ⧸ R, D = C.map (MulAut.conj y).toMonoidHom := by
    intro D hD
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hD
    exact ⟨y, rfl⟩
  have hcomp : ∀ D ∈ 𝒯, IsComponent D := by
    intro D hD
    obtain ⟨y, rfl⟩ := hmem D hD
    exact isComponent_conj hC y
  have hcard : ∀ D ∈ 𝒯, Nat.card D = Nat.card C := by
    intro D hD
    obtain ⟨y, rfl⟩ := hmem D hD
    exact Subgroup.card_map_of_injective (MulAut.conj y).injective
  set J := sSup (𝒯 : Set (Subgroup (Z ⧸ R)))
  have hJdvd := card_sSup_dvd 𝒯 fun D hD D' hD' hne =>
    component_commute (hcomp D hD) (hcomp D' hD') hne
  have hcop : Nat.Coprime p (Nat.card J) := by
    refine Nat.Coprime.coprime_dvd_right hJdvd ?_
    refine Nat.Coprime.prod_right fun D hD => ?_
    rw [hcard D hD]
    exact (Nat.Prime.coprime_iff_not_dvd hp.out).mpr hpC
  have hJn : J.Normal := by
    refine ⟨fun x hx g => ?_⟩
    have : J ≤ J.comap (MulAut.conj g).toMonoidHom := by
      refine sSup_le fun D hD => ?_
      intro d hd
      rw [mem_comap]
      have hD' : D ∈ 𝒯 := by exact_mod_cast hD
      obtain ⟨y, rfl⟩ := hmem D hD'
      have hmem2 : C.map (MulAut.conj (g * y)).toMonoidHom ∈ 𝒯 :=
        Finset.mem_image.mpr ⟨g * y, Finset.mem_univ _, rfl⟩
      refine le_sSup (show C.map (MulAut.conj (g * y)).toMonoidHom ∈
        (𝒯 : Set (Subgroup (Z ⧸ R))) by exact_mod_cast hmem2) ?_
      obtain ⟨c, hc, rfl⟩ := mem_map.mp hd
      exact ⟨c, hc, by simp [MulAut.conj_apply, mul_assoc]⟩
    exact this hx
  have hJ := quot_no_pSol hRp hRmax J hJn (isPSolvable_of_coprime hcop)
  have hCJ : C ≤ J := by
    refine le_sSup (show C ∈ (𝒯 : Set (Subgroup (Z ⧸ R))) from ?_)
    have : C.map (MulAut.conj (1 : Z ⧸ R)).toMonoidHom ∈ 𝒯 :=
      Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
    have hC1 : C.map (MulAut.conj (1 : Z ⧸ R)).toMonoidHom = C := by ext; simp
    rw [hC1] at this
    exact_mod_cast this
  have hsimp := component_isSimple hF hC
  have : Nontrivial C := hsimp.toNontrivial
  apply (C.nontrivial_iff_ne_bot.mp this)
  rw [eq_bot_iff, ← hJ]
  exact hCJ

end Quot

end CFSGOutside.Wilson
