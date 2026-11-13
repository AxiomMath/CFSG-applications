import Mathlib

/-!
# Group-theoretic facts for Gagola's splitting lemmas

* `exists_fixed_of_weight_sum`: a weighted count prime to `p` gives a fixed point of nonzero weight
  for an action in which every element acts with `p`-power order.
* `exists_pQuotient_of_not_mem_commutator`: a `p`-element outside the commutator subgroup gives a
  proper normal subgroup with `p`-group quotient.
* `exists_pQuotient_of_central`: **Burnside** — if a Sylow `p`-subgroup `P` is abelian and a nontrivial
  element of `P` centralizes `N(P)`, the group has a proper normal subgroup with `p`-group quotient.
* `transfer_eq_pow_of_normal`: the transfer to a normal subgroup at an element whose conjugates have
  the same image.
-/

namespace CFSGOutside.Gagola

open scoped BigOperators
open Classical

noncomputable section

section Weight

variable {P α : Type*} [Group P] [MulAction P α] [Fintype α] {p : ℕ} [hp : Fact p.Prime]

/-- **A weighted fixed-point count.** If every element of `P` acts with `p`-power order and the total
of an invariant weight is prime to `p`, some point of nonzero weight is fixed by `P`. -/
theorem exists_fixed_of_weight_sum (hP : ∀ g : P, ∃ k : ℕ, ∀ x : α, (g ^ p ^ k) • x = x)
    (w : α → ℕ) (hw : ∀ (g : P) x, w (g • x) = w x) (hsum : ¬ p ∣ ∑ x, w x) :
    ∃ x, w x ≠ 0 ∧ ∀ g : P, g • x = x := by
  by_contra hno
  push Not at hno
  apply hsum
  -- the image of `P` in `Perm α` is a `p`-group
  set Q := (MulAction.toPermHom P α).range with hQ
  have hQp : IsPGroup p Q := by
    rintro ⟨q, g, rfl⟩
    obtain ⟨k, hk⟩ := hP g
    refine ⟨k, Subtype.ext ?_⟩
    ext x
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one, Equiv.Perm.coe_one, id_eq]
    rw [← map_pow]
    exact hk x
  -- the sum splits over level sets
  have hsplit : ∑ x, w x = ∑ v ∈ Finset.univ.image w, v * Fintype.card {x // w x = v} := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := w) (t := Finset.univ.image w)
      (fun x _ => Finset.mem_image_of_mem w (Finset.mem_univ x))]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.sum_congr rfl fun x hx => (Finset.mem_filter.mp hx).2, Finset.sum_const,
      smul_eq_mul, mul_comm, Fintype.card_subtype]
  rw [hsplit]
  refine Finset.dvd_sum fun v _ => ?_
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · simp
  refine Dvd.dvd.mul_left ?_ v
  -- `Q` acts on the level set without fixed points
  letI : MulAction Q {x : α // w x = v} :=
    { smul q x := ⟨(q : Equiv.Perm α) x.1, by
        obtain ⟨g, hg⟩ := q.2
        rw [← hg]; exact (hw g x.1).trans x.2⟩
      one_smul x := Subtype.ext rfl
      mul_smul q r x := Subtype.ext rfl }
  have hmod := hQp.card_modEq_card_fixedPoints {x : α // w x = v}
  have hfix : IsEmpty (MulAction.fixedPoints Q {x : α // w x = v}) := by
    refine ⟨fun ⟨x, hx⟩ => ?_⟩
    obtain ⟨g, hg⟩ := hno x.1 (by rw [x.2]; exact hv.ne')
    apply hg
    have := hx ⟨MulAction.toPermHom P α g, g, rfl⟩
    exact congrArg Subtype.val this
  have h0 : Nat.card (MulAction.fixedPoints Q {x : α // w x = v}) = 0 := Nat.card_of_isEmpty
  rw [h0, Nat.card_eq_fintype_card] at hmod
  exact Nat.modEq_zero_iff_dvd.mp hmod

end Weight

section Quotient

variable {X : Type*} [Group X] [Finite X] {p : ℕ} [hp : Fact p.Prime]

/-- A `p`-element outside the commutator subgroup gives a proper normal subgroup with `p`-group
quotient. -/
theorem exists_pQuotient_of_not_mem_commutator {c : X} (hc : ∃ k : ℕ, c ^ p ^ k = 1)
    (hcX : c ∉ commutator X) :
    ∃ M : Subgroup X, ∃ _ : M.Normal, M ≠ ⊤ ∧ IsPGroup p (X ⧸ M) := by
  set m := ordCompl[p] (Nat.card X) with hm
  set f : X →* Abelianization X := (powMonoidHom m).comp Abelianization.of with hf
  have hX0 : Nat.card X ≠ 0 := Nat.card_pos.ne'
  refine ⟨f.ker, inferInstance, ?_, ?_⟩
  · intro htop
    have hc' : c ∈ f.ker := htop ▸ Subgroup.mem_top c
    rw [MonoidHom.mem_ker] at hc'
    simp only [hf, MonoidHom.coe_comp, Function.comp_apply, powMonoidHom_apply] at hc'
    -- `of c` has `p`-power order and `m` is prime to `p`
    obtain ⟨k, hk⟩ := hc
    have h1 : Abelianization.of c ^ p ^ k = 1 := by rw [← map_pow, hk, map_one]
    have hcop : Nat.Coprime (p ^ k) m := Nat.Coprime.pow_left k (Nat.coprime_ordCompl hp.out hX0)
    have hone : Abelianization.of c = 1 := by
      have := (pow_gcd_eq_one (a := Abelianization.of c)).mpr ⟨h1, hc'⟩
      rwa [hcop.gcd_eq_one, pow_one] at this
    apply hcX
    rw [← Abelianization.ker_of]
    exact hone
  · -- every element of the quotient has `p`-power order
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    refine ⟨(Nat.card X).factorization p, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, MonoidHom.mem_ker]
    simp only [hf, MonoidHom.coe_comp, Function.comp_apply, powMonoidHom_apply, ← map_pow, ← pow_mul]
    rw [show p ^ (Nat.card X).factorization p * m = Nat.card X from
      Nat.ordProj_mul_ordCompl_eq_self _ _, pow_card_eq_one', map_one]

theorem pow_eq_one_of_mem_sylow {P : Sylow p X} {c : X} (hc : c ∈ P) : ∃ k : ℕ, c ^ p ^ k = 1 := by
  obtain ⟨k, hk⟩ := P.isPGroup' ⟨c, hc⟩
  exact ⟨k, congrArg Subtype.val hk⟩

theorem eq_one_of_pow_index_eq_one {P : Sylow p X} {c : X} (hc : c ∈ P)
    (h : c ^ (P : Subgroup X).index = 1) : c = 1 := by
  obtain ⟨k, hk⟩ := pow_eq_one_of_mem_sylow hc
  have hcop : Nat.Coprime (p ^ k) (P : Subgroup X).index :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr P.not_dvd_index)
  have := (pow_gcd_eq_one (a := c)).mpr ⟨hk, h⟩
  rwa [hcop.gcd_eq_one, pow_one] at this

/-- **Burnside**: if a Sylow `p`-subgroup `P` is abelian and `1 ≠ c ∈ P` centralizes `N(P)`, then
the group has a proper normal subgroup with `p`-group quotient. -/
theorem exists_pQuotient_of_central (P : Sylow p X) (hab : IsMulCommutative (P : Subgroup X))
    {c : X} (hcP : c ∈ P) (hc1 : c ≠ 1)
    (hcN : ∀ n ∈ Subgroup.normalizer ((P : Subgroup X) : Set X), n * c = c * n) :
    ∃ M : Subgroup X, ∃ _ : M.Normal, M ≠ ⊤ ∧ IsPGroup p (X ⧸ M) := by
  refine exists_pQuotient_of_not_mem_commutator (pow_eq_one_of_mem_sylow hcP) fun hcX => hc1 ?_
  have hPc : (P : Subgroup X) ≤ Subgroup.centralizer (P : Set X) := by
    intro x hx y hy
    exact congrArg Subtype.val (hab.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
  have key : ∀ (k : ℕ) (g₀ : X), g₀⁻¹ * c ^ k * g₀ ∈ (P : Subgroup X) →
      g₀⁻¹ * c ^ k * g₀ = c ^ k := by
    intro k g₀ hk
    obtain ⟨n, hn, hn'⟩ := Sylow.conj_eq_normalizer_conj_of_mem_centralizer P (c ^ k) g₀
      (hPc ((P : Subgroup X).pow_mem hcP k)) (hPc hk)
    rw [hn']
    have hnc : n * c ^ k = c ^ k * n := (Commute.pow_right (hcN n hn) k).eq
    rw [mul_assoc, ← hnc, ← mul_assoc, inv_mul_cancel, one_mul]
  set ϕ : (P : Subgroup X) →* Abelianization (P : Subgroup X) := Abelianization.of
  have hV := MonoidHom.transfer_eq_pow ϕ c key
  have h1 : (ϕ.transfer c) = 1 := Abelianization.commutator_subset_ker _ hcX
  rw [h1] at hV
  have h2 : (⟨c ^ (P : Subgroup X).index, MonoidHom.transfer_eq_pow_aux c key⟩ :
      (P : Subgroup X)) ∈ commutator (P : Subgroup X) := by
    rw [← Abelianization.ker_of]; exact hV.symm
  have hbot : commutator (P : Subgroup X) = ⊥ := by
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _ y _
    exact hab.is_comm.comm y x
  rw [hbot, Subgroup.mem_bot] at h2
  exact eq_one_of_pow_index_eq_one hcP (congrArg Subtype.val h2)

/-- The transfer to a normal subgroup at an element whose conjugates all have the same image. -/
theorem transfer_eq_pow_of_normal {A : Type*} [CommGroup A] {N : Subgroup X} [N.Normal]
    (ϕ : N →* A) {c : X} (hc : c ∈ N)
    (hconj : ∀ g₀ : X, ϕ ⟨g₀⁻¹ * c * g₀, by simpa using ‹N.Normal›.conj_mem c hc g₀⁻¹⟩ = ϕ ⟨c, hc⟩) :
    ϕ.transfer c = ϕ ⟨c, hc⟩ ^ N.index := by
  classical
  let := N.fintypeQuotientOfFiniteIndex
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot, Subgroup.index_eq_sum_minimalPeriod N c,
    ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun q _ => ?_
  have hpow : ∀ (k : ℕ) (g₀ : X), ϕ ⟨g₀⁻¹ * c ^ k * g₀, by
      simpa using ‹N.Normal›.conj_mem _ (N.pow_mem hc k) g₀⁻¹⟩ = ϕ ⟨c, hc⟩ ^ k := by
    intro k g₀
    have e : (⟨g₀⁻¹ * c ^ k * g₀, by simpa using ‹N.Normal›.conj_mem _ (N.pow_mem hc k) g₀⁻¹⟩ : N) =
        (⟨g₀⁻¹ * c * g₀, by simpa using ‹N.Normal›.conj_mem c hc g₀⁻¹⟩ : N) ^ k := by
      ext
      simp only [SubgroupClass.coe_pow]
      have := conj_pow (a := g₀⁻¹) (b := c) (i := k)
      simpa using this.symm
    rw [e, map_pow, hconj]
  exact hpow _ _

end Quotient

end

end CFSGOutside.Gagola
