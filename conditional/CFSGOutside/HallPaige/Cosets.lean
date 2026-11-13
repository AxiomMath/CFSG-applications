import CFSGOutside.HallPaige.Statements
import Mathlib.Combinatorics.Hall.Basic

/-!
# Extending complete mappings along cosets

* `CFSGOutside.HallPaige.exists_left_right_transversal`: a subgroup of a finite group has a common left and
  right transversal (Hall's marriage theorem).
* `CFSGOutside.HallPaige.hasCompleteMapping_of_cosets`: **Wilcox, Proposition 14** (generalising Hall–Paige,
  Theorem 1).
* `CFSGOutside.HallPaige.hasCompleteMapping_of_normal`: Hall–Paige, Corollary 2 (the quotient lemma).
* `CFSGOutside.HallPaige.hasCompleteMapping_of_factorization`: Hall–Paige, Corollary 1 (exact factorisations).
-/

namespace CFSGOutside.HallPaige

open QuotientGroup

universe u

variable {G : Type*} [Group G]

/-- A subgroup `H` of a finite group has a common left and right transversal: a choice `t q ∈ q`
of a representative of each left coset `q` such that every `g` lies in `H * t q` for exactly one
`q`. -/
theorem exists_left_right_transversal [Finite G] (H : Subgroup G) :
    ∃ t : G ⧸ H → G, (∀ q, (t q : G ⧸ H) = q) ∧ ∀ g : G, ∃! q, g * (t q)⁻¹ ∈ H := by
  classical
  have := Fintype.ofFinite G
  let R := Quotient (QuotientGroup.rightRel H)
  let r : G ⧸ H → R → Prop := fun q p => ∃ g : G, (g : G ⧸ H) = q ∧ (⟦g⟧ : R) = p
  have hall : ∀ A : Finset (G ⧸ H), A.card ≤ (Finset.univ.filter fun p => ∃ q ∈ A, r q p).card := by
    intro A
    set B := Finset.univ.filter fun p => ∃ q ∈ A, r q p
    set S := Finset.univ.filter fun g : G => (g : G ⧸ H) ∈ A
    have h1 : (A ×ˢ (Finset.univ : Finset H)).card ≤ S.card := by
      refine Finset.card_le_card_of_injOn (fun x => x.1.out * x.2) ?_ ?_
      · intro x hx
        simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hx
        simp [S, QuotientGroup.mk_mul_of_mem _ x.2.2, hx.1]
      · rintro ⟨q, h⟩ - ⟨q', h'⟩ - he
        simp only at he
        have hq : q = q' := by
          have := congrArg (fun g : G => (g : G ⧸ H)) he
          simpa [QuotientGroup.mk_mul_of_mem _ h.2, QuotientGroup.mk_mul_of_mem _ h'.2] using this
        subst hq
        simpa using he
    have h2 : S.card ≤ (B ×ˢ (Finset.univ : Finset H)).card := by
      refine Finset.card_le_card_of_injOn
        (fun g => ((⟦g⟧ : R), (⟨g * (Quotient.out (⟦g⟧ : R))⁻¹, ?_⟩ : H))) ?_ ?_
      · have := Quotient.mk_out (s := QuotientGroup.rightRel H) g
        exact QuotientGroup.rightRel_apply.mp this
      · intro g hg
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, S] at hg
        simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.coe_univ,
          Set.mem_univ, and_true, B, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨_, hg, g, rfl, rfl⟩
      · intro g _ g' _ he
        simp only [Prod.mk.injEq, Subtype.mk.injEq] at he
        obtain ⟨h1, h2⟩ := he
        rw [h1] at h2
        simpa using h2
    have hH : 0 < (Finset.univ : Finset H).card := Finset.card_pos.mpr Finset.univ_nonempty
    rw [Finset.card_product] at h1 h2
    exact Nat.le_of_mul_le_mul_right (h1.trans h2) hH
  obtain ⟨f, hf, hfr⟩ := (Fintype.all_card_le_filter_rel_iff_exists_injective r).mp hall
  choose t ht htf using hfr
  have hcard : Nat.card R ≤ Nat.card (G ⧸ H) :=
    (Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel H)).le
  have hfs : Function.Surjective f := (hf.bijective_of_nat_card_le hcard).2
  refine ⟨t, ht, fun g => ?_⟩
  have key : ∀ q, g * (t q)⁻¹ ∈ H ↔ f q = ⟦g⟧ := by
    intro q
    rw [← htf q, Quotient.eq]
    exact QuotientGroup.rightRel_apply.symm
  obtain ⟨q, hq⟩ := hfs ⟦g⟧
  exact ⟨q, (key q).mpr hq, fun q' hq' => hf (((key q').mp hq').trans hq.symm)⟩

/-- **Wilcox, Proposition 14** (generalising Hall–Paige, Theorem 1). Let `H ≤ G` have a complete
mapping, and let `x y z : ι ≃ G ⧸ H` be bijections onto the left cosets with `z i ⊆ x i * y i`
(phrased with representatives) for all `i`. Then `G` has a complete mapping. -/
theorem hasCompleteMapping_of_cosets [Finite G] (H : Subgroup G) (hH : HasCompleteMapping H)
    {ι : Type*} (x y z : ι ≃ G ⧸ H)
    (hxyz : ∀ i, ∃ a b : G, (a : G ⧸ H) = x i ∧ (b : G ⧸ H) = y i ∧ ((a * b : G) : G ⧸ H) = z i) :
    HasCompleteMapping G := by
  obtain ⟨J, a, b, c, habc⟩ := (hasCompleteMapping_iff_exists_triple (G := H)).mp hH
  obtain ⟨t, ht, htu⟩ := exists_left_right_transversal H
  -- `s i ∈ x i` with `s i * t (y i) ∈ z i`
  have hs : ∀ i, ∃ s : G, (s : G ⧸ H) = x i ∧ ((s * t (y i) : G) : G ⧸ H) = z i := by
    intro i
    obtain ⟨g, k, hg, hk, hgk⟩ := hxyz i
    refine ⟨g, hg, ?_⟩
    rw [← hgk, QuotientGroup.eq]
    have : (t (y i))⁻¹ * k ∈ H := QuotientGroup.eq.mp ((ht _).trans hk.symm)
    simpa [mul_assoc] using this
  choose s hsx hsz using hs
  -- `t (y i) * a j = d i j * t (q i j)` with `d i j ∈ H`
  let q : ι → J → G ⧸ H := fun i j => (htu (t (y i) * a j)).exists.choose
  have hq : ∀ i j, t (y i) * a j * (t (q i j))⁻¹ ∈ H :=
    fun i j => (htu (t (y i) * a j)).exists.choose_spec
  have mk_mul : ∀ (g : G) {h : G}, h ∈ H → ((g * h : G) : G ⧸ H) = g :=
    fun g _ hh => QuotientGroup.mk_mul_of_mem g hh
  let A : ι × J → G := fun p => s p.1 * (t (y p.1) * a p.2 * (t (q p.1 p.2))⁻¹)
  let B : ι × J → G := fun p => t (q p.1 p.2) * b p.2
  let C : ι × J → G := fun p => s p.1 * t (y p.1) * c p.2
  have hcard : Nat.card G ≤ Nat.card (ι × J) := by
    rw [Nat.card_prod, Nat.card_congr x, Nat.card_congr a, ← H.index_mul_card]
    rfl
  have hA : Function.Injective A := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ he
    simp only [A] at he
    have hi : i = i' := by
      have := congrArg (fun g : G => (g : G ⧸ H)) he
      simp only [mk_mul _ (hq _ _)] at this
      exact x.injective ((hsx i).symm.trans (this.trans (hsx i')))
    subst hi
    have he' : t (q i j) * (a j : G)⁻¹ = t (q i j') * (a j' : G)⁻¹ := by
      have := mul_left_cancel he
      have := congrArg (fun g => g⁻¹ * t (y i)) this
      simpa [mul_assoc] using this
    have hqq : q i j = q i j' := by
      have := congrArg (fun g : G => (g : G ⧸ H)) he'
      simp only [mk_mul _ (H.inv_mem (a _).2), ht] at this
      exact this
    rw [hqq, mul_right_inj, inv_inj] at he'
    exact Prod.ext rfl (a.injective (Subtype.ext he'))
  have hB : Function.Injective B := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ he
    simp only [B] at he
    have hqq : q i j = q i' j' := by
      have := congrArg (fun g : G => (g : G ⧸ H)) he
      simpa only [mk_mul _ (b _).2, ht] using this
    rw [hqq, mul_right_inj] at he
    have hj : j = j' := b.injective (Subtype.ext he)
    subst hj
    have hi : y i = y i' := by
      refine (htu (t (y i))).unique (by simp [H.one_mem]) ?_
      have h1 := hq i j
      have h2 := hq i' j
      rw [hqq] at h1
      have := H.mul_mem h1 (H.inv_mem h2)
      simpa [mul_assoc] using this
    exact Prod.ext (y.injective hi) rfl
  have hC : Function.Injective C := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ he
    simp only [C] at he
    have hi : i = i' := by
      have := congrArg (fun g : G => (g : G ⧸ H)) he
      simp only [mk_mul _ (c _).2, hsz] at this
      exact z.injective this
    subst hi
    exact Prod.ext rfl (c.injective (Subtype.ext (mul_left_cancel he)))
  refine HasCompleteMapping.of_triple (Equiv.ofBijective A (hA.bijective_of_nat_card_le hcard))
    (Equiv.ofBijective B (hB.bijective_of_nat_card_le hcard))
    (Equiv.ofBijective C (hC.bijective_of_nat_card_le hcard)) ?_
  rintro ⟨i, j⟩
  simp only [Equiv.ofBijective_apply, A, B, C, ← habc j, Subgroup.coe_mul]
  group

/-- `CosetStatement` holds: see `hasCompleteMapping_of_cosets`. -/
theorem cosetStatement : CosetStatement.{u} :=
  fun H hH _ x y z hxyz => hasCompleteMapping_of_cosets H hH x y z hxyz

/-- **Hall–Paige, Corollary 2** (the quotient lemma). If `N ⊴ G` and both `N` and `G ⧸ N` have
complete mappings, then so does `G`. -/
theorem hasCompleteMapping_of_normal [Finite G] (N : Subgroup G) [N.Normal]
    (hN : HasCompleteMapping N) (hQ : HasCompleteMapping (G ⧸ N)) : HasCompleteMapping G := by
  obtain ⟨ι, a, b, c, habc⟩ := (hasCompleteMapping_iff_exists_triple (G := G ⧸ N)).mp hQ
  refine hasCompleteMapping_of_cosets N hN a b c fun i => ?_
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (a i)
  obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (b i)
  exact ⟨g, k, hg, hk, by rw [QuotientGroup.mk_mul, hg, hk, habc]⟩

/-- **Hall–Paige, Corollary 1** (exact factorisations). If `G = A * B` with `A ∩ B = 1` and both
`A` and `B` have complete mappings, then so does `G`. -/
theorem hasCompleteMapping_of_factorization [Finite G] (A B : Subgroup G) (hAB : A ⊓ B = ⊥)
    (hcard : Nat.card A * Nat.card B = Nat.card G)
    (hA : HasCompleteMapping A) (hB : HasCompleteMapping B) : HasCompleteMapping G := by
  obtain ⟨ι, a, b, c, habc⟩ := (hasCompleteMapping_iff_exists_triple (G := A)).mp hA
  -- the elements of `A` form a left transversal of `B`
  let f : A → G ⧸ B := fun g => ((g : G) : G ⧸ B)
  have hf : Function.Injective f := by
    intro g g' he
    have hmem : (g : G)⁻¹ * g' ∈ A ⊓ B :=
      ⟨A.mul_mem (A.inv_mem g.2) g'.2, QuotientGroup.eq.mp he⟩
    rw [hAB, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    exact Subtype.ext hmem
  have hle : Nat.card (G ⧸ B) ≤ Nat.card A := by
    have h := B.index_mul_card
    rw [← hcard] at h
    exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos h).le
  let e : A ≃ G ⧸ B := Equiv.ofBijective f (hf.bijective_of_nat_card_le hle)
  refine hasCompleteMapping_of_cosets B hB (a.trans e) (b.trans e) (c.trans e) fun i =>
    ⟨a i, b i, rfl, rfl, ?_⟩
  simp [e, f, ← habc i]

end CFSGOutside.HallPaige
