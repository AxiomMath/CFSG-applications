import CFSGOutside.HallPaige.Statements
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Transfer
import Mathlib.GroupTheory.PGroup

/-!
# Reduction of Hall–Paige sufficiency to simple groups

Wilcox, Theorem 12, in a form needing neither the Feit–Thompson theorem nor the solvable case:
assuming four ingredient lemmas (stated here as `Prop`s), a finite group satisfying the
Hall–Paige condition has a complete mapping as soon as every simple such group does (given that
its proper good subgroups are admissible).

The proof is a strong induction on `Nat.card G`, using a nontrivial proper normal subgroup `N`:
* a nontrivial normal subgroup of odd order is split off by `NormalQuotientStatement`;
* 2-groups are treated directly (central involutions, and `Z₂ × Z₂` by hand);
* if `N` and `G ⧸ N` are good, `NormalQuotientStatement`;
* if `G ⧸ N` is bad, it has a normal subgroup of index 2 (Burnside transfer), whose preimage is
  good and is handled by `IndexTwoStatement`;
* if `N` is bad, it is a cyclic 2-group (its normal 2-complement is normal in `G`), so `G` has a
  central involution `z`, and `G ⧸ ⟨z⟩` is good, so `CentralTwoStatement` applies.
-/

namespace CFSGOutside.HallPaige

universe u

open Subgroup

/-! ### The ingredient statements -/

/-- Normal subgroup and quotient admissible implies the group admissible. -/
def NormalQuotientStatement : Prop :=
  ∀ {G : Type u} [Group G] [Finite G] (N : Subgroup G) [N.Normal],
    HasCompleteMapping N → HasCompleteMapping (G ⧸ N) → HasCompleteMapping G

/-- An exact factorisation `G = A B` into admissible subgroups is admissible. -/
def FactorizationStatement : Prop :=
  ∀ {G : Type u} [Group G] [Finite G] (A B : Subgroup G),
    A ⊓ B = ⊥ → Nat.card A * Nat.card B = Nat.card G →
      HasCompleteMapping A → HasCompleteMapping B → HasCompleteMapping G

/-- A good group with a normal subgroup of order 2 and admissible quotient is admissible. -/
def CentralTwoStatement : Prop :=
  ∀ {G : Type u} [Group G] [Finite G], IsGood G → ∀ (N : Subgroup G) [N.Normal],
    Nat.card N = 2 → HasCompleteMapping (G ⧸ N) → HasCompleteMapping G

/-- A good group with an admissible normal subgroup of index 2 is admissible. -/
def IndexTwoStatement : Prop :=
  ∀ {G : Type u} [Group G] [Finite G], IsGood G → ∀ (N : Subgroup G) [N.Normal],
    N.index = 2 → HasCompleteMapping N → HasCompleteMapping G

/-! ### Elementary facts about good groups -/

section Good

variable {X : Type*} [Group X] [Finite X]

/-- A group of odd order is good. -/
theorem isGood_of_odd (h : Odd (Nat.card X)) : IsGood X := by
  intro P
  left
  have h2 : ¬ 2 ∣ Nat.card X := by
    rintro ⟨m, hm⟩; rw [hm] at h; exact (Nat.not_even_iff_odd.mpr h) (even_two_mul m)
  rw [← Subgroup.card_eq_one, P.card_eq_multiplicity, Nat.factorization_eq_zero_of_not_dvd h2,
    pow_zero]

/-- If a non-cyclic 2-group embeds in `X`, then `X` is good. -/
theorem isGood_of_injective {Y : Type*} [Group Y] (hY : IsPGroup 2 Y) (hc : ¬ IsCyclic Y)
    (f : Y →* X) (hf : Function.Injective f) : IsGood X := by
  intro P
  right
  intro hP
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow
    (hY.of_surjective f.rangeRestrict f.rangeRestrict_surjective)
  have hQc : IsCyclic (Q : Subgroup X) := (MulEquiv.isCyclic (Sylow.equiv P Q)).mp hP
  have : IsCyclic (f.range.subgroupOf Q) := inferInstance
  have : IsCyclic f.range := (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hQ)).mp this
  exact hc ((MulEquiv.isCyclic (MonoidHom.ofInjective hf)).mpr this)

/-- A non-cyclic 2-group is good. -/
theorem isGood_of_isPGroup_of_not_isCyclic (hX : IsPGroup 2 X) (hc : ¬ IsCyclic X) : IsGood X :=
  isGood_of_injective hX hc (MonoidHom.id X) Function.injective_id

/-- A good group of even order has a non-cyclic Sylow 2-subgroup. -/
theorem IsGood.exists_sylow_not_isCyclic (hX : IsGood X) (h2 : 2 ∣ Nat.card X) :
    ∃ P : Sylow 2 X, ¬ IsCyclic P := by
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 X))
  exact ⟨P, (hX P).resolve_left (P.ne_bot_of_dvd_card h2)⟩

omit [Finite X] in
/-- A nontrivial good 2-group is not cyclic. -/
theorem IsGood.not_isCyclic_of_isPGroup (hX : IsGood X) (hp : IsPGroup 2 X) [Nontrivial X] :
    ¬ IsCyclic X := by
  intro hc
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 X))
  have hP : (P : Subgroup X) = ⊤ := (P.3 (hp.to_subgroup ⊤) le_top).symm
  rcases hX P with h | h
  · exact bot_ne_top (h.symm.trans hP)
  · exact h inferInstance

/-- A subgroup containing a good subgroup of even order is good. -/
theorem isGood_of_le {N H : Subgroup X} (hle : N ≤ H) (hN : IsGood N) (h2 : 2 ∣ Nat.card N) :
    IsGood H := by
  obtain ⟨P, hP⟩ := hN.exists_sylow_not_isCyclic h2
  refine isGood_of_injective P.2 hP ((Subgroup.inclusion hle).comp (P : Subgroup N).subtype) ?_
  exact (Subgroup.inclusion_injective hle).comp (Subgroup.subtype_injective _)

/-- The quotient of a good group by a normal subgroup of odd order is good. -/
theorem isGood_quotient_of_odd (hX : IsGood X) (L : Subgroup X) [L.Normal]
    (hL : Odd (Nat.card L)) : IsGood (X ⧸ L) := by
  by_cases h2 : 2 ∣ Nat.card X
  · obtain ⟨P, hP⟩ := hX.exists_sylow_not_isCyclic h2
    refine isGood_of_injective P.2 hP ((QuotientGroup.mk' L).comp (P : Subgroup X).subtype) ?_
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp P.2
    have hbot : (P : Subgroup X) ⊓ L = ⊥ := by
      apply Disjoint.eq_bot
      apply Subgroup.disjoint_of_coprime_natCard
      rw [hk]
      exact (Nat.coprime_two_left.mpr hL).pow_left k
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxL : (x : X) ∈ L := (QuotientGroup.eq_one_iff _).mp hx
    have : (x : X) ∈ (P : Subgroup X) ⊓ L := ⟨x.2, hxL⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact Subtype.ext this
  · apply isGood_of_odd
    have hodd : Odd (Nat.card X) := by
      rcases Nat.even_or_odd (Nat.card X) with h | h
      · exact absurd (even_iff_two_dvd.mp h) h2
      · exact h
    rw [L.card_eq_card_quotient_mul_card_subgroup] at hodd
    exact (Nat.odd_mul.mp hodd).1

/-- A group of order `2 * m` with `m` odd is bad (its Sylow 2-subgroups have order 2). -/
theorem not_isGood_of_card_eq_two_mul (m : ℕ) (hm : Odd m) (h : Nat.card X = 2 * m) :
    ¬ IsGood X := by
  intro hX
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 X))
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hm2 : ¬ 2 ∣ m := by
    rintro ⟨r, rfl⟩; exact (Nat.not_even_iff_odd.mpr hm) (even_two_mul r)
  have hcard : Nat.card P = 2 := by
    rw [P.card_eq_multiplicity, h, Nat.factorization_mul two_ne_zero hm0, Finsupp.add_apply,
      Nat.prime_two.factorization_self, Nat.factorization_eq_zero_of_not_dvd hm2, add_zero,
      pow_one]
  rcases hX P with h' | h'
  · rw [← Subgroup.card_eq_one, hcard] at h'; exact absurd h' (by norm_num)
  · exact h' (isCyclic_of_prime_card hcard)

end Good

/-! ### Bad groups have normal 2-complements -/

section Bad

variable {X : Type*} [Group X] [Finite X]

/-- **Burnside's transfer theorem for `p = 2`.** A bad group `X` has a cyclic Sylow 2-subgroup `P`
of order `2 ^ k` with `k > 0` and a surjection `X → P` whose kernel has odd order. -/
theorem exists_hom_of_not_isGood (h : ¬ IsGood X) :
    ∃ (P : Subgroup X) (φ : X →* P), IsCyclic P ∧ Function.Surjective φ ∧
      Odd (Nat.card φ.ker) ∧ ∃ k, 0 < k ∧ Nat.card P = 2 ^ k ∧
        Nat.card X = Nat.card φ.ker * 2 ^ k := by
  simp only [IsGood, not_forall, not_or, not_not] at h
  obtain ⟨P, hbot, hcyc⟩ := h
  have hP := P.card_eq_multiplicity
  set k := (Nat.card X).factorization 2
  have hk : 0 < k := by
    rw [Nat.pos_iff_ne_zero]
    intro hk0
    rw [hk0, pow_zero, Subgroup.card_eq_one] at hP
    exact hbot hP
  have h2 : 2 ∣ Nat.card X := by
    have := (P : Subgroup X).card_subgroup_dvd_card
    rw [hP] at this
    exact (dvd_pow_self 2 hk.ne').trans this
  have hc := IsCyclic.isComplement' ((Nat.minFac_eq_two_iff _).mpr h2) hcyc
  set φ := MonoidHom.transferSylow P (hcyc.normalizer_le_centralizer
    ((Nat.minFac_eq_two_iff _).mpr h2))
  have hmul := hc.card_mul_card
  rw [hP] at hmul
  have hX0 : Nat.card X ≠ 0 := Nat.card_pos.ne'
  refine ⟨P, φ, hcyc, ?_, ?_, k, hk, hP, hmul.symm⟩
  · -- `φ` is injective on `P` (as `ker φ ⊓ P = ⊥`), hence surjective by counting
    have hrange : φ.range = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv] at h1
      rw [hP]
      have hpos : 0 < Nat.card φ.ker := Nat.card_pos
      have : Nat.card φ.range * Nat.card φ.ker = 2 ^ k * Nat.card φ.ker := by
        rw [← h1, ← hmul, mul_comm]
      exact Nat.eq_of_mul_eq_mul_right hpos this
    exact MonoidHom.range_eq_top.mp hrange
  · rcases Nat.even_or_odd (Nat.card φ.ker) with he | ho
    · exfalso
      obtain ⟨r, hr⟩ := he
      have hd : 2 ^ (k + 1) ∣ Nat.card X := ⟨r, by rw [← hmul, hr, pow_succ]; ring⟩
      exact Nat.pow_succ_factorization_not_dvd hX0 Nat.prime_two hd
    · exact ho

/-- A bad group has a normal subgroup of index 2. -/
theorem exists_normal_index_two_of_not_isGood (h : ¬ IsGood X) :
    ∃ H : Subgroup X, H.Normal ∧ H.index = 2 := by
  obtain ⟨P, φ, hcyc, hsurj, -, k, hk, hP, -⟩ := exists_hom_of_not_isGood h
  obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime (G := P) 2 (n := k - 1)
    (by rw [hP]; exact Nat.pow_dvd_pow 2 (Nat.sub_le k 1))
  have hQi : Q.index = 2 := by
    have := Q.card_mul_index
    rw [hQ, hP] at this
    have hk' : 2 ^ k = 2 ^ (k - 1) * 2 := by
      rw [← pow_succ, Nat.sub_add_cancel hk]
    rw [hk'] at this
    exact Nat.eq_of_mul_eq_mul_left (by positivity) this
  refine ⟨Q.comap φ, (Subgroup.normal_of_isMulCommutative Q).comap φ, ?_⟩
  rw [Subgroup.index_comap_of_surjective Q hsurj, hQi]

/-- The normal 2-complement of a bad normal subgroup `N ⊴ G` is normal in `G`: there is a normal
subgroup `L` of `G` of odd order with `|N| = |L| * 2 ^ k`, `k > 0`, and `N` is cyclic if `L = ⊥`. -/
theorem exists_normal_odd_of_not_isGood {G : Type*} [Group G] [Finite G] (N : Subgroup G)
    [hN : N.Normal] (h : ¬ IsGood N) :
    ∃ L : Subgroup G, L.Normal ∧ Odd (Nat.card L) ∧ ∃ k, 0 < k ∧
      Nat.card N = Nat.card L * 2 ^ k ∧ (L = ⊥ → IsCyclic N) := by
  obtain ⟨P, φ, hcyc, hsurj, hodd, k, hk, hP, hcard⟩ := exists_hom_of_not_isGood h
  -- elements of `N` of odd order lie in `ker φ`, and conversely
  have key : ∀ y : N, Odd (orderOf y) → φ y = 1 := by
    intro y hy
    rw [← orderOf_eq_one_iff]
    have h1 : orderOf (φ y) ∣ 2 ^ k := hP ▸ _root_.orderOf_dvd_natCard (φ y)
    have h2 : orderOf (φ y) ∣ orderOf y := orderOf_map_dvd φ y
    exact Nat.Coprime.eq_one_of_dvd
      ((Nat.coprime_two_left.mpr (hy.of_dvd_nat h2)).pow_left k).symm h1
  have mem : ∀ y ∈ φ.ker, Odd (orderOf y) := by
    intro y hy
    rw [← Subgroup.orderOf_mk y hy]
    exact hodd.of_dvd_nat (_root_.orderOf_dvd_natCard _)
  have hLc : Nat.card (φ.ker.map N.subtype) = Nat.card φ.ker :=
    Subgroup.card_map_of_injective N.subtype_injective
  refine ⟨φ.ker.map N.subtype, ⟨fun x hx g => ?_⟩, hLc ▸ hodd, k, hk, hLc ▸ hcard, fun hL => ?_⟩
  · obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    refine ⟨⟨g * y * g⁻¹, hN.conj_mem y y.2 g⟩, key _ ?_, rfl⟩
    have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective (y : G)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
    rw [Subgroup.orderOf_mk, this, Subgroup.orderOf_coe]
    exact mem y hy
  · have hk1 : φ.ker = ⊥ := by
      rw [← Subgroup.card_eq_one, ← hLc, hL, Subgroup.card_bot]
    have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hk1
    exact (MulEquiv.isCyclic (MulEquiv.ofBijective φ ⟨hinj, hsurj⟩)).mpr hcyc

end Bad

/-! ### Involutions -/

section Involutions

variable {G : Type*} [Group G]

/-- The subgroup generated by an involution `x` is `{1, x}`. -/
theorem mem_zpowers_of_orderOf_eq_two {x y : G} (hx : orderOf x = 2) (hy : y ∈ zpowers x) :
    y = 1 ∨ y = x := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [← zpow_mod_orderOf, hx]
  push_cast
  rcases Int.emod_two_eq_zero_or_one i with h | h <;> simp [h]

/-- Powers of an element `g` with `g * g = 1` are `1` or `g`. -/
theorem pow_eq_one_or_self_of_mul_self {g : G} (hg : g * g = 1) (b : ℕ) : g ^ b = 1 ∨ g ^ b = g := by
  induction b with
  | zero => simp
  | succ b ih =>
    rcases ih with h | h
    · right; rw [pow_succ, h, one_mul]
    · left; rw [pow_succ, h, hg]

/-- The cyclic subgroup generated by a central element is normal. -/
theorem zpowers_normal_of_central {z : G} (hz : ∀ g, g * z * g⁻¹ = z) : (zpowers z).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
  rw [← conj_zpow, hz]
  exact zpow_mem (mem_zpowers z) i

/-- A cyclic normal subgroup of even order contains a central involution. -/
theorem exists_central_of_isCyclic [Finite G] (N : Subgroup G) [hN : N.Normal] (hc : IsCyclic N)
    (h2 : 2 ∣ Nat.card N) : ∃ z : G, orderOf z = 2 ∧ ∀ g, g * z * g⁻¹ = z := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := N) 2 h2
  refine ⟨x, by rw [Subgroup.orderOf_coe, hx], fun g => ?_⟩
  let y : N := ⟨g * x * g⁻¹, hN.conj_mem x x.2 g⟩
  have hy : orderOf y = 2 := by
    have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective (x : G)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
    rw [Subgroup.orderOf_mk, this, Subgroup.orderOf_coe, hx]
  have hzp : zpowers y = zpowers x := IsCyclic.subgroup_eq_iff_card_eq.mpr
    (by rw [Nat.card_zpowers, Nat.card_zpowers, hy, hx])
  have hmem : y ∈ zpowers x := hzp ▸ mem_zpowers y
  rcases mem_zpowers_of_orderOf_eq_two hx hmem with h1 | h1
  · rw [h1, orderOf_one] at hy; norm_num at hy
  · exact congrArg Subtype.val h1

end Involutions

/-! ### Cardinalities -/

section Card

variable {G : Type*} [Group G] [Finite G]

/-- A proper subgroup is smaller than the group. -/
theorem card_lt_of_ne_top {K : Subgroup G} (h : K ≠ ⊤) : Nat.card K < Nat.card G := by
  have h1 := K.card_mul_index
  have h2 : K.index ≠ 1 := mt Subgroup.index_eq_one.mp h
  have h3 : K.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h4 : 0 < Nat.card K := Nat.card_pos
  have h5 : 2 ≤ K.index := by omega
  rw [← h1]
  nlinarith

/-- The quotient by a nontrivial normal subgroup is smaller than the group. -/
theorem card_quotient_lt {N : Subgroup G} (h : N ≠ ⊥) : Nat.card (G ⧸ N) < Nat.card G := by
  have h1 := N.card_eq_card_quotient_mul_card_subgroup
  have h2 := (Subgroup.one_lt_card_iff_ne_bot N).mpr h
  have h3 : 0 < Nat.card (G ⧸ N) := Nat.card_pos
  rw [h1]
  nlinarith

omit [Finite G] in
/-- A subgroup of order 2 is nontrivial. -/
theorem ne_bot_of_card_eq_two {N : Subgroup G} (h : Nat.card N = 2) : N ≠ ⊥ := by
  rintro rfl
  rw [Subgroup.card_bot] at h
  norm_num at h

end Card

/-- If `G` is not a 2-group and has no nontrivial normal subgroup of odd order, then its quotient
by a normal subgroup of order 2 is good. -/
theorem isGood_quotient_of_card_eq_two {G : Type*} [Group G] [Finite G]
    (hp : ¬ IsPGroup 2 G) (hodd : ∀ L : Subgroup G, L.Normal → Odd (Nat.card L) → L = ⊥)
    (Z : Subgroup G) [Z.Normal] (hZ : Nat.card Z = 2) : IsGood (G ⧸ Z) := by
  by_contra h
  obtain ⟨P, φ, -, -, hodd', k, -, -, hcard⟩ := exists_hom_of_not_isGood h
  let K := φ.ker.comap (QuotientGroup.mk' Z)
  have hK : Nat.card K = 2 * Nat.card φ.ker := by
    rw [← hZ]
    exact QuotientGroup.card_preimage_mk Z φ.ker
  have : K.Normal := Subgroup.Normal.comap inferInstance _
  obtain ⟨L, hLn, hLodd, j, -, hj, -⟩ :=
    exists_normal_odd_of_not_isGood K (not_isGood_of_card_eq_two_mul _ hodd' hK)
  rw [hodd L hLn hLodd, Subgroup.card_bot, one_mul, hK] at hj
  have hc1 : Nat.card φ.ker = 1 :=
    Nat.Coprime.eq_one_of_dvd ((Nat.coprime_two_left.mpr hodd').pow_left j).symm
      ⟨2, by rw [← hj]; ring⟩
  apply hp
  apply IsPGroup.of_card (n := k + 1)
  rw [Z.card_eq_card_quotient_mul_card_subgroup, hcard, hc1, hZ, one_mul, pow_succ]

/-! ### 2-groups -/

/-- A non-cyclic group of order 4 has a complete mapping. -/
theorem hasCompleteMapping_of_card_four {G : Type*} [Group G] [Finite G]
    (hcomm : ∀ a b : G, a * b = b * a) (z g : G) (hz : z * z = 1) (hg : g * g = 1)
    (hgen : ∀ x : G, x = 1 ∨ x = z ∨ x = g ∨ x = z * g) (hcard : Nat.card G = 4) :
    HasCompleteMapping G := by
  let a : Bool × Bool → G := fun p => (if p.1 then z else 1) * (if p.2 then g else 1)
  have ha : Function.Bijective a := by
    apply Function.Surjective.bijective_of_nat_card_le
    · intro x
      rcases hgen x with rfl | rfl | rfl | rfl
      · exact ⟨(false, false), by simp [a]⟩
      · exact ⟨(true, false), by simp [a]⟩
      · exact ⟨(false, true), by simp [a]⟩
      · exact ⟨(true, true), by simp [a]⟩
    · rw [hcard]; simp
  let σ : Bool × Bool ≃ Bool × Bool :=
    Equiv.ofBijective (fun p => (p.2, xor p.1 p.2)) (by decide)
  let τ : Bool × Bool ≃ Bool × Bool :=
    Equiv.ofBijective (fun p => (xor p.1 p.2, p.1)) (by decide)
  let A := Equiv.ofBijective a ha
  have e1 : g * (z * g) = z := by rw [hcomm z g, ← mul_assoc, hg, one_mul]
  have e2 : z * g * z = g := by rw [hcomm z g, mul_assoc, hz, mul_one]
  refine HasCompleteMapping.of_triple A (σ.trans A) (τ.trans A) ?_
  rintro ⟨i, j⟩
  cases i <;> cases j <;> simp [A, σ, τ, a, e1, e2]

/-- Inside the induction: a good 2-group has a complete mapping, given `CentralTwoStatement` and
complete mappings for smaller good groups. -/
theorem hasCompleteMapping_of_isPGroup (hC2 : CentralTwoStatement.{u}) {G : Type u} [Group G]
    [Finite G]
    (IH : ∀ (H : Type u) [Group H] [Finite H], Nat.card H < Nat.card G → IsGood H →
      HasCompleteMapping H)
    (hG : IsGood G) (hp : IsPGroup 2 G) [Nontrivial G] : HasCompleteMapping G := by
  have hnc := hG.not_isCyclic_of_isPGroup hp
  -- a central involution `z`
  obtain ⟨z, hzc, hzo⟩ : ∃ z : G, z ∈ center G ∧ orderOf z = 2 := by
    have := hp.center_nontrivial
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hp.to_subgroup (center G))
    have hn0 : n ≠ 0 := by
      rintro rfl
      have := Finite.one_lt_card_iff_nontrivial.mpr ‹Nontrivial (center G)›
      rw [hn, pow_zero] at this
      exact lt_irrefl _ this
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := center G) 2
      (by rw [hn]; exact dvd_pow_self 2 hn0)
    exact ⟨x, x.2, by rw [Subgroup.orderOf_coe, hx]⟩
  have hz1 : z ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hzo; norm_num at hzo
  have hz2 : z ^ 2 = 1 := hzo ▸ pow_orderOf_eq_one z
  have hcent : ∀ g, g * z * g⁻¹ = z := fun g => by
    rw [Subgroup.mem_center_iff.mp hzc g, mul_inv_cancel_right]
  have : (zpowers z).Normal := zpowers_normal_of_central hcent
  have hZ : Nat.card (zpowers z) = 2 := by rw [Nat.card_zpowers, hzo]
  by_cases hq : IsGood (G ⧸ zpowers z)
  · exact hC2 hG (zpowers z) hZ (IH _ (card_quotient_lt (ne_bot_of_card_eq_two hZ)) hq)
  -- otherwise `G ⧸ ⟨z⟩` is cyclic, so `G` is abelian, `G = ⟨z⟩ × ⟨g⟩`
  have hqp : IsPGroup 2 (G ⧸ zpowers z) := hp.to_quotient _
  have hqc : IsCyclic (G ⧸ zpowers z) :=
    by_contra fun h => hq (isGood_of_isPGroup_of_not_isCyclic hqp h)
  have hcomm : ∀ a b : G, a * b = b * a := by
    have := MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center (QuotientGroup.mk' (zpowers z))
      (by rw [QuotientGroup.ker_mk']; exact zpowers_le.mpr hzc)
    exact fun a b => this.is_comm.comm a b
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hqp
  have hGc : Nat.card G = 2 ^ (n + 1) := by
    rw [(zpowers z).card_eq_card_quotient_mul_card_subgroup, hn, hZ, pow_succ]
  obtain ⟨gq, hgq⟩ := IsCyclic.exists_generator (α := G ⧸ zpowers z)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective gq
  have hog : orderOf (g : G ⧸ zpowers z) = 2 ^ n := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hgq, hn]
  have hdec : ∀ x : G, ∃ b : ℕ, x = g ^ b ∨ x = z * g ^ b := by
    intro x
    obtain ⟨b, hb⟩ := (Submonoid.mem_powers_iff _ _).mp
      (mem_powers_iff_mem_zpowers.mpr (hgq (x : G ⧸ zpowers z)))
    have : ((g ^ b : G) : G ⧸ zpowers z) = x := by rw [QuotientGroup.mk_pow, hb]
    rcases mem_zpowers_of_orderOf_eq_two hzo (QuotientGroup.eq.mp this) with h | h
    · exact ⟨b, Or.inl (inv_mul_eq_one.mp h).symm⟩
    · exact ⟨b, Or.inr (by rw [inv_mul_eq_iff_eq_mul.mp h, hcomm])⟩
  have hgn : g ^ (2 ^ n) = 1 := by
    have : ((g ^ (2 ^ n) : G) : G ⧸ zpowers z) = 1 := by
      rw [QuotientGroup.mk_pow, ← hog, pow_orderOf_eq_one]
    rcases mem_zpowers_of_orderOf_eq_two hzo ((QuotientGroup.eq_one_iff _).mp this) with h | h
    · exact h
    · exfalso
      apply hnc
      apply isCyclic_of_orderOf_eq_card g
      rw [hGc]
      apply orderOf_eq_prime_pow
      · rw [h]; exact hz1
      · rw [pow_succ, pow_mul, h, hz2]
  rcases n with _ | _ | m
  · exact absurd (isCyclic_of_prime_card (p := 2) (by rw [hGc]; rfl)) hnc
  · -- `|G| = 4`
    refine hasCompleteMapping_of_card_four hcomm z g (by rw [← sq, hz2])
      (by rw [← sq]; simpa using hgn) (fun x => ?_) (by rw [hGc]; rfl)
    have hg2 : g * g = 1 := by rw [← sq]; simpa using hgn
    obtain ⟨b, hb | hb⟩ := hdec x <;>
      rcases pow_eq_one_or_self_of_mul_self hg2 b with h | h <;> rw [h] at hb <;> simp [hb]
  · -- `|G| ≥ 8`: use the involution `z' = g ^ (|G| / 4)` instead
    set z' := g ^ (2 ^ (m + 1))
    have hz'o : orderOf z' = 2 := by
      apply orderOf_eq_prime
      · rw [← pow_mul, ← pow_succ, hgn]
      · intro h1
        have : (g : G ⧸ zpowers z) ^ (2 ^ (m + 1)) = 1 := by
          rw [← QuotientGroup.mk_pow, show g ^ 2 ^ (m + 1) = 1 from h1, QuotientGroup.mk_one]
        exact pow_ne_one_of_lt_orderOf (by positivity)
          (by rw [hog]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)) this
    have : (zpowers z').Normal :=
      zpowers_normal_of_central (fun h => by rw [hcomm h z', mul_inv_cancel_right])
    have hZ' : Nat.card (zpowers z') = 2 := by rw [Nat.card_zpowers, hz'o]
    have hq'c : Nat.card (G ⧸ zpowers z') = 2 ^ (m + 2) := by
      have := (zpowers z').card_eq_card_quotient_mul_card_subgroup
      rw [hZ', hGc, pow_succ] at this
      exact (Nat.eq_of_mul_eq_mul_right (by norm_num) this).symm
    have hzpow : z ^ (2 ^ (m + 1)) = 1 := by rw [pow_succ', pow_mul, hz2, one_pow]
    have hgpow : ∀ b : ℕ, (g ^ b) ^ (2 ^ (m + 1)) ∈ zpowers z' := by
      intro b
      rw [← pow_mul, mul_comm, pow_mul]
      exact pow_mem (mem_zpowers z') b
    have hexp : ∀ y : G ⧸ zpowers z', y ^ (2 ^ (m + 1)) = 1 := by
      intro y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      obtain ⟨b, hb | hb⟩ := hdec x
      · rw [hb]; exact hgpow b
      · rw [hb, Commute.mul_pow (hcomm z (g ^ b)), hzpow, one_mul]; exact hgpow b
    have hq'nc : ¬ IsCyclic (G ⧸ zpowers z') := by
      intro hc
      obtain ⟨y, hy⟩ := IsCyclic.exists_generator (α := G ⧸ zpowers z')
      have h1 := orderOf_eq_card_of_forall_mem_zpowers hy
      have h2 := orderOf_dvd_of_pow_eq_one (hexp y)
      rw [h1, hq'c] at h2
      exact absurd (Nat.le_of_dvd (by positivity) h2)
        (not_le.mpr (Nat.pow_lt_pow_right (by norm_num) (by omega)))
    refine hC2 hG (zpowers z') hZ' (IH _ ?_ (isGood_of_isPGroup_of_not_isCyclic
      (hp.to_quotient _) hq'nc))
    rw [hq'c, hGc]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)

/-! ### The reduction -/

/-- **Reduction to simple groups** (Wilcox, Theorem 12, restructured). Given the ingredient
lemmas `NormalQuotientStatement`, `CentralTwoStatement` and `IndexTwoStatement`, if every good
simple group whose proper good subgroups are admissible is admissible, then every good finite
group is admissible. (`FactorizationStatement` is not needed.) -/
theorem hasCompleteMapping_of_isGood_of_simple'
    (hNQ : NormalQuotientStatement.{u}) (hC2 : CentralTwoStatement.{u})
    (hI2 : IndexTwoStatement.{u})
    (hsimple : ∀ (G : Type u) [Group G] [Finite G], IsSimpleGroup G → IsGood G →
      ProperSubgroupsAdmissible G → HasCompleteMapping G)
    (G : Type u) [Group G] [Finite G] (hG : IsGood G) : HasCompleteMapping G := by
  suffices h : ∀ n (G : Type u) [Group G] [Finite G], Nat.card G = n → IsGood G →
      HasCompleteMapping G from h _ G rfl hG
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ _ hn hG
  have IH : ∀ (H : Type u) [Group H] [Finite H], Nat.card H < Nat.card G → IsGood H →
      HasCompleteMapping H := fun H _ _ hlt hH => ih _ (hn ▸ hlt) H rfl hH
  clear ih hn
  by_cases hodd : Odd (Nat.card G)
  · exact hasCompleteMapping_of_odd hodd
  -- split off a nontrivial normal subgroup of odd order
  by_cases h1 : ∃ L : Subgroup G, L.Normal ∧ Odd (Nat.card L) ∧ L ≠ ⊥
  · obtain ⟨L, hLn, hLo, hL⟩ := h1
    exact hNQ L (hasCompleteMapping_of_odd hLo)
      (IH _ (card_quotient_lt hL) (isGood_quotient_of_odd hG L hLo))
  have h1' : ∀ L : Subgroup G, L.Normal → Odd (Nat.card L) → L = ⊥ :=
    fun L hn ho => by_contra fun h => h1 ⟨L, hn, ho, h⟩
  have h2G : 2 ∣ Nat.card G := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  have : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp (by
    have := Nat.card_pos (α := G)
    obtain ⟨r, hr⟩ := h2G
    omega)
  by_cases hp : IsPGroup 2 G
  · exact hasCompleteMapping_of_isPGroup hC2 IH hG hp
  by_cases hs : IsSimpleGroup G
  · exact hsimple G hs hG (fun K hK hKg => IH K (card_lt_of_ne_top hK) hKg)
  obtain ⟨N, hNn, hNb, hNt⟩ : ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ := by
    by_contra h
    push Not at h
    exact hs { toNontrivial := inferInstance
               eq_bot_or_eq_top_of_normal := fun H hH => by
                 by_cases hb : H = ⊥
                 · exact Or.inl hb
                 · exact Or.inr (h H hH hb) }
  have := hNn
  by_cases hNg : IsGood N
  · by_cases hQg : IsGood (G ⧸ N)
    · exact hNQ N (IH N (card_lt_of_ne_top hNt) hNg) (IH _ (card_quotient_lt hNb) hQg)
    -- `G ⧸ N` is bad: pass to a good normal subgroup of index 2
    have h2N : 2 ∣ Nat.card N := by
      rcases Nat.even_or_odd (Nat.card N) with h | h
      · exact even_iff_two_dvd.mp h
      · exact absurd (h1' N hNn h) hNb
    obtain ⟨Hb, hHbn, hHbi⟩ := exists_normal_index_two_of_not_isGood hQg
    let H := Hb.comap (QuotientGroup.mk' N)
    have : H.Normal := hHbn.comap _
    have hHi : H.index = 2 := by
      rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective N), hHbi]
    have hle : N ≤ H := fun x hx => by
      rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
      exact one_mem _
    have hHt : H ≠ ⊤ := fun h => by rw [h, Subgroup.index_top] at hHi; norm_num at hHi
    exact hI2 hG H hHi (IH H (card_lt_of_ne_top hHt) (isGood_of_le hle hNg h2N))
  -- `N` is bad, hence a cyclic 2-group: it contains a central involution `z`
  obtain ⟨L, hLn, hLo, k, hk, hNc, hcyc⟩ := exists_normal_odd_of_not_isGood N hNg
  have hL := h1' L hLn hLo
  rw [hL, Subgroup.card_bot, one_mul] at hNc
  obtain ⟨z, hzo, hz⟩ :=
    exists_central_of_isCyclic N (hcyc hL) (by rw [hNc]; exact dvd_pow_self 2 hk.ne')
  have : (zpowers z).Normal := zpowers_normal_of_central hz
  have hZ : Nat.card (zpowers z) = 2 := by rw [Nat.card_zpowers, hzo]
  exact hC2 hG (zpowers z) hZ (IH _ (card_quotient_lt (ne_bot_of_card_eq_two hZ))
    (isGood_quotient_of_card_eq_two hp h1' _ hZ))

end CFSGOutside.HallPaige
