import CFSGOutside.ChillagSonn.Lemma19B
import CFSGOutside.ChillagSonn.Case1
import CFSGOutside.ChillagSonn.Covers

/-!
# Lemma (1.9): the Sylow statements, and the exceptional case `A ≅ SL(2, 5)`

Let `G = N A` be Sylow-metacyclic with `N ⊴ G` of odd order and `N ∩ A = 1`, and let `q` divide `|A|` and `|N|`.

* The Sylow `q`-subgroup `P` of `G` containing a Sylow `q`-subgroup `R` of `A` is `(P ∩ N) R`, and Lemma (1.2) shows
  that `P ∩ N` and `R` are cyclic. So the Sylow `q`-subgroups of `A` and of `N` are cyclic.
* If the `q`-elements of `A` act trivially on `N/L` for some `L` of order prime to `q`, then `R` centralizes the
  `q`-group `P ∩ N`, which it normalizes, and `P` is abelian.

For a quasisimple `A` with `|Z(A)| ≤ 2`, `A` centralizes `N` unless `|Z(A)| = 2` and `|A/Z(A)| = 60`, which for the
stem extensions of Lemma (1.5) means `A ≅ SL(2, 5)`. In that case `A` still centralizes `N/L`, `L` the normal Hall
subgroup of `N` for the primes `≥ 7`, which is enough for the Sylow statements.
-/

namespace CFSGOutside.ChillagSonn

open CFSGOutside.Corpus CFSGOutside.Corpus.GorensteinWalter
open scoped MatrixGroups

section Helpers

variable {G : Type} [Group G]

/-- `|H ⊔ K| = |H| |K|` for `K` normal and `H ∩ K = 1`. -/
theorem card_sup_of_normal [Finite G] (H K : Subgroup G) [K.Normal] (h : H ⊓ K = ⊥) :
    Nat.card (H ⊔ K : Subgroup G) = Nat.card H * Nat.card K := by
  have h1 := Subgroup.relIndex_mul_card K H
  have h2 := Subgroup.relIndex_mul_card K (H ⊔ K)
  rw [inf_comm, h, Subgroup.card_bot, mul_one] at h1
  rw [inf_of_le_left le_sup_right, Subgroup.relIndex_sup_right, h1] at h2
  exact h2.symm

theorem isMulCommutative_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) [h : IsMulCommutative Y] :
    IsMulCommutative X :=
  ⟨⟨fun a b => e.injective (by simp only [map_mul]; exact h.is_comm.comm _ _)⟩⟩

theorem mul_comm_of_isCyclic {X : Type*} [Group X] (h : IsCyclic X) (a b : X) : a * b = b * a := by
  let := IsCyclic.commGroup (α := X)
  exact mul_comm a b

/-- `|N/L| |L| = |N|`. -/
theorem card_map_mk_mul {N L : Subgroup G} [L.Normal] (hLN : L ≤ N) :
    Nat.card (N.map (QuotientGroup.mk' L)) * Nat.card L = Nat.card N := by
  have hker : ((QuotientGroup.mk' L).subgroupMap N).ker = L.subgroupOf N := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val h)
    · intro h
      exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr h)
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (L.subgroupOf N)
  rw [← hker, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
    (MonoidHom.subgroupMap_surjective _ _)).toEquiv, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLN).toEquiv] at h1
  exact h1.symm

theorem not_dvd_upperPart_of_lt {q t n : ℕ} (hq : q.Prime) (hqt : q < t) : ¬ q ∣ upperPart t n := by
  rw [upperPart]
  intro h
  obtain ⟨p, hp, hqp⟩ := (Prime.dvd_finsetProd_iff hq.prime _).mp h
  rw [Finset.mem_filter, Nat.mem_primeFactors] at hp
  have := (Nat.prime_dvd_prime_iff_eq hq hp.1.1).mp (hq.dvd_of_dvd_pow hqp)
  omega

/-- If `n = upperPart t n * m`, the primes dividing `m` are `< t`. -/
theorem lt_of_dvd_of_upperPart {t n m r : ℕ} (hn : n ≠ 0) (h : upperPart t n * m = n) (hr : r.Prime)
    (hrm : r ∣ m) : r < t := by
  by_contra hlt
  push Not at hlt
  have hrn : r ∣ n := h ▸ Dvd.dvd.mul_left hrm _
  have hmem : r ∈ n.primeFactors.filter (t ≤ ·) :=
    Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hr, hrn, hn⟩, hlt⟩
  have h1 : r ^ n.factorization r ∣ upperPart t n := Finset.dvd_prod_of_mem (fun q => q ^ n.factorization q) hmem
  have h2 : r ^ (n.factorization r + 1) ∣ n := by
    rw [pow_succ]
    conv_rhs => rw [← h]
    exact mul_dvd_mul h1 hrm
  exact Nat.pow_succ_factorization_not_dvd hn hr h2

/-- A `q`-element (`q` odd) of `A` lies in any `C` with `|A : A ∩ C| ≤ 2`. -/
theorem mem_of_relIndex_le_two [Finite G] {C A : Subgroup G} (h : C.relIndex A ≤ 2) {q : ℕ} [Fact q.Prime]
    (hq2 : q ≠ 2) {a : G} (ha : a ∈ A) (hk : ∃ k : ℕ, a ^ (q ^ k) = 1) : a ∈ C := by
  obtain ⟨k, hk⟩ := hk
  have hsq : a ^ 2 ∈ C := by
    have h0 : (C.subgroupOf A).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    change (C.subgroupOf A).index ≤ 2 at h
    rcases (show (C.subgroupOf A).index = 1 ∨ (C.subgroupOf A).index = 2 by omega) with h1 | h2
    · have : (⟨a, ha⟩ : A) ∈ C.subgroupOf A := by
        rw [Subgroup.index_eq_one.mp h1]
        exact Subgroup.mem_top _
      exact C.pow_mem (Subgroup.mem_subgroupOf.mp this) 2
    · exact Subgroup.mem_subgroupOf.mp (Subgroup.sq_mem_of_index_two h2 ⟨a, ha⟩)
  have hodd : Odd (q ^ k) := (Nat.Prime.odd_of_ne_two Fact.out hq2).pow
  obtain ⟨m, hm⟩ := hodd
  have : a = (a ^ 2) ^ (m + 1) := by
    rw [← pow_mul]
    calc a = a ^ (q ^ k) * a := by rw [hk, one_mul]
      _ = a ^ (2 * (m + 1)) := by rw [← pow_succ, hm, show 2 * m + 1 + 1 = 2 * (m + 1) by ring]
  rw [this]
  exact C.pow_mem hsq _

end Helpers

section Sylow

variable {G : Type} [Group G] [Finite G]

/-- The Sylow `q`-subgroup `P` of `G = N A` containing a Sylow `q`-subgroup `R` of `A` is `(P ∩ N) R`, and both
factors are cyclic (Lemma (1.2)). -/
theorem exists_sylow_sup [FrattiniElementaryQuotient.{0}] (hG : SylowMetacyclic G) (N A : Subgroup G) [N.Normal]
    (hinf : N ⊓ A = ⊥) (hsup : N ⊔ A = ⊤) (hodd : Odd (Nat.card N)) {q : ℕ} [Fact q.Prime]
    (hqA : q ∣ Nat.card A) (hqN : q ∣ Nat.card N) (R : Sylow q A) :
    ∃ P : Sylow q G, (R : Subgroup A).map A.subtype ≤ P ∧
      (P : Subgroup G) ⊓ N ⊔ (R : Subgroup A).map A.subtype = P ∧
      IsCyclic ((P : Subgroup G) ⊓ N : Subgroup G) ∧ IsCyclic ((R : Subgroup A).map A.subtype) := by
  classical
  have hq : q.Prime := Fact.out
  have hq2 : q ≠ 2 := fun h => by
    rw [h] at hqN
    exact Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr hqN)
  have hR'p : IsPGroup q ((R : Subgroup A).map A.subtype) := R.isPGroup'.map _
  obtain ⟨P, hRP⟩ := hR'p.exists_le_sylow
  obtain ⟨Q₀, hQ₀⟩ := exists_sylow_map_eq_inf P N
  have hNpos : Nat.card N ≠ 0 := Nat.card_pos.ne'
  have hApos : Nat.card A ≠ 0 := Nat.card_pos.ne'
  have hcardPN : Nat.card ((P : Subgroup G) ⊓ N : Subgroup G) = q ^ (Nat.card N).factorization q := by
    rw [← hQ₀, Subgroup.card_map_of_injective N.subtype_injective, Sylow.card_eq_multiplicity]
  have hcardR' : Nat.card ((R : Subgroup A).map A.subtype) = q ^ (Nat.card A).factorization q := by
    rw [Subgroup.card_map_of_injective A.subtype_injective, Sylow.card_eq_multiplicity]
  have hcardG : Nat.card G = Nat.card A * Nat.card N := by
    rw [← card_sup_of_normal A N (by rw [inf_comm, hinf]), sup_comm, hsup, Subgroup.card_top]
  have hcardP : Nat.card (P : Subgroup G) =
      q ^ (Nat.card A).factorization q * q ^ (Nat.card N).factorization q := by
    rw [Sylow.card_eq_multiplicity, hcardG, Nat.factorization_mul hApos hNpos, Finsupp.add_apply, pow_add]
  set P₁ : Subgroup P := N.subgroupOf P with hP₁def
  set P₂ : Subgroup P := ((R : Subgroup A).map A.subtype).subgroupOf P with hP₂def
  have : P₁.Normal := Subgroup.normal_subgroupOf
  have hP₁ : P₁.map (P : Subgroup G).subtype = (P : Subgroup G) ⊓ N := by
    rw [hP₁def, Subgroup.subgroupOf_map_subtype, inf_comm]
  have hP₂ : P₂.map (P : Subgroup G).subtype = (R : Subgroup A).map A.subtype := by
    rw [hP₂def, Subgroup.subgroupOf_map_subtype, inf_of_le_left hRP]
  have hcard₁ : Nat.card P₁ = q ^ (Nat.card N).factorization q := by
    rw [← Subgroup.card_map_of_injective (P : Subgroup G).subtype_injective, hP₁, hcardPN]
  have hcard₂ : Nat.card P₂ = q ^ (Nat.card A).factorization q := by
    rw [← Subgroup.card_map_of_injective (P : Subgroup G).subtype_injective, hP₂, hcardR']
  have hinf₁₂ : P₂ ⊓ P₁ = ⊥ := by
    apply Subgroup.map_injective (P : Subgroup G).subtype_injective
    rw [Subgroup.map_inf_eq _ _ _ (P : Subgroup G).subtype_injective, hP₁, hP₂, Subgroup.map_bot, eq_bot_iff]
    rintro x ⟨hxR, -, hxN⟩
    rw [← hinf]
    exact ⟨hxN, Subgroup.map_subtype_le _ hxR⟩
  have hsup₁₂ : P₂ ⊔ P₁ = ⊤ := by
    refine Subgroup.eq_top_of_card_eq _ ?_
    rw [card_sup_of_normal P₂ P₁ hinf₁₂, hcard₁, hcard₂, hcardP]
  have hpow_ne : ∀ n : ℕ, n ≠ 0 → q ∣ n → q ^ n.factorization q ≠ 1 := fun n hn hqn h => by
    have := Nat.one_lt_pow (hq.factorization_pos_of_dvd hn hqn).ne' hq.one_lt
    omega
  have h₁ : P₁ ≠ ⊥ := fun h => hpow_ne _ hNpos hqN (by rw [← hcard₁, h, Subgroup.card_bot])
  have h₂ : P₂ ≠ ⊥ := fun h => hpow_ne _ hApos hqA (by rw [← hcard₂, h, Subgroup.card_bot])
  have hPp : IsPGroup q (P : Subgroup G) := P.isPGroup'
  have hPm : IsMetacyclic (P : Subgroup G) := hG.isMetacyclic_of_isPGroup P hPp
  have hs : P₁ ⊔ P₂ = ⊤ := by rw [sup_comm]; exact hsup₁₂
  have hi : P₁ ⊓ P₂ = ⊥ := by rw [inf_comm]; exact hinf₁₂
  have hc₂ := lemma_1_2_a hPp hPm P₁ P₂ hs hi h₁
  have hc₁ := lemma_1_2_b hq2 hPp hPm P₁ P₂ hs hi h₂
  refine ⟨P, hRP, ?_, ?_, ?_⟩
  · have := congrArg (Subgroup.map (P : Subgroup G).subtype) hsup₁₂
    rw [Subgroup.map_sup, hP₁, hP₂, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at this
    rw [sup_comm]
    exact this
  · let e : P₁ ≃* ((P : Subgroup G) ⊓ N : Subgroup G) :=
      (P₁.equivMapOfInjective _ (P : Subgroup G).subtype_injective).trans (MulEquiv.subgroupCongr hP₁)
    exact isCyclic_of_injective e.symm.toMonoidHom e.symm.injective
  · let e : P₂ ≃* ((R : Subgroup A).map A.subtype) :=
      (P₂.equivMapOfInjective _ (P : Subgroup G).subtype_injective).trans (MulEquiv.subgroupCongr hP₂)
    exact isCyclic_of_injective e.symm.toMonoidHom e.symm.injective

/-- **Lemma (1.9)**, Sylow statements: if `q` divides `|A|` and `|N|`, the Sylow `q`-subgroups of `A` and `N` are
cyclic; if moreover the `q`-elements of `A` act trivially on `N` modulo some `L` of order prime to `q`, the Sylow
`q`-subgroups of `G` are abelian. -/
theorem sylow_claims [FrattiniElementaryQuotient.{0}] (hG : SylowMetacyclic G) (N A : Subgroup G) [N.Normal]
    (hinf : N ⊓ A = ⊥) (hsup : N ⊔ A = ⊤) (hodd : Odd (Nat.card N)) {q : ℕ} [Fact q.Prime]
    (hqA : q ∣ Nat.card A) (hqN : q ∣ Nat.card N) (L : Subgroup G) (hLq : ¬ q ∣ Nat.card L)
    (htriv : ∀ a ∈ A, (∃ k : ℕ, a ^ (q ^ k) = 1) → ∀ x ∈ N, a * x * a⁻¹ * x⁻¹ ∈ L) :
    (∀ Q : Sylow q G, IsMulCommutative Q) ∧ (∀ Q : Sylow q A, IsCyclic Q) ∧ (∀ Q : Sylow q N, IsCyclic Q) := by
  classical
  have hq : q.Prime := Fact.out
  obtain ⟨R⟩ : Nonempty (Sylow q A) := inferInstance
  obtain ⟨P, hRP, hPeq, hc₁, hc₂⟩ := exists_sylow_sup hG N A hinf hsup hodd hqA hqN R
  obtain ⟨Q₀, hQ₀⟩ := exists_sylow_map_eq_inf P N
  have hcR : IsCyclic (R : Subgroup A) := by
    have := hc₂
    exact isCyclic_of_injective
      ((R : Subgroup A).equivMapOfInjective A.subtype A.subtype_injective).toMonoidHom (MulEquiv.injective _)
  have hcQ₀ : IsCyclic (Q₀ : Subgroup N) := by
    have := hc₁
    exact isCyclic_of_injective (((Q₀ : Subgroup N).equivMapOfInjective N.subtype N.subtype_injective).trans
      (MulEquiv.subgroupCongr hQ₀)).toMonoidHom (MulEquiv.injective _)
  refine ⟨?_, fun Q => ?_, fun Q => ?_⟩
  rotate_left
  · have := hcR
    exact isCyclic_of_injective (Sylow.equiv Q R).toMonoidHom (MulEquiv.injective _)
  · have := hcQ₀
    exact isCyclic_of_injective (Sylow.equiv Q Q₀).toMonoidHom (MulEquiv.injective _)
  -- `R` centralizes `P ∩ N`
  have hPNcard : Nat.card ((P : Subgroup G) ⊓ N : Subgroup G) = q ^ (Nat.card N).factorization q := by
    rw [← hQ₀, Subgroup.card_map_of_injective N.subtype_injective, Sylow.card_eq_multiplicity]
  have hcop : ((P : Subgroup G) ⊓ N) ⊓ L = ⊥ := Subgroup.inf_eq_bot_of_coprime (by
    rw [hPNcard]
    exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hq).mpr hLq))
  have hcomm : ∀ a ∈ (R : Subgroup A).map A.subtype, ∀ x ∈ (P : Subgroup G) ⊓ N, a * x = x * a := by
    intro a ha x hx
    have haP : a ∈ (P : Subgroup G) := hRP ha
    have hc : a * x * a⁻¹ * x⁻¹ ∈ ((P : Subgroup G) ⊓ N) ⊓ L := by
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact (P : Subgroup G).mul_mem ((P : Subgroup G).mul_mem ((P : Subgroup G).mul_mem haP hx.1)
          ((P : Subgroup G).inv_mem haP)) ((P : Subgroup G).inv_mem hx.1)
      · exact N.mul_mem ((inferInstance : N.Normal).conj_mem x hx.2 a) (N.inv_mem hx.2)
      · obtain ⟨a', ha', rfl⟩ := ha
        refine htriv _ a'.2 ?_ x hx.2
        obtain ⟨k, hk⟩ := R.isPGroup' ⟨a', ha'⟩
        exact ⟨k, by simpa using congrArg Subtype.val (congrArg Subtype.val hk)⟩
    rw [hcop, Subgroup.mem_bot] at hc
    calc a * x = (a * x * a⁻¹ * x⁻¹) * (x * a) := by group
      _ = x * a := by rw [hc, one_mul]
  have hPN_comm : ∀ x y : ((P : Subgroup G) ⊓ N : Subgroup G), x * y = y * x := mul_comm_of_isCyclic hc₁
  have hR_comm : ∀ x y : ((R : Subgroup A).map A.subtype : Subgroup G), x * y = y * x :=
    mul_comm_of_isCyclic hc₂
  have h1 : ((P : Subgroup G) ⊓ N : Subgroup G) ≤ Subgroup.centralizer (P : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) := by
      rw [← hPeq]
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro u hu
        rw [Set.mem_singleton_iff.mp hu]
        exact congrArg Subtype.val (hPN_comm ⟨x, hx⟩ ⟨y, hy⟩)
      · rw [Subgroup.mem_centralizer_iff]
        intro u hu
        rw [Set.mem_singleton_iff.mp hu]
        exact (hcomm y hy x hx).symm
    exact (Subgroup.mem_centralizer_iff.mp (this hz) x rfl).symm
  have h2 : (R : Subgroup A).map A.subtype ≤ Subgroup.centralizer (P : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have : (P : Subgroup G) ≤ Subgroup.centralizer ({y} : Set G) := by
      rw [← hPeq]
      refine sup_le (fun x hx => ?_) (fun w hw => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro u hu
        rw [Set.mem_singleton_iff.mp hu]
        exact hcomm y hy x hx
      · rw [Subgroup.mem_centralizer_iff]
        intro u hu
        rw [Set.mem_singleton_iff.mp hu]
        exact congrArg Subtype.val (hR_comm ⟨y, hy⟩ ⟨w, hw⟩)
    exact (Subgroup.mem_centralizer_iff.mp (this hz) y rfl).symm
  have key : (P : Subgroup G) ≤ Subgroup.centralizer (P : Set G) :=
    calc (P : Subgroup G) = _ := hPeq.symm
      _ ≤ _ := sup_le h1 h2
  have hPc : IsMulCommutative (P : Subgroup G) :=
    ⟨⟨fun a b => Subtype.ext (Subgroup.mem_centralizer_iff.mp (key a.2) b b.2).symm⟩⟩
  intro Q
  exact isMulCommutative_of_mulEquiv (Sylow.equiv Q P)

end Sylow

section Centralizer

variable {G : Type} [Group G] [Finite G]
variable [DicksonPsl2SubgroupClassification.{0}] [FrattiniElementaryQuotient.{0}] [FrattiniAutomorphismKernel.{0}]
  [TwoLePRankOfIsSimpleGroup.{0}] [MinimalNormalSimpleFactors.{0}] [FrobeniusNormalPComplement.{0}]

/-- **Lemma (1.9)** for `A = A₀` quasisimple. -/
theorem le_centralizer_top (hG : SylowMetacyclic G) (A : Subgroup G) (hq : IsQuasisimple A)
    (hZ : Nat.card (Subgroup.center A) ≤ 2) (N : Subgroup G) [N.Normal] (hinf : N ⊓ A = ⊥)
    (hodd : Odd (Nat.card N))
    (hexc : Nat.card (Subgroup.center A) = 2 → Nat.card (A ⧸ Subgroup.center A) = 60 →
      ∀ r, r.Prime → r ∣ Nat.card N → r ∣ Nat.card A) :
    A ≤ Subgroup.centralizer (N : Set G) := by
  have eT : (⊤ : Subgroup A) ≃* A := Subgroup.topEquiv
  have hZT : Nat.card (Subgroup.center (⊤ : Subgroup A)) = Nat.card (Subgroup.center A) :=
    Nat.card_congr (Subgroup.centerCongr eT).toEquiv
  have hQT : Nat.card ((⊤ : Subgroup A) ⧸ Subgroup.center (⊤ : Subgroup A)) =
      Nat.card (A ⧸ Subgroup.center A) :=
    Nat.card_congr (QuotientGroup.congr _ _ eT (Subgroup.map_center_eq eT)).toEquiv
  intro a ha
  exact le_centralizer_aux hG A ⊤ (hq.of_mulEquiv eT) (hZT.le.trans hZ) (by rw [Subgroup.index_top]; norm_num)
    le_top _ N rfl inferInstance hinf hodd (fun _ h2 h3 => hexc (hZT.symm.trans h2) (hQT.symm.trans h3))
    ⟨a, ha⟩ (Subgroup.mem_top _)

/-- **Lemma (1.9)** modulo `L`: a quasisimple `A` with `|Z(A)| ≤ 2` acts trivially on `N/L`, unless `|Z(A)| = 2`,
`|A/Z(A)| = 60` and some prime divides `|N/L|` but not `|A|`. -/
theorem comm_mem_of_quotient (hG : SylowMetacyclic G) (A : Subgroup G) (hq : IsQuasisimple A)
    (hZ : Nat.card (Subgroup.center A) ≤ 2) (N L : Subgroup G) [N.Normal] [L.Normal] (hLN : L ≤ N)
    (hinf : N ⊓ A = ⊥) (hodd : Odd (Nat.card N))
    (hexc : Nat.card (Subgroup.center A) = 2 → Nat.card (A ⧸ Subgroup.center A) = 60 →
      ∀ r, r.Prime → r ∣ Nat.card (N.map (QuotientGroup.mk' L)) → r ∣ Nat.card A) :
    ∀ a ∈ A, ∀ x ∈ N, a * x * a⁻¹ * x⁻¹ ∈ L := by
  classical
  have : (N.map (QuotientGroup.mk' L)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective L)
  have hinj : Function.Injective ((QuotientGroup.mk' L).subgroupMap A) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    have h1 : QuotientGroup.mk' L (a : G) = 1 := congrArg Subtype.val ha
    have h2 : (a : G) ∈ N ⊓ A := ⟨hLN ((QuotientGroup.eq_one_iff _).mp h1), a.2⟩
    rw [hinf, Subgroup.mem_bot] at h2
    exact (Subgroup.mem_bot).mpr (Subtype.ext h2)
  let eA : A ≃* A.map (QuotientGroup.mk' L) :=
    MulEquiv.ofBijective _ ⟨hinj, MonoidHom.subgroupMap_surjective _ A⟩
  have hAbinf : N.map (QuotientGroup.mk' L) ⊓ A.map (QuotientGroup.mk' L) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨x, hx, rfl⟩, ⟨a, ha, hax⟩⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hax
    have haN : a ∈ N := by
      have := N.mul_mem hx (N.inv_mem (hLN hax))
      simpa [mul_assoc] using this
    have : a ∈ N ⊓ A := ⟨haN, ha⟩
    rw [hinf, Subgroup.mem_bot] at this
    subst this
    exact (Subgroup.mem_bot).mpr ((QuotientGroup.eq_one_iff x).mpr (by simpa using hax))
  have hNbodd : Odd (Nat.card (N.map (QuotientGroup.mk' L))) :=
    Odd.of_dvd_nat hodd ⟨Nat.card L, (card_map_mk_mul hLN).symm⟩
  have hZb : Nat.card (Subgroup.center (A.map (QuotientGroup.mk' L))) = Nat.card (Subgroup.center A) :=
    Nat.card_congr (Subgroup.centerCongr eA.symm).toEquiv
  have hQb : Nat.card (A.map (QuotientGroup.mk' L) ⧸ Subgroup.center (A.map (QuotientGroup.mk' L))) =
      Nat.card (A ⧸ Subgroup.center A) :=
    Nat.card_congr (QuotientGroup.congr _ _ eA.symm (Subgroup.map_center_eq eA.symm)).toEquiv
  have hAb : Nat.card (A.map (QuotientGroup.mk' L)) = Nat.card A := (Nat.card_congr eA.toEquiv).symm
  have hle := le_centralizer_top (hG.quotient L) (A.map (QuotientGroup.mk' L)) (hq.of_mulEquiv eA.symm)
    (hZb.le.trans hZ) (N.map (QuotientGroup.mk' L)) hAbinf hNbodd
    (fun h2 h3 r hr hrN => hAb ▸ hexc (hZb.symm.trans h2) (hQb.symm.trans h3) r hr hrN)
  intro a ha x hx
  have hmem := Subgroup.mem_centralizer_iff.mp (hle ⟨a, ha, rfl⟩) _ ⟨x, hx, rfl⟩
  simp only [QuotientGroup.mk'_apply] at hmem
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
    QuotientGroup.mk_inv, QuotientGroup.mk_inv, ← hmem]
  group

end Centralizer

section Stem

/-- `SL(2, -)` of isomorphic rings. -/
def slCongr {R S : Type*} [CommRing R] [CommRing S] (f : R ≃+* S) : SL(2, R) ≃* SL(2, S) :=
  MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map f.toRingHom) (Matrix.SpecialLinearGroup.map f.symm.toRingHom)
    (by ext A i j; simp) (by ext A i j; simp)

variable [PslTwoHopfMultiplier] [HopfMultiplierAlternating] [CardHopfMultiplierEqCardGriess]
  [FieldNineAlternatingSix.{0}] [HopfCentralCoverConsequences] [CardKerDvdHopfMultiplier] [HopfMultiplierM11]

/-- A stem extension by a group of order 2 of a group of order 60 in the list of Lemma (1.5) is `SL(2, 5)`. -/
theorem nonempty_sl_five_of_stem {A X : Type} [Group A] [Finite A] [Group X] (hA : commutator A = ⊤)
    (D : Subgroup A) [D.Normal] (hD : D ≤ Subgroup.center A) (hD2 : Nat.card D = 2) (e : A ⧸ D ≃* X)
    [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a) (hX : Lemma15Conclusion X) (h60 : Nat.card X = 60) :
    Nonempty (A ≃* SL(2, ZMod 5)) := by
  rcases hX with ⟨⟨eX⟩⟩ | ⟨⟨eX⟩⟩ | ⟨F, _, _, p, n, hp, hn, hF, h5, ⟨eX⟩⟩
  · exfalso
    rw [Nat.card_congr eX.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at h60
    norm_num [Nat.factorial] at h60
  · -- `M₁₁` has trivial Schur multiplier
    exfalso
    let π : A →* Blueprint.NativeSporadic.M11 := ((e.trans eX).toMonoidHom).comp (QuotientGroup.mk' D)
    have hker : π.ker = D := ker_comp_mk D (e.trans eX)
    have hdvd := CardKerDvdHopfMultiplier.card_ker_dvd_hopfMultiplier hA π
      ((e.trans eX).surjective.comp (QuotientGroup.mk'_surjective D)) (hker ▸ hD)
    rw [hker, hD2, ← CardHopfMultiplierEqCardGriess.card_hopfMultiplier_eq_card_griessHopfMultiplier,
      HopfMultiplierM11.nativeRow_M11] at hdvd
    omega
  · have : IsSimpleGroup (PSL2 F) := eX.symm.isSimpleGroup
    have hnab' : ∃ a b : PSL2 F, a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := hnab
      exact ⟨eX a, eX b, fun h => hab (eX.injective (by simpa using h))⟩
    have hchar := ringChar_ne_two_of_card hp hn hF h5
    have hcard := LinearTwo.card_PSL2_mul_two F hchar
    rw [← Nat.card_congr eX.toEquiv, h60] at hcard
    have h5' : 5 ≤ Nat.card F := hF ▸ h5
    have hq5 : Nat.card F = 5 := by
      by_contra hne
      have h6 : 6 ≤ Nat.card F := by omega
      have := Nat.mul_le_mul h6 (Nat.sub_le_sub_right (Nat.pow_le_pow_left h6 2) 1)
      rw [← hcard] at this
      norm_num at this
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have := Fintype.ofFinite F
    have e5 : F ≃+* ZMod 5 :=
      FiniteField.ringEquivOfCardEq (by rw [ZMod.card, Fintype.card_eq_nat_card, hq5])
    obtain ⟨eS⟩ := nonempty_mulEquiv_sl2 hA D hD hD2 hchar (by omega) (e.trans eX) hnab'
    exact ⟨eS.trans (slCongr e5)⟩

end Stem

end CFSGOutside.ChillagSonn
