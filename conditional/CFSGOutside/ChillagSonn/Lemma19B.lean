import CFSGOutside.ChillagSonn.Lemma19A
import CFSGOutside.ChillagSonn.SylowTower
import CFSGOutside.ChillagSonn.Simple

/-!
# Lemma (1.9): a quasisimple complement centralizes the odd normal subgroup

Let `G` be Sylow-metacyclic, `N ⊴ G` of odd order and `A ≤ G` with `N ∩ A = 1`, and let `A₀ ⊴ A` be quasisimple with
`|Z(A₀)| ≤ 2`, `|A : A₀| ≤ 2`, `C_A(A₀) ≤ A₀`. Unless `A = A₀`, `|Z(A₀)| = 2`, `|A₀/Z(A₀)| = 60` and some prime
divisor of `|N|` does not divide `|A|`, `A₀` centralizes `N`.

Induction on `|N|`, as in the paper. If `N` is an `r`-group, this is `le_ker_of_action` (with Lemma (1.2)(b): if `r`
divides `|A|` then `N` is cyclic). Otherwise let `q` be the smallest prime divisor of `|N|` and `M ⊴ G` the normal
Hall subgroup of `N` for the primes `> q` (Sylow tower). By induction `A₀` centralizes `M`, and by the one-prime case it
acts trivially on `N/M`. A 2-element `t ∈ A₀ ∖ Z(A₀)` normalizes a Sylow `q`-subgroup `Q` of `N` (there are an odd
number of them) and centralizes it (`Q ≅ N/M` equivariantly), hence centralizes `N = MQ`. So `C_{A₀}(N)` is a normal
subgroup of the quasisimple `A₀` not contained in `Z(A₀)`, i.e. all of `A₀`.
-/

namespace CFSGOutside.ChillagSonn

open CFSGOutside.Corpus

open scoped Pointwise

/-- A quasisimple group has a 2-element outside its center. -/
theorem exists_two_element_not_mem_center [TwoLePRankOfIsSimpleGroup.{0}] [MinimalNormalSimpleFactors.{0}]
    {A₀ : Type} [Group A₀] [Finite A₀] (hq : IsQuasisimple A₀) :
    ∃ t : A₀, t ∉ Subgroup.center A₀ ∧ ∃ k : ℕ, t ^ (2 ^ k) = 1 := by
  have : IsSimpleGroup (A₀ ⧸ Subgroup.center A₀) := hq.2.1
  obtain ⟨E, -, hEs, hE4⟩ := exists_elem4 (A₀ ⧸ Subgroup.center A₀) hq.2.2
  obtain ⟨ū, hū, hū1⟩ : ∃ ū ∈ E, ū ≠ 1 := by
    by_contra h
    push Not at h
    have : E = ⊥ := eq_bot_iff.mpr fun x hx => (Subgroup.mem_bot).mpr (h x hx)
    rw [this, Subgroup.card_bot] at hE4
    omega
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective ū
  obtain ⟨a, m, hm, hu⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos u).ne'
  refine ⟨u ^ m, ?_, a, ?_⟩
  · intro hmem
    apply hū1
    have h2 : ((u : A₀ ⧸ Subgroup.center A₀)) ^ 2 = 1 := hEs _ hū
    obtain ⟨k, rfl⟩ := hm
    have : ((u ^ (2 * k + 1) : A₀) : A₀ ⧸ Subgroup.center A₀) = 1 := (QuotientGroup.eq_one_iff _).mpr hmem
    rw [QuotientGroup.mk_pow, pow_succ, pow_mul, h2, one_pow, one_mul] at this
    exact this
  · rw [← pow_mul, mul_comm, ← hu, pow_orderOf_eq_one]

/-- If `N ⊴ G` is an `r`-group (`r` odd) with `N ∩ A = 1` and `r ∣ |A|`, then `N` is cyclic (Lemma (1.2)(b)). -/
theorem isCyclic_of_dvd_card [FrattiniElementaryQuotient.{0}] {G : Type} [Group G] [Finite G]
    (hG : SylowMetacyclic G) (N A : Subgroup G) [N.Normal] (hinf : N ⊓ A = ⊥) {r : ℕ} [Fact r.Prime]
    (hr2 : r ≠ 2) (hN : IsPGroup r N) (hrA : r ∣ Nat.card A) : IsCyclic N := by
  obtain ⟨R⟩ : Nonempty (Sylow r A) := inferInstance
  set R' : Subgroup G := (R : Subgroup A).map A.subtype
  have hR'p : IsPGroup r R' := R.isPGroup'.map _
  have hR'1 : R' ≠ ⊥ := by
    intro h
    have hc : Nat.card (R : Subgroup A) = 1 := by
      rw [← Subgroup.card_map_of_injective A.subtype_injective]
      change Nat.card R' = 1
      rw [h, Subgroup.card_bot]
    rw [Sylow.card_eq_multiplicity] at hc
    have hpos := Nat.Prime.factorization_pos_of_dvd Fact.out (Nat.card_pos (α := A)).ne' hrA
    have : r ≤ r ^ (Nat.card A).factorization r := by
      calc r = r ^ 1 := (pow_one r).symm
        _ ≤ _ := Nat.pow_le_pow_right (Nat.Prime.pos Fact.out) hpos
    have := (Fact.out : r.Prime).two_le
    omega
  have hR'A : R' ≤ A := Subgroup.map_subtype_le _
  set P : Subgroup G := N ⊔ R'
  have hPp : IsPGroup r P := IsPGroup.to_sup_of_normal_left hN hR'p
  have hPm : IsMetacyclic P := hG.isMetacyclic_of_isPGroup P hPp
  have hPpg : IsPGroup r ↥P := hPp
  have h1 : (N.subgroupOf P ⊔ R'.subgroupOf P) = ⊤ := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left le_sup_left, inf_of_le_left le_sup_right, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have h2 : (N.subgroupOf P ⊓ R'.subgroupOf P) = ⊥ := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_inf_eq _ _ _ P.subtype_injective, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, Subgroup.map_bot, eq_bot_iff]
    rintro x ⟨⟨hxN, -⟩, hxR, -⟩
    rw [← hinf]
    exact ⟨hxN, hR'A hxR⟩
  have h3 : R'.subgroupOf P ≠ ⊥ := by
    intro h
    apply hR'1
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, le_sup_right (a := N) hx⟩ : P) ∈ R'.subgroupOf P := hx
    rw [h, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).mpr (congrArg Subtype.val this)
  have : (N.subgroupOf P).Normal := Subgroup.normal_subgroupOf
  have hc := lemma_1_2_b hr2 hPpg hPm (N.subgroupOf P) (R'.subgroupOf P) h1 h2 h3
  exact isCyclic_of_injective (Subgroup.subgroupOfEquivOfLe (le_sup_left : N ≤ P)).symm.toMonoidHom
    (MulEquiv.injective _)

/-- `n = upperPart (q + 1) n * q ^ v_q(n)` for `q` the smallest prime factor of `n`. -/
theorem eq_upperPart_mul_pow_minFac {n : ℕ} (hn : n ≠ 0) (hn1 : n ≠ 1) :
    n = upperPart (n.minFac + 1) n * n.minFac ^ n.factorization n.minFac := by
  have hq := Nat.minFac_prime hn1
  conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hn]
  rw [upperPart, ← Finset.prod_filter_mul_prod_filter_not n.primeFactors (fun p => n.minFac + 1 ≤ p)]
  congr 1
  have hfil : n.primeFactors.filter (fun p => ¬ n.minFac + 1 ≤ p) = {n.minFac} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_singleton, Nat.mem_primeFactors, not_le]
    constructor
    · rintro ⟨⟨hp, hpn, -⟩, hlt⟩
      have := Nat.minFac_le_of_dvd hp.two_le hpn
      omega
    · rintro rfl
      exact ⟨⟨hq, Nat.minFac_dvd n, hn⟩, by omega⟩
  rw [hfil, Finset.prod_singleton]

theorem not_dvd_upperPart {q n : ℕ} (hq : q.Prime) : ¬ q ∣ upperPart (q + 1) n := by
  rw [upperPart]
  intro h
  obtain ⟨p, hp, hqp⟩ := (Prime.dvd_finsetProd_iff hq.prime _).mp h
  rw [Finset.mem_filter, Nat.mem_primeFactors] at hp
  have := (Nat.prime_dvd_prime_iff_eq hq hp.1.1).mp (hq.dvd_of_dvd_pow hqp)
  omega

variable [DicksonPsl2SubgroupClassification.{0}] [FrattiniElementaryQuotient.{0}] [FrattiniAutomorphismKernel.{0}]
  [TwoLePRankOfIsSimpleGroup.{0}] [MinimalNormalSimpleFactors.{0}] [FrobeniusNormalPComplement.{0}]

/-- **Lemma (1.9)**, centralizer statement, by induction on `|N|`. -/
theorem le_centralizer_aux {G : Type} [Group G] [Finite G] (hG : SylowMetacyclic G) (A : Subgroup G)
    (A₀ : Subgroup A) [A₀.Normal] (hq : IsQuasisimple A₀) (hZ : Nat.card (Subgroup.center A₀) ≤ 2)
    (hidx : A₀.index ≤ 2) (hCA : Subgroup.centralizer (A₀ : Set A) ≤ A₀) (n : ℕ) :
    ∀ N : Subgroup G, Nat.card N = n → N.Normal → N ⊓ A = ⊥ → Odd (Nat.card N) →
      (A₀ = ⊤ → Nat.card (Subgroup.center A₀) = 2 → Nat.card (A₀ ⧸ Subgroup.center A₀) = 60 →
        ∀ r, r.Prime → r ∣ Nat.card N → r ∣ Nat.card A) →
      ∀ a ∈ A₀, (a : G) ∈ Subgroup.centralizer (N : Set G) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro N hn hNn hinf hodd hexc
  classical
  have := hNn
  set φ : A →* MulAut N := (MulAut.conjNormal : G →* MulAut N).comp A.subtype
  have hφ : ∀ a : A, a ∈ φ.ker → (a : G) ∈ Subgroup.centralizer (N : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have := congrArg (fun σ : MulAut N => ((σ ⟨x, hx⟩ : N) : G)) (MonoidHom.mem_ker.mp ha)
    simp only [φ, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conjNormal_apply, MulAut.one_apply] at this
    calc x * a = ((a : G) * x * (a : G)⁻¹) * a := by rw [this]
      _ = a * x := by group
  by_cases hN1 : Nat.card N = 1
  · intro a _
    rw [Subgroup.eq_bot_of_card_eq N hN1]
    exact Subgroup.mem_centralizer_iff.mpr fun x hx => by rw [(Subgroup.mem_bot).mp hx]; group
  set q := (Nat.card N).minFac
  have hqp : q.Prime := Nat.minFac_prime hN1
  have : Fact q.Prime := ⟨hqp⟩
  have hqN : q ∣ Nat.card N := Nat.minFac_dvd _
  have hq2 : q ≠ 2 := fun h => by
    rw [h] at hqN
    exact Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr hqN)
  by_cases hpg : IsPGroup q N
  · intro a ha
    apply hφ
    refine le_ker_of_action hq2 hpg (hG.isMetacyclic_of_isPGroup N hpg) ?_ φ A₀ hq hZ hidx hCA ?_ ha
    · intro hnc hqA
      exact hnc (isCyclic_of_dvd_card hG N A hinf hq2 hpg hqA)
    · intro h1 h2 h3
      exact isCyclic_of_dvd_card hG N A hinf hq2 hpg (hexc h1 h2 h3 q hqp hqN)
  -- several primes: the normal Hall subgroup `M` for the primes `> q`
  have hNpos : Nat.card N ≠ 0 := Nat.card_pos.ne'
  obtain ⟨H, hHc, hHcard⟩ := exists_characteristic_upperPart (Nat.card N) rfl (hG.subgroup N) hodd (q + 1)
  set M : Subgroup G := H.map N.subtype
  have hMN : M ≤ N := Subgroup.map_subtype_le H
  have hMn : M.Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨y, hy, rfl⟩ := hx
    have hmap := Subgroup.characteristic_iff_map_eq.mp hHc (MulAut.conjNormal g)
    have : (MulAut.conjNormal g) y ∈ H := hmap ▸ Subgroup.mem_map_of_mem _ hy
    exact ⟨_, this, by simp [MulAut.conjNormal_apply]⟩
  have hMcard : Nat.card M = upperPart (q + 1) (Nat.card N) := by
    rw [Subgroup.card_map_of_injective N.subtype_injective, hHcard]
  have hNfac : Nat.card N = Nat.card M * q ^ (Nat.card N).factorization q := by
    rw [hMcard]
    exact eq_upperPart_mul_pow_minFac hNpos hN1
  have hMq : ¬ q ∣ Nat.card M := by
    rw [hMcard]
    exact not_dvd_upperPart hqp
  have hv : 1 ≤ (Nat.card N).factorization q := hqp.factorization_pos_of_dvd hNpos hqN
  have hMlt : Nat.card M < n := by
    rw [← hn, hNfac]
    have hMpos : 0 < Nat.card M := Nat.card_pos
    have : 2 ≤ q ^ (Nat.card N).factorization q :=
      le_trans hqp.two_le (Nat.le_self_pow (by omega) q)
    nlinarith
  have hM := ih _ hMlt M rfl hMn (eq_bot_iff.mpr fun x hx => hinf ▸ ⟨hMN hx.1, hx.2⟩)
    (Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hMN))
    (fun h1 h2 h3 r hr hrM => hexc h1 h2 h3 r hr (hrM.trans (Subgroup.card_dvd_of_le hMN)))
  -- the action on `N/M`
  set Nb : Subgroup (G ⧸ M) := N.map (QuotientGroup.mk' M)
  have hNbn : Nb.Normal := hNn.map _ (QuotientGroup.mk'_surjective M)
  have hNbcard : Nat.card Nb = q ^ (Nat.card N).factorization q := by
    have hker : ((QuotientGroup.mk' M).subgroupMap N).ker = M.subgroupOf N := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro h
        exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val h)
      · intro h
        exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr h)
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (M.subgroupOf N)
    rw [← hker, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
      (MonoidHom.subgroupMap_surjective _ _)).toEquiv, hker,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMN).toEquiv] at h1
    have hMpos : 0 < Nat.card M := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hMpos ((h1.symm.trans hNfac).trans (mul_comm _ _))
  have hNbp : IsPGroup q Nb := IsPGroup.of_card hNbcard
  set Ab : Subgroup (G ⧸ M) := A.map (QuotientGroup.mk' M)
  have hMA : M ⊓ A = ⊥ := eq_bot_iff.mpr fun x hx => hinf ▸ ⟨hMN hx.1, hx.2⟩
  have hAbinf : Nb ⊓ Ab = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨x, hx, rfl⟩, ⟨a, ha, hax⟩⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hax
    have haN : a ∈ N := by
      have := N.mul_mem hx (N.inv_mem (hMN hax))
      simpa [mul_assoc] using this
    have : a ∈ N ⊓ A := ⟨haN, ha⟩
    rw [hinf, Subgroup.mem_bot] at this
    subst this
    exact (Subgroup.mem_bot).mpr ((QuotientGroup.eq_one_iff x).mpr (by simpa using hax))
  have hAbcard : Nat.card Ab = Nat.card A := by
    have hinj : Function.Injective ((QuotientGroup.mk' M).subgroupMap A) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro a ha
      have h1 : QuotientGroup.mk' M (a : G) = 1 := congrArg Subtype.val ha
      have h2 : (a : G) ∈ M ⊓ A := ⟨(QuotientGroup.eq_one_iff _).mp h1, a.2⟩
      rw [hMA, Subgroup.mem_bot] at h2
      exact (Subgroup.mem_bot).mpr (Subtype.ext h2)
    exact (Nat.card_congr (Equiv.ofBijective _ ⟨hinj, MonoidHom.subgroupMap_surjective _ A⟩)).symm
  have hGb := hG.quotient M
  set φb : A →* MulAut Nb :=
    (MulAut.conjNormal : (G ⧸ M) →* MulAut Nb).comp ((QuotientGroup.mk' M).comp A.subtype)
  have hker := le_ker_of_action hq2 hNbp (hGb.isMetacyclic_of_isPGroup Nb hNbp)
    (fun hnc hqA => hnc (isCyclic_of_dvd_card hGb Nb Ab hAbinf hq2 hNbp (hAbcard ▸ hqA))) φb A₀ hq hZ hidx hCA
    (fun h1 h2 h3 => isCyclic_of_dvd_card hGb Nb Ab hAbinf hq2 hNbp (hAbcard ▸ hexc h1 h2 h3 q hqp hqN))
  have htriv : ∀ a ∈ A₀, ∀ x ∈ N, ((a : G) * x * (a : G)⁻¹)⁻¹ * x ∈ M := by
    intro a ha x hx
    have h1 := congrArg (fun σ : MulAut Nb => ((σ ⟨QuotientGroup.mk' M x, x, hx, rfl⟩ : Nb) : G ⧸ M))
      (MonoidHom.mem_ker.mp (hker ha))
    simp only [φb, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conjNormal_apply, MulAut.one_apply] at h1
    rw [← QuotientGroup.eq]
    simpa [QuotientGroup.mk'_apply] using h1
  -- a 2-element `t ∈ A₀ ∖ Z(A₀)` normalizes a Sylow `q`-subgroup of `N`
  obtain ⟨t, ht, k, htk⟩ := exists_two_element_not_mem_center hq
  set σ : MulAut N := MulAut.conjNormal ((t : A) : G)
  have hσ : σ ^ (2 ^ k) = 1 := by
    rw [← map_pow]
    have : ((t : A) : G) ^ (2 ^ k) = 1 := by
      rw [← Subgroup.coe_pow, ← Subgroup.coe_pow, htk]; rfl
    rw [this, map_one]
  have hT : IsPGroup 2 (Subgroup.zpowers σ) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hσ)
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := hT.card_modEq_card_fixedPoints (Sylow q N)
  have hSodd : Odd (Nat.card (Sylow q N)) := by
    obtain ⟨P₀⟩ : Nonempty (Sylow q N) := inferInstance
    rw [Sylow.card_eq_index_normalizer P₀]
    exact Odd.of_dvd_nat hodd (Subgroup.index_dvd_card _)
  have hfix : (MulAction.fixedPoints (Subgroup.zpowers σ) (Sylow q N)).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    rw [hemp] at hmod
    have h0 : Nat.card (Sylow q N) % 2 = 0 := by simpa [Nat.ModEq] using hmod
    exact Nat.not_even_iff_odd.mpr hSodd (Nat.even_iff.mpr h0)
  obtain ⟨P, hP⟩ := hfix
  have hPσ : ∀ x ∈ (P : Subgroup N), σ x ∈ (P : Subgroup N) := by
    intro x hx
    have h1 : (⟨σ, Subgroup.mem_zpowers σ⟩ : Subgroup.zpowers σ) • P = P := hP _
    have h2 : σ • x ∈ σ • (P : Subgroup N) := Subgroup.smul_mem_pointwise_smul x σ _ hx
    rw [← Sylow.pointwise_smul_def] at h2
    change σ • P = P at h1
    rw [h1] at h2
    exact h2
  set Q : Subgroup G := (P : Subgroup N).map N.subtype
  have hQN : Q ≤ N := Subgroup.map_subtype_le _
  have hQcard : Nat.card Q = q ^ (Nat.card N).factorization q := by
    rw [Subgroup.card_map_of_injective N.subtype_injective, Sylow.card_eq_multiplicity]
  have hQM : Q ⊓ M = ⊥ := Subgroup.inf_eq_bot_of_coprime (by
    rw [hQcard]
    exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hqp).mpr hMq))
  -- `t` centralizes `Q`
  have htQ : ∀ x ∈ Q, ((t : A) : G) * x = x * ((t : A) : G) := by
    rintro _ ⟨x, hx, rfl⟩
    have hy : σ x ∈ (P : Subgroup N) := hPσ x hx
    have hyx : ((σ x : N) : G)⁻¹ * (x : G) ∈ Q ⊓ M := by
      refine ⟨Q.mul_mem (Q.inv_mem ⟨_, hy, rfl⟩) ⟨x, hx, rfl⟩, ?_⟩
      exact htriv _ t.2 x x.2
    rw [hQM, Subgroup.mem_bot, inv_mul_eq_one] at hyx
    have : ((t : A) : G) * x * ((t : A) : G)⁻¹ = x := by
      have h := hyx
      simp only [σ, MulAut.conjNormal_apply] at h
      exact h
    calc ((t : A) : G) * x = ((t : A) : G) * x * ((t : A) : G)⁻¹ * ((t : A) : G) := by group
      _ = x * ((t : A) : G) := by rw [this]
  -- `N = M Q`
  have hNMQ : M ⊔ Q = N := by
    have h1 := Subgroup.relIndex_mul_card M Q
    have h2 := Subgroup.relIndex_mul_card M (Q ⊔ M)
    rw [inf_comm, hQM, Subgroup.card_bot, mul_one] at h1
    rw [inf_of_le_left le_sup_right, Subgroup.relIndex_sup_right, h1] at h2
    rw [sup_comm]
    refine Subgroup.eq_of_le_of_card_ge (sup_le hQN hMN) (le_of_eq ?_)
    rw [← h2, hQcard]
    conv_lhs => rw [hNfac]
    rw [mul_comm]
  have htN : ((t : A) : G) ∈ Subgroup.centralizer (N : Set G) := by
    have hle : M ⊔ Q ≤ Subgroup.centralizer ({((t : A) : G)} : Set G) := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        rintro _ rfl
        exact ((Subgroup.mem_centralizer_iff.mp (hM t t.2)) x hx).symm
      · rw [Subgroup.mem_centralizer_iff]
        rintro _ rfl
        exact htQ x hx
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (Subgroup.mem_centralizer_iff.mp (hle (hNMQ ▸ hh)) _ rfl).symm
  -- `C_{A₀}(N)` is normal in `A₀` and not central, hence everything
  set K : Subgroup A₀ := ((Subgroup.centralizer (N : Set G)).comap A.subtype).subgroupOf A₀
  have hKn : K.Normal := by
    have : ((Subgroup.centralizer (N : Set G)).comap A.subtype).Normal :=
      (inferInstance : (Subgroup.centralizer (N : Set G)).Normal).comap _
    exact Subgroup.normal_subgroupOf
  rcases LocalCores.quasisimple_normal_subgroups hq hKn with h | h
  · intro a ha
    have : (⟨a, ha⟩ : A₀) ∈ K := h ▸ Subgroup.mem_top _
    exact this
  · exact absurd (h (show t ∈ K from htN)) ht

end CFSGOutside.ChillagSonn
