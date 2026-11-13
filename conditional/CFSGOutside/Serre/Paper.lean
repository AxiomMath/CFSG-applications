import CFSGOutside.Corpus.LieOrderBridgeHolds
import CFSGOutside.Corpus.OrdProjLeOfMulEq
import CFSGOutside.Serre.Defs
import CFSGOutside.Serre.Good
import CFSGOutside.Serre.ProjectiveSpecialLinearFive

/-!
# Serre (2013), Théorème 5 (Artin): `Σ_ℓ ∩ Σ_ℓ' = ∅`

J.-P. Serre, *Un critère d'indépendance pour une famille de représentations ℓ-adiques*,
Comment. Math. Helv. 88 (2013), 541-554 (arXiv 1006.2442), §6.4.

For a prime `ℓ ≥ 5`, `Σ_ℓ` is the set of (isomorphism classes of) finite simple groups of Lie type in
characteristic `ℓ`, together with the cyclic group `ℤ/ℓℤ` (§6.1; see `CFSGOutside.Serre.InSigma`).
Théorème 5: for distinct primes `ℓ, ℓ' ≥ 5`, `Σ_ℓ ∩ Σ_ℓ' = ∅`; the proof even gives that groups in `Σ_ℓ` and
`Σ_ℓ'` have distinct orders.

The theorems are conditional on two corpus inputs, stated as classes in `CFSGOutside.Corpus`: the orders of
the catalogue groups of Lie type (`LieOrderBridgeHolds`) and Artin's estimate of the `s`-part of such an order
(`OrdProjLeOfMulEq`). The paper does not use the classification of finite simple groups. The facts about
`PSL₂(𝔽₅)` and `A₅` are proved in `CFSGOutside.Serre.ProjectiveSpecialLinearFive`.
-/

namespace CFSGOutside.Serre

open CFSGOutside.Corpus CFSGOutside.Corpus.Open CFSGOutside.Corpus.ComponentClassification.CatLeaf

/-- Artin's argument (distinct odd characteristics): a number cannot be an order of a group of
Lie type in two distinct characteristics `p, r ≥ 5`. -/
theorem not_good_good [OrdProjLeOfMulEq] {p r M : ℕ} (hp : p.Prime) (hr : r.Prime) (hp5 : 5 ≤ p)
    (hr5 : 5 ≤ r) (hpr : p ≠ r) (hM0 : M ≠ 0) (hgp : Good p M) (hgr : Good r M) : False := by
  obtain ⟨t, n, f, hadm, hmul, hcop, hP, hpos⟩ := hgp
  obtain ⟨t', n', f', hadm', hmul', hcop', hP', hpos'⟩ := hgr
  have hPM : p ^ (f * lieSylowExponent t n) ∣ M := by
    rw [pow_mul]
    rw [← hmul] at hP
    exact (Nat.Coprime.pow_left _ (Nat.Coprime.pow_left _ hcop)).dvd_of_dvd_mul_right hP
  have hRM : r ^ (f' * lieSylowExponent t' n') ∣ M := by
    rw [pow_mul]
    rw [← hmul'] at hP'
    exact (Nat.Coprime.pow_left _ (Nat.Coprime.pow_left _ hcop')).dvd_of_dvd_mul_right hP'
  have h1 := OrdProjLeOfMulEq.ordProj_le_of_mul_eq hadm (by omega) hmul hr (by omega) (Ne.symm hpr)
  have h2 := OrdProjLeOfMulEq.ordProj_le_of_mul_eq hadm' (by omega) hmul' hp (by omega) hpr
  rw [← pow_mul] at h1 h2
  have h3 := pow_le_ordProj hp hM0 hPM
  have h4 := pow_le_ordProj hr hM0 hRM
  have heq : ordProj[p] M = ordProj[r] M := le_antisymm (h2.trans h4.1) (h1.trans h3.1)
  have hk : M.factorization p ≠ 0 := by
    have := Nat.mul_pos hadm.2.1 hpos
    omega
  have hdvd : p ∣ ordProj[r] M := heq ▸ dvd_pow_self p hk
  exact hpr ((Nat.prime_dvd_prime_iff_eq hp hr).1 (hp.dvd_of_dvd_pow hdvd))

/-- For `ℓ ≥ 5` the only omitted duplicate of characteristic `ℓ` is `A₁(5) = PSL₂(5)`, of order 60. -/
theorem duplicateLie_card {ℓ : ℕ} (h5 : 5 ≤ ℓ) {G : Type} [Group G] [Finite G]
    (hG : DuplicateLie ℓ G) : ℓ = 5 ∧ Nat.card G = 60 := by
  rcases hG with ⟨n, q, k, _, _, _, hd, hp, hk, ⟨e⟩⟩ | ⟨h3, _⟩
  · have hpp : q.p.Prime := q.3
    have hcard : q.card = q.p ^ q.exponent := rfl
    have hdvd : q.p ∣ q.p ^ q.exponent := dvd_pow_self _ q.4.ne'
    have hp5 : 5 ≤ q.p := hp ▸ h5
    simp [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff] at hd
    have h1 : n = 1 ∧ q.p ^ q.exponent = 5 := by
      rcases hd with ⟨hn, hc⟩ | ⟨hn, hc⟩ | ⟨hn, hc⟩
      · rcases hc with hc | hc | hc
        · exfalso; rw [hc] at hdvd; have := Nat.le_of_dvd (by norm_num) hdvd; omega
        · exact ⟨hn, hc⟩
        · exfalso; rw [hc, show (9:ℕ) = 3 ^ 2 by norm_num] at hdvd
          have := Nat.le_of_dvd (by norm_num) (hpp.dvd_of_dvd_pow hdvd); omega
      · exfalso; rw [hc] at hdvd; have := Nat.le_of_dvd (by norm_num) hdvd; omega
      · exfalso; rw [hc] at hdvd; have := Nat.le_of_dvd (by norm_num) hdvd; omega
    obtain ⟨rfl, hc5⟩ := h1
    have hl : ℓ = 5 := by
      rw [← hp]
      have h5' : q.p ∣ 5 := hc5 ▸ hdvd
      exact (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_five).1 h5'
    refine ⟨hl, ?_⟩
    rw [Nat.card_congr e.toEquiv]
    exact card_projectiveSpecialLinearGroup_two_of_card_five k (hk.trans (hcard.trans hc5))
  · omega

/-- A group in `Σ_ℓ` has an order with `Good` data in characteristic `ℓ`, or has order `ℓ`. -/
theorem card_of_inSigma [LieOrderBridgeHolds] {ℓ : ℕ} (hℓ5 : 5 ≤ ℓ) {G : Type} [Group G]
    [Finite G] (hG : InSigma ℓ G) : Good ℓ (Nat.card G) ∨ Nat.card G = ℓ := by
  rcases hG with ⟨idx, hc, ⟨e⟩⟩ | hd | he
  · left
    rw [LieOrderBridgeHolds.lieOrderBridge_holds idx G ⟨e⟩, ← hc]
    exact good_lieOrderFormula idx.1 idx.2 (hc ▸ hℓ5)
  · left
    obtain ⟨rfl, hcard⟩ := duplicateLie_card hℓ5 hd
    rw [hcard]
    exact good_five_sixty
  · right
    obtain ⟨e⟩ := he
    rw [Nat.card_congr (e.toEquiv.trans Multiplicative.toAdd), Nat.card_zmod]

/-- A prime `ℓ` is not `Good` in a characteristic `p ≠ ℓ`. -/
theorem not_good_prime {p ℓ : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime) (hpℓ : p ≠ ℓ) (hg : Good p ℓ) :
    False := by
  obtain ⟨k, hk, hdvd⟩ := pow_dvd_of_good hg
  exact hpℓ ((Nat.prime_dvd_prime_iff_eq hp hℓ).1 ((dvd_pow_self p (by omega)).trans hdvd))

/-- **ℓ-adic independence criterion.** For a prime ℓ ≥ 5 let Σ_ℓ be the class of finite groups isomorphic to a finite
simple group of Lie type in characteristic ℓ or to the cyclic group of order ℓ. If ℓ and ℓ′ are distinct primes,
both at least 5, then a group in Σ_ℓ and a group in Σ_ℓ′ never have the same order. In particular no finite group
lies in both classes.

Source: J.-P. Serre, Un critère d'indépendance pour une famille de représentations ℓ-adiques, Comment. Math. Helv.
88 (2013), 541–554, Théorème 5 and the remark on orders after it, §6.4. https://arxiv.org/abs/1006.2442

This version takes the corpus theorems it uses as instance arguments; the version in `unconditional/` supplies them
from the CFSG corpus. -/
theorem card_ne_of_inSigma [LieOrderBridgeHolds] [OrdProjLeOfMulEq] {ℓ ℓ' : ℕ} (hℓ : ℓ.Prime)
    (hℓ' : ℓ'.Prime) (h5 : 5 ≤ ℓ) (h5' : 5 ≤ ℓ') (hne : ℓ ≠ ℓ') {G G' : Type} [Group G] [Finite G] [Group G'] [Finite G']
    (hG : InSigma ℓ G) (hG' : InSigma ℓ' G') : Nat.card G ≠ Nat.card G' := by
  intro hcard
  have hM0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  rcases card_of_inSigma h5 hG with hg | hc <;> rcases card_of_inSigma h5' hG' with hg' | hc'
  · rw [← hcard] at hg'
    exact not_good_good hℓ hℓ' h5 h5' hne hM0 hg hg'
  · rw [hcard, hc'] at hg
    exact not_good_prime hℓ hℓ' hne hg
  · rw [← hcard, hc] at hg'
    exact not_good_prime hℓ' hℓ (Ne.symm hne) hg'
  · exact hne (hc.symm.trans (hcard.trans hc'))

/-- **Serre (2013), Théorème 5.** "Si `ℓ'` est premier `≥ 5` et distinct de `ℓ`, on a
`Σ_ℓ ∩ Σ_ℓ' = ∅`": no finite group belongs to both `Σ_ℓ` and `Σ_ℓ'`. -/
theorem sigma_disjoint [LieOrderBridgeHolds] [OrdProjLeOfMulEq] {ℓ ℓ' : ℕ} (hℓ : ℓ.Prime)
    (hℓ' : ℓ'.Prime) (h5 : 5 ≤ ℓ) (h5' : 5 ≤ ℓ')
    (hne : ℓ ≠ ℓ') (G : Type) [Group G] [Finite G] : ¬ (InSigma ℓ G ∧ InSigma ℓ' G) :=
  fun ⟨h, h'⟩ => card_ne_of_inSigma hℓ hℓ' h5 h5' hne h h' rfl

/-- `PSL₂(𝔽₅)`, the omitted duplicate `A₁(5)`, belongs to `Σ₅`. -/
theorem psl2_five_mem_sigma :
    InSigma 5 (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5)) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine Or.inr (Or.inl ?_)
  refine Or.inl ⟨1, ⟨5, 1, Nat.prime_five, Nat.one_pos⟩, ZMod 5, inferInstance, inferInstance,
    ?_, ?_, rfl, ?_, ⟨MulEquiv.refl _⟩⟩
  · rw [TauCeti.LieTypeIndex.inStandardRange_iff]
    exact ⟨le_rfl, fun _ => by norm_num⟩
  · rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    left; exact ⟨rfl, Or.inr (Or.inl rfl)⟩
  · rw [Nat.card_eq_fintype_card, ZMod.card]; rfl

/-- `A₅` belongs to `Σ₅`: it is `PSL₂(𝔽₅)` (the catalogue lists it as an alternating group). -/
theorem alternatingGroup_five_mem_sigma : InSigma 5 (alternatingGroup (Fin 5)) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨e⟩ := nonempty_projectiveSpecialLinearGroup_two_zmod_five_mulEquiv_alternatingGroup
  refine Or.inr (Or.inl (Or.inl ⟨1, ⟨5, 1, Nat.prime_five, Nat.one_pos⟩, ZMod 5, inferInstance,
    inferInstance, ?_, ?_, rfl, ?_, ⟨e.symm⟩⟩))
  · rw [TauCeti.LieTypeIndex.inStandardRange_iff]
    exact ⟨le_rfl, fun _ => by norm_num⟩
  · rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    left; exact ⟨rfl, Or.inr (Or.inl rfl)⟩
  · rw [Nat.card_eq_fintype_card, ZMod.card]; rfl

end CFSGOutside.Serre
