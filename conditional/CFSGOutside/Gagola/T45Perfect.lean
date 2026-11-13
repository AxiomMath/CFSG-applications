import CFSGOutside.Gagola.Perfect
import CFSGOutside.Gagola.GroupFacts

/-!
# Gagola, Theorem 4.5: the perfect case and a minimal normal subgroup of `p`-power index
-/

namespace CFSGOutside.Gagola

open Classical CFSGOutside.Corpus

noncomputable section

theorem perfect_false [WalterSplit] [CardOfReeTitsModelTwistedG2] [CardWalterJ1]
    [GorensteinWalter] [BrauerSuzukiQuaternion] [Order8Nonabelian]
    [RankTwoSylowShapes] [HoltAtMostOneInvolution.{0}] [CardStatedClassicalModelTwo]
    [Gh74SectionalTwoRankFour]
    {H : Type} [Group H] [Fintype H] {Z : Subgroup H} [Z.Normal] {χ : H → ℂ}
    (hfr : FullyRamified Z χ) (hperf : commutator (H ⧸ Z) = ⊤) (hnt : Nontrivial (H ⧸ Z))
    (h16 : ∀ P : Sylow 2 (H ⧸ Z), ¬ IsMulCommutative (P : Subgroup (H ⧸ Z)) → Nat.card P ≤ 16) :
    False := by
  obtain ⟨M, hMn, hsimple⟩ := exists_simple_quotient (H ⧸ Z)
  have hnonab : ∃ a b : (H ⧸ Z) ⧸ M, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    have hle : commutator (H ⧸ Z) ≤ M := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [← QuotientGroup.eq_one_iff, commutatorElement_def, QuotientGroup.mk_mul,
        QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv,
        hc (a : (H ⧸ Z) ⧸ M) (b : (H ⧸ Z) ⧸ M)]
      group
    rw [hperf, top_le_iff] at hle
    subst hle
    obtain ⟨x, y, hxy⟩ := (inferInstance : Nontrivial ((H ⧸ Z) ⧸ (⊤ : Subgroup (H ⧸ Z))))
    exact hxy (@Subsingleton.elim _ QuotientGroup.subsingleton_quotient_top x y)
  let f : H →* (H ⧸ Z) ⧸ M := (QuotientGroup.mk' M).comp (QuotientGroup.mk' Z)
  have hf : Function.Surjective f :=
    (QuotientGroup.mk'_surjective M).comp (QuotientGroup.mk'_surjective Z)
  have hZK : Z ≤ f.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    simp [f, (QuotientGroup.eq_one_iff z).mpr hz]
  let ψ : H ⧸ f.ker ≃* (H ⧸ Z) ⧸ M := QuotientGroup.quotientKerEquivOfSurjective f hf
  haveI : Nontrivial (H ⧸ f.ker) := ψ.toEquiv.nontrivial
  haveI : IsSimpleGroup (H ⧸ f.ker) :=
    IsSimpleGroup.isSimpleGroup_of_surjective ψ.symm.toMonoidHom ψ.symm.surjective
  have hnonab' : ∃ a b : H ⧸ f.ker, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    refine ⟨ψ.symm a, ψ.symm b, fun h => hab ?_⟩
    have := congrArg ψ h
    simpa using this
  exact perfect_step hfr f.ker hZK hnonab' h16

section PElement

variable {X : Type*} [Group X] [Finite X]

theorem exists_pElement_not_mem_commutator (hnp : commutator X ≠ ⊤) :
    ∃ (p : ℕ) (_ : Fact p.Prime) (c : X), (∃ k : ℕ, c ^ p ^ k = 1) ∧ c ∉ commutator X := by
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : X, c₀ ∉ commutator X := by
    by_contra hc; push Not at hc
    exact hnp (eq_top_iff.mpr fun g _ => hc g)
  set q := QuotientGroup.mk' (commutator X) with hq
  have hqmem : ∀ x : X, q x = 1 ↔ x ∈ commutator X := fun x => QuotientGroup.eq_one_iff x
  have ha₀ : q c₀ ≠ 1 := fun h => hc₀ ((hqmem c₀).mp h)
  set n := orderOf (q c₀) with hn
  have hnpos : 0 < n := orderOf_pos _
  have hn1 : n ≠ 1 := fun h => ha₀ (orderOf_eq_one_iff.mp h)
  set p := n.minFac with hp
  have hpp : p.Prime := Nat.minFac_prime hn1
  haveI : Fact p.Prime := ⟨hpp⟩
  have hpn : p ∣ n := Nat.minFac_dvd n
  set c₁ := c₀ ^ (n / p) with hc₁
  have ha : orderOf (q c₁) = p := by
    rw [hc₁, map_pow, orderOf_pow_of_dvd (Nat.div_pos (Nat.le_of_dvd hnpos hpn) hpp.pos).ne'
      (Nat.div_dvd_of_dvd hpn), ← hn]
    exact Nat.div_div_self hpn hnpos.ne'
  have hao : orderOf c₁ ≠ 0 := (orderOf_pos _).ne'
  set o := orderOf c₁ with ho
  set m := ordCompl[p] o with hm
  set v := o.factorization p with hv
  have hom : p ^ v * m = o := Nat.ordProj_mul_ordCompl_eq_self o p
  have hpm : ¬ p ∣ m := Nat.not_dvd_ordCompl hpp hao
  refine ⟨p, ⟨hpp⟩, c₁ ^ m, ⟨v, ?_⟩, ?_⟩
  · rw [← pow_mul, mul_comm, hom]; exact pow_orderOf_eq_one c₁
  · intro hmem
    have h1 := (hqmem _).mpr hmem
    rw [map_pow, ← orderOf_dvd_iff_pow_eq_one, ha] at h1
    exact hpm h1

end PElement

section Pull

variable {H : Type*} [Group H] [Finite H] {p : ℕ}

theorem isPGroup_comap_quotient (Z : Subgroup H) [Z.Normal] (M : Subgroup (H ⧸ Z)) [M.Normal]
    (hM : IsPGroup p ((H ⧸ Z) ⧸ M)) :
    IsPGroup p (H ⧸ M.comap (QuotientGroup.mk' Z)) := by
  intro g
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨k, hk⟩ := hM (((h : H ⧸ Z) : (H ⧸ Z) ⧸ M))
  refine ⟨k, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk
  exact hk

end Pull

section Minimal

variable {H : Type*} [Group H] [Finite H] {p : ℕ} [hp : Fact p.Prime]

theorem eq_top_of_minimal (Z : Subgroup H) [Z.Normal] (K : Subgroup H) [K.Normal] (hZK : Z ≤ K)
    (hKtop : K ≠ ⊤) (hKp : IsPGroup p (H ⧸ K))
    (hmin : ∀ (K' : Subgroup H) [K'.Normal], Z ≤ K' → K' ≠ ⊤ → IsPGroup p (H ⧸ K') →
      Nat.card K ≤ Nat.card K')
    (M : Subgroup (K ⧸ Z.subgroupOf K)) [M.Normal]
    (hM : IsPGroup p ((K ⧸ Z.subgroupOf K) ⧸ M)) : M = ⊤ := by
  set π : K →* (K ⧸ Z.subgroupOf K) ⧸ M :=
    (QuotientGroup.mk' M).comp (QuotientGroup.mk' (Z.subgroupOf K)) with hπ
  have hπs : Function.Surjective π :=
    (QuotientGroup.mk'_surjective M).comp (QuotientGroup.mk'_surjective _)
  obtain ⟨s, hs⟩ := hM.exists_card_eq
  have hpow : ∀ x : K, x ^ p ^ s ∈ π.ker := fun x => by
    rw [MonoidHom.mem_ker, map_pow, ← hs]
    exact pow_card_eq_one'
  set M'' : Subgroup H := π.ker.map K.subtype with hM''
  have hM''K : M'' ≤ K := by
    rintro _ ⟨x, _, rfl⟩; exact x.2
  have hZM : Z ≤ M'' := by
    intro z hz
    refine ⟨⟨z, hZK hz⟩, ?_, rfl⟩
    show π _ = 1
    have : (QuotientGroup.mk' (Z.subgroupOf K)) ⟨z, hZK hz⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hz
    show QuotientGroup.mk' M ((QuotientGroup.mk' (Z.subgroupOf K)) ⟨z, hZK hz⟩) = 1
    rw [this, map_one]
  set N := M''.normalCore with hN
  have hNZ : Z ≤ N := Subgroup.normal_le_normalCore.mpr hZM
  have hNM : N ≤ M'' := Subgroup.normalCore_le _
  have hNtop : N ≠ ⊤ := fun h => hKtop (eq_top_iff.mpr (h ▸ hNM.trans hM''K))
  have hNp : IsPGroup p (H ⧸ N) := by
    intro g
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨k, hk⟩ := hKp (h : H ⧸ K)
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk
    refine ⟨k + s, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, pow_add, pow_mul]
    set y := h ^ p ^ k
    show ∀ b : H, b * y ^ p ^ s * b⁻¹ ∈ M''
    intro b
    have hgy : b * y * b⁻¹ ∈ K := Subgroup.Normal.conj_mem inferInstance y hk b
    have := hpow ⟨b * y * b⁻¹, hgy⟩
    refine ⟨_, this, ?_⟩
    simp [conj_pow]
  have hcard := hmin N hNZ hNtop hNp
  have hle : Nat.card N ≤ Nat.card M'' := Subgroup.card_le_of_le hNM
  have hMK : M'' = K := Subgroup.eq_of_le_of_card_ge hM''K (hcard.trans hle)
  have hker : ∀ x : K, π x = 1 := by
    intro x
    have hx : (x : H) ∈ M'' := by rw [hMK]; exact x.2
    obtain ⟨x', hx', hxx⟩ := hx
    have : x' = x := Subtype.ext hxx
    have h1 : π x' = 1 := hx'
    rw [this] at h1
    exact h1
  rw [eq_top_iff]
  intro g _
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf K) g
  have := hker x
  simp only [hπ, MonoidHom.comp_apply, QuotientGroup.mk'_apply] at this
  exact (QuotientGroup.eq_one_iff _).mp this

end Minimal

theorem exists_minimal_K {H : Type} [Group H] [Fintype H] (Z : Subgroup H) [Z.Normal]
    (hnp : commutator (H ⧸ Z) ≠ ⊤) :
    ∃ (p : ℕ) (_ : Fact p.Prime) (K : Subgroup H) (_ : K.Normal), Z ≤ K ∧ K ≠ ⊤ ∧
      IsPGroup p (H ⧸ K) ∧
      ∀ (M : Subgroup (K ⧸ Z.subgroupOf K)) [M.Normal],
        IsPGroup p ((K ⧸ Z.subgroupOf K) ⧸ M) → M = ⊤ := by
  obtain ⟨p, hp, c, hc, hcX⟩ := exists_pElement_not_mem_commutator hnp
  obtain ⟨M, hMn, hMtop, hMp⟩ := exists_pQuotient_of_not_mem_commutator hc hcX
  letI := Fintype.ofFinite (Subgroup H)
  set K₀ := M.comap (QuotientGroup.mk' Z) with hK₀
  have hK₀n : K₀.Normal := hMn.comap _
  have hZK₀ : Z ≤ K₀ := fun z hz => by
    show QuotientGroup.mk' Z z ∈ M
    have h1 : QuotientGroup.mk' Z z = 1 := (QuotientGroup.eq_one_iff z).mpr hz
    rw [h1]; exact M.one_mem
  have hK₀top : K₀ ≠ ⊤ := by
    intro h
    apply hMtop
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective Z x
    have : y ∈ K₀ := h ▸ Subgroup.mem_top y
    exact this
  have hK₀p : IsPGroup p (H ⧸ K₀) := isPGroup_comap_quotient Z M hMp
  obtain ⟨K, hK, hmin⟩ := Finset.exists_min_image
    (Finset.univ.filter (fun K : Subgroup H =>
      ∃ _ : K.Normal, Z ≤ K ∧ K ≠ ⊤ ∧ IsPGroup p (H ⧸ K))) (fun K => Nat.card K)
    ⟨K₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hK₀n, hZK₀, hK₀top, hK₀p⟩⟩
  obtain ⟨hKn, hZK, hKtop, hKp⟩ := (Finset.mem_filter.mp hK).2
  haveI := hKn
  refine ⟨p, hp, K, hKn, hZK, hKtop, hKp, fun M hM hMp => ?_⟩
  exact eq_top_of_minimal Z K hZK hKtop hKp (fun K' [hK'n : K'.Normal] hZK' hK'top hK'p =>
    hmin K' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hK'n, hZK', hK'top, hK'p⟩)) M hMp

end

end CFSGOutside.Gagola
