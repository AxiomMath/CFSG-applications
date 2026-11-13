import CFSGOutside.Gagola.Thm25
import CFSGOutside.Gagola.PSL2
import CFSGOutside.Corpus.WalterSplit
import CFSGOutside.Corpus.CardOfReeTitsModelTwistedG2
import CFSGOutside.Corpus.CardWalterJ1

/-!
# Gagola, Theorem 4.5, in the abelian Sylow 2-subgroup case, from Walter's theorem

Let `(H, Z, χ)` be a fully ramified triple and `Z ≤ K ⊴ H`.

* `not_simple_quotient`: `H/K` is not a nonabelian simple group with an abelian Sylow 2-subgroup.
  By Walter's theorem such a group is `PSL(2, q)`, `²G₂(3^f)` or `J₁`. In `PSL(2, q)` two primes have
  nontrivial cyclic Sylow subgroups, against Theorem 2.5(a). `²G₂(3^f)` and `J₁` have Sylow 2-subgroups of
  order 8; by Lemma 2.3, `8 = b² s` and `H/K` has a subgroup of index `s ∈ {2, 8}`, so `|H/K| ≤ 8!`.
* `typeFR_perfect`: a perfect group of type f.r. whose Sylow 2-subgroups are abelian is trivial. This is
  Gagola's Theorem 4.5 ("groups of type f.r. are solvable") for perfect groups with abelian Sylow
  2-subgroups.

The inputs are the classes `WalterSplit`, `CardOfReeTitsModelTwistedG2` and `CardWalterJ1`.
-/

namespace CFSGOutside.Gagola

open Classical CFSGOutside.Corpus
open scoped MatrixGroups

noncomputable section

section Group

theorem cyclic_sylow_of_equiv {X Y : Type*} [Group X] [Group Y] [Finite X] (φ : X ≃* Y) {p : ℕ}
    [Fact p.Prime] (h : ∀ P : Sylow p Y, IsCyclic (P : Subgroup Y) ∧ Nat.card P ≠ 1) (P : Sylow p X) :
    IsCyclic (P : Subgroup X) ∧ Nat.card P ≠ 1 := by
  let P' := P.mapSurjective (f := φ.toMonoidHom) φ.surjective
  obtain ⟨hc, hn⟩ := h P'
  have hP' : (P' : Subgroup Y) = (P : Subgroup X).map φ.toMonoidHom := Sylow.coe_mapSurjective _ _
  have hc' : IsCyclic ((P : Subgroup X).map φ.toMonoidHom) := hP' ▸ hc
  have hinj : Function.Injective (φ.toMonoidHom.subgroupMap (P : Subgroup X)) := fun a b hab =>
    Subtype.ext (φ.injective (congrArg Subtype.val hab))
  refine ⟨isCyclic_of_injective _ hinj, ?_⟩
  rwa [hP', Subgroup.card_map_of_injective φ.injective] at hn

theorem isMulCommutative_map {A B : Type*} [Group A] [Group B] (f : A →* B) (S : Subgroup A)
    [h : IsMulCommutative S] : IsMulCommutative (S.map f) := by
  refine ⟨⟨fun x y => ?_⟩⟩
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy⟩ := y
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  rw [← map_mul, ← map_mul]
  congr 1
  exact congrArg Subtype.val (h.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem index_ne_two_of_simple {G : Type*} [Group G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (M : Subgroup G) : M.index ≠ 2 := by
  intro h
  haveI := Subgroup.normal_of_index_eq_two h
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M with rfl | rfl
  · rw [Subgroup.index_bot] at h
    haveI : IsCyclic G := isCyclic_of_prime_card h
    letI := IsCyclic.commGroup (α := G)
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab (mul_comm a b)
  · rw [Subgroup.index_top] at h
    exact absurd h (by norm_num)

theorem card_le_factorial_index {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] {M : Subgroup G}
    (hM : M ≠ ⊤) : Nat.card G ≤ M.index.factorial := by
  have hcore : M.normalCore = ⊥ := by
    rcases (M.normalCore_normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact absurd (eq_top_iff.mpr (h ▸ M.normalCore_le)) hM
  have hinj : Function.Injective (MulAction.toPermHom G (G ⧸ M)) := by
    rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.normalCore_eq_ker, hcore]
  calc Nat.card G ≤ Nat.card (Equiv.Perm (G ⧸ M)) := Nat.card_le_card_of_injective _ hinj
    _ = M.index.factorial := by rw [Nat.card_perm]; rfl

/-- A finite nontrivial group has a simple quotient. -/
theorem exists_simple_quotient (G : Type*) [Group G] [Finite G] [Nontrivial G] :
    ∃ (M : Subgroup G) (_ : M.Normal), IsSimpleGroup (G ⧸ M) := by
  letI := Fintype.ofFinite (Subgroup G)
  obtain ⟨M, hM, hmax⟩ := Finset.exists_max_image
    (Finset.univ.filter (fun M : Subgroup G => M.Normal ∧ M ≠ ⊤)) (fun M => Nat.card M)
    ⟨⊥, Finset.mem_filter.mpr ⟨Finset.mem_univ _, inferInstance, bot_ne_top⟩⟩
  obtain ⟨hMn, hMtop⟩ := (Finset.mem_filter.mp hM).2
  haveI := hMn
  refine ⟨M, hMn, ?_⟩
  obtain ⟨g, hg⟩ : ∃ g, g ∉ M := by
    by_contra hc; push Not at hc; exact hMtop (eq_top_iff.mpr fun g _ => hc g)
  haveI : Nontrivial (G ⧸ M) := ⟨⟨(g : G ⧸ M), 1, fun h => hg ((QuotientGroup.eq_one_iff g).mp h)⟩⟩
  refine ⟨fun N hN => ?_⟩
  set N' := N.comap (QuotientGroup.mk' M)
  have hN' : N'.Normal := hN.comap _
  have hMN : M ≤ N' := by
    intro m hm
    show QuotientGroup.mk' M m ∈ N
    have h1 : QuotientGroup.mk' M m = 1 := (QuotientGroup.eq_one_iff m).mpr hm
    rw [h1]
    exact N.one_mem
  have hmapN : N'.map (QuotientGroup.mk' M) = N :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective M) N
  by_cases htop : N' = ⊤
  · right
    rw [← hmapN, htop, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective M)]
  · left
    have hle := hmax N' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hN', htop⟩)
    have heq : M = N' := Subgroup.eq_of_le_of_card_ge hMN hle
    rw [← hmapN, ← heq, QuotientGroup.map_mk'_self]

end Group

section Numbers

theorem factorization_two_pow_mul {k m : ℕ} (hm : Odd m) : (2 ^ k * m).factorization 2 = k := by
  rw [Nat.factorization_mul (pow_ne_zero _ two_ne_zero) hm.pos.ne',
    Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (fun h => (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h)),
    add_zero]

theorem three_pow_odd_mod_eight (a : ℕ) : 3 ^ (2 * a + 1) % 8 = 3 := by
  induction a with
  | zero => norm_num
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring, pow_add, Nat.mul_mod, ih]
    norm_num

/-- `|²G₂(3^(2a+1))|` has 2-part `8`. -/
theorem factorization_ordRee (a : ℕ) : (Open.ordRee (3 ^ (2 * a + 1))).factorization 2 = 3 := by
  unfold Open.ordRee
  obtain ⟨q, hq⟩ : ∃ q, q = 3 ^ (2 * a + 1) := ⟨_, rfl⟩
  rw [← hq]
  have hq8 : q % 8 = 3 := hq ▸ three_pow_odd_mod_eight a
  have hA8 : q ^ 3 % 8 = 3 := by rw [Nat.pow_mod, hq8]
  obtain ⟨A, hA⟩ : ∃ A, A = q ^ 3 := ⟨_, rfl⟩
  rw [← hA] at hA8 ⊢
  have e1 : A + 1 = 4 * ((A + 1) / 4) := by omega
  have e2 : q - 1 = 2 * ((q - 1) / 2) := by omega
  rw [e1, e2, show A * (4 * ((A + 1) / 4)) * (2 * ((q - 1) / 2)) =
    2 ^ 3 * (A * ((A + 1) / 4) * ((q - 1) / 2)) by ring]
  refine factorization_two_pow_mul ((Odd.mul ?_ ?_).mul ?_) <;> exact Nat.odd_iff.mpr (by omega)

theorem ordRee_large {a : ℕ} (ha : 1 ≤ a) : 40320 < Open.ordRee (3 ^ (2 * a + 1)) := by
  unfold Open.ordRee
  have hq : 27 ≤ 3 ^ (2 * a + 1) := (Nat.pow_le_pow_right (by norm_num) (by omega) : 3 ^ 3 ≤ _)
  have h1 : 19683 ≤ (3 ^ (2 * a + 1)) ^ 3 := (Nat.pow_le_pow_left hq 3 : 27 ^ 3 ≤ _)
  calc 40320 < 19683 * (19683 + 1) * 1 := by norm_num
    _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul h1 (by omega)) (by omega)

end Numbers

section Main

variable {H : Type} [Group H] [Fintype H] {Z : Subgroup H} {χ : H → ℂ} {θ : Z → ℂ} {e : ℕ}

/-- **Gagola, Lemma 2.3 at `p = 2`**: if `H/K` is simple nonabelian with Sylow 2-subgroups of order 8,
then `|H/K| ≤ 8!`. -/
theorem card_le_of_sylow_two_eight [Z.Normal] (hχ : χ ∈ Irr H) (hθ : θ ∈ Irr Z)
    (hres : pull Z.subtype χ = (e : ℂ) • θ) (he : e ^ 2 = Z.index) (K : Subgroup H) [K.Normal]
    (hZK : Z ≤ K) [IsSimpleGroup (H ⧸ K)] (hnonab : ∃ a b : H ⧸ K, a * b ≠ b * a)
    (h8 : (Nat.card (H ⧸ K)).factorization 2 = 3) : Nat.card (H ⧸ K) ≤ 40320 := by
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 (H ⧸ K)))
  obtain ⟨b, s, hb, hbs, M, hM⟩ := thm_2_5_sq hχ hθ hres he K hZK P
  rw [Sylow.card_eq_multiplicity, h8] at hbs
  have hs0 : 0 < s := Nat.pos_of_ne_zero (by rintro rfl; simp at hbs)
  have hb2 : b ^ 2 ≤ 8 := by
    calc b ^ 2 ≤ b ^ 2 * s := Nat.le_mul_of_pos_right _ hs0
      _ = 8 := by rw [hbs]; norm_num
  have hb3 : b ≤ 2 := by nlinarith
  have hs : s = 2 ∨ s = 8 := by interval_cases b <;> simp at hbs <;> omega
  rcases hs with rfl | rfl
  · exact absurd hM (index_ne_two_of_simple hnonab M)
  · have hMne : M ≠ ⊤ := by rintro rfl; simp at hM
    have := card_le_factorial_index hMne
    rw [hM] at this
    simpa [Nat.factorial] using this

/-- **Theorem T1.** Let `(H, Z, χ)` be a fully ramified triple and `Z ≤ K ⊴ H`. Then `H/K` is not a
nonabelian simple group with an abelian Sylow 2-subgroup. -/
theorem not_simple_quotient [WalterSplit] [CardOfReeTitsModelTwistedG2] [CardWalterJ1]
    (hfr : FullyRamified Z χ) (K : Subgroup H) [K.Normal] (hZK : Z ≤ K) [IsSimpleGroup (H ⧸ K)]
    (hnonab : ∃ a b : H ⧸ K, a * b ≠ b * a) (P : Sylow 2 (H ⧸ K))
    (hP : IsMulCommutative (P : Subgroup (H ⧸ K))) : False := by
  obtain ⟨hZ, hχ, θ, e, hθ, hres, he⟩ := hfr
  haveI := hZ
  have two_primes : ∀ (Y : Type) [Group Y], (H ⧸ K ≃* Y) →
      (∃ p r : ℕ, ∃ _ : Fact p.Prime, ∃ _ : Fact r.Prime, p ≠ r ∧
        (∀ P : Sylow p Y, IsCyclic (P : Subgroup Y) ∧ Nat.card P ≠ 1) ∧
        (∀ P : Sylow r Y, IsCyclic (P : Subgroup Y) ∧ Nat.card P ≠ 1)) → False := by
    intro Y _ φ ⟨p, r, hp, hr, hpr, h1, h2⟩
    obtain ⟨P1⟩ := (inferInstance : Nonempty (Sylow p (H ⧸ K)))
    obtain ⟨P2⟩ := (inferInstance : Nonempty (Sylow r (H ⧸ K)))
    obtain ⟨c1, n1⟩ := cyclic_sylow_of_equiv φ h1 P1
    obtain ⟨c2, n2⟩ := cyclic_sylow_of_equiv φ h2 P2
    exact thm_2_5_a hχ hθ hres he K hZK hpr P1 c1 n1 P2 c2 n2
  rcases WalterSplit.walter_split (H ⧸ K) hnonab P hP with
    ⟨f, hf, ⟨φ⟩⟩ | ⟨p, f, hp, hpodd, hf0, h5, h8, ⟨φ⟩⟩ | ⟨f, -, -, hRee⟩ | hJ
  · -- `PSL(2, 2^f)`, `f ≥ 2`
    letI := Fintype.ofFinite (GaloisField 2 f)
    have hcard : Fintype.card (GaloisField 2 f) = 2 ^ f := by
      rw [← Nat.card_eq_fintype_card, GaloisField.card 2 f (by omega)]
    exact two_primes _ φ (psl2_two_primes _ (Or.inl ⟨f, hf, hcard⟩))
  · -- `PSL(2, q)`, `q ≡ ±3 (mod 8)`, `q ≥ 5`
    letI := Fintype.ofFinite (GaloisField p f)
    have hcard : Fintype.card (GaloisField p f) = p ^ f := by
      rw [← Nat.card_eq_fintype_card, GaloisField.card p f (by omega)]
    exact two_primes _ φ (psl2_two_primes _ (Or.inr ⟨by rw [hcard]; exact hpodd.pow,
      by rw [hcard]; exact h5, by rw [hcard]; exact h8⟩))
  · -- `²G₂(3^f)`
    obtain ⟨-, a, ha1, rfl, hcardX⟩ := CardOfReeTitsModelTwistedG2.card_of_reeTitsModel_twistedG2 hRee
    have hle := card_le_of_sylow_two_eight hχ hθ hres he K hZK hnonab
      (by rw [hcardX]; exact factorization_ordRee a)
    rw [hcardX] at hle
    exact absurd hle (by have := ordRee_large ha1; omega)
  · -- `J₁`
    obtain ⟨φ⟩ := hJ
    have hcardX : Nat.card (H ⧸ K) = 175560 := by
      rw [Nat.card_congr φ.toEquiv, CardWalterJ1.card_walterJ1]
    have hle := card_le_of_sylow_two_eight hχ hθ hres he K hZK hnonab (by
      rw [hcardX, show (175560 : ℕ) = 2 ^ 3 * 21945 by norm_num]
      exact factorization_two_pow_mul (by decide))
    rw [hcardX] at hle
    exact absurd hle (by norm_num)

/-- **Corollary (Gagola, Theorem 4.5, for perfect groups with abelian Sylow 2-subgroups).** A perfect group
of type f.r. whose Sylow 2-subgroups are abelian is trivial. -/
theorem typeFR_perfect [WalterSplit] [CardOfReeTitsModelTwistedG2] [CardWalterJ1] {G : Type} [Group G]
    (hG : IsTypeFR G) (hperf : commutator G = ⊤)
    (hab : ∀ P : Sylow 2 G, IsMulCommutative (P : Subgroup G)) : Subsingleton G := by
  obtain ⟨H, _, _, Z, hZ, χ, hfr, ⟨eG⟩⟩ := hG
  haveI : Finite G := Finite.of_equiv _ eG.symm.toEquiv
  by_contra hnt
  rw [not_subsingleton_iff_nontrivial] at hnt
  obtain ⟨M, hMn, hsimple⟩ := exists_simple_quotient G
  -- `G/M` is nonabelian since `G` is perfect
  have hnonab : ∃ a b : G ⧸ M, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    have hle : commutator G ≤ M := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [← QuotientGroup.eq_one_iff, commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv, hc (a : G ⧸ M) (b : G ⧸ M)]
      group
    rw [hperf, top_le_iff] at hle
    subst hle
    obtain ⟨x, y, hxy⟩ := (inferInstance : Nontrivial (G ⧸ (⊤ : Subgroup G)))
    exact hxy (@Subsingleton.elim _ QuotientGroup.subsingleton_quotient_top x y)
  -- `H → G/M`
  let f : H →* G ⧸ M := (QuotientGroup.mk' M).comp (eG.symm.toMonoidHom.comp (QuotientGroup.mk' Z))
  have hf : Function.Surjective f := fun y => by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective M y
    obtain ⟨h, hh⟩ := QuotientGroup.mk'_surjective Z (eG g)
    refine ⟨h, ?_⟩
    simp only [f, MonoidHom.comp_apply, QuotientGroup.mk'_apply, MulEquiv.coe_toMonoidHom] at hh ⊢
    rw [hh, MulEquiv.symm_apply_apply]
  have hZK : Z ≤ f.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    simp [f, (QuotientGroup.eq_one_iff z).mpr hz]
  let ψ : H ⧸ f.ker ≃* G ⧸ M := QuotientGroup.quotientKerEquivOfSurjective f hf
  haveI : Nontrivial (H ⧸ f.ker) := ψ.toEquiv.nontrivial
  haveI : IsSimpleGroup (H ⧸ f.ker) :=
    IsSimpleGroup.isSimpleGroup_of_surjective ψ.symm.toMonoidHom ψ.symm.surjective
  have hnonab' : ∃ a b : H ⧸ f.ker, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    refine ⟨ψ.symm a, ψ.symm b, fun h => hab ?_⟩
    have := congrArg ψ h
    simpa using this
  obtain ⟨P₀⟩ := (inferInstance : Nonempty (Sylow 2 G))
  haveI := hab P₀
  let g' : G →* H ⧸ f.ker := ψ.symm.toMonoidHom.comp (QuotientGroup.mk' M)
  have hg' : Function.Surjective g' := ψ.symm.surjective.comp (QuotientGroup.mk'_surjective M)
  let P := P₀.mapSurjective hg'
  have hP : IsMulCommutative (P : Subgroup (H ⧸ f.ker)) := by
    rw [show (P : Subgroup (H ⧸ f.ker)) = (P₀ : Subgroup G).map g' from Sylow.coe_mapSurjective _ _]
    exact isMulCommutative_map g' _
  exact not_simple_quotient hfr f.ker hZK hnonab' P hP

end Main

end

end CFSGOutside.Gagola
