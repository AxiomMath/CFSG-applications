import CFSGOutside.Gagola.Cor36
import CFSGOutside.Gagola.D8Branch
import CFSGOutside.Corpus.YoshidaTransfer
import CFSGOutside.Corpus.Order8Nonabelian
import CFSGOutside.Gagola.PCube
import CFSGOutside.Gagola.SkewSymm
import CFSGOutside.Gagola.L44Central

/-!
# Gagola, Lemma 4.4

A `p`-group of order `p⁴` of type f.r. is reductive: if `(H, Z, χ)` is fully ramified, `R/Z` is a
Sylow `p`-subgroup of `H/Z` of order `p⁴`, `K = O^p(H) Z` and `(R ∩ K)/Z` is nonabelian (so of order
`p³`), then `χ_K` has a single irreducible constituent.
-/

namespace CFSGOutside.Gagola

open scoped BigOperators Pointwise
open Classical CFSGOutside.Corpus

noncomputable section


section Wreath

/-- `C_p ≀ C_p`. -/
abbrev Wr (p : ℕ) := Multiplicative (ZMod p) ≀ᵣ Multiplicative (ZMod p)

theorem card_Wr (p : ℕ) [Fact p.Prime] : Nat.card (Wr p) = p ^ p * p := by
  rw [RegularWreathProduct.card]
  simp [Nat.card_eq_fintype_card, ZMod.card]

theorem q8_involution_unique : ∀ a b : QuaternionGroup 2, a ^ 2 = 1 → b ^ 2 = 1 → a ≠ 1 → b ≠ 1 →
    a = b := by decide

theorem wr_two_involutions : ∃ a b : Wr 2, a ^ 2 = 1 ∧ b ^ 2 = 1 ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  refine ⟨⟨fun _ => Multiplicative.ofAdd 1, 1⟩, ⟨1, Multiplicative.ofAdd 1⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sq]
    ext x
    · show Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 1 = 1
      decide
    · show (1 : Multiplicative (ZMod 2)) * 1 = 1
      rfl
  · rw [sq]
    ext x
    · show (1 : Multiplicative (ZMod 2)) * 1 = 1
      rfl
    · show Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 1 = 1
      decide
  · intro h
    have := congrArg (fun w : Wr 2 => w.left 1) h
    simp only at this
    exact absurd this (by decide)
  · intro h
    have := congrArg (fun w : Wr 2 => w.right) h
    simp only at this
    exact absurd this (by decide)
  · intro h
    have := congrArg (fun w : Wr 2 => w.right) h
    simp only at this
    exact absurd this (by decide)

theorem not_q8_equiv_wr : IsEmpty (QuaternionGroup 2 ≃* Wr 2) := by
  refine ⟨fun e => ?_⟩
  obtain ⟨a, b, ha, hb, ha1, hb1, hab⟩ := wr_two_involutions
  apply hab
  apply e.symm.injective
  refine q8_involution_unique _ _ ?_ ?_ ?_ ?_
  · rw [← map_pow, ha, map_one]
  · rw [← map_pow, hb, map_one]
  · intro h; exact ha1 (e.symm.injective (by rw [h, map_one]))
  · intro h; exact hb1 (e.symm.injective (by rw [h, map_one]))

/-- A nonabelian group of order `p³` other than `D₈` has no quotient `C_p ≀ C_p`. -/
theorem no_wreath_quotient [Order8Nonabelian] {PP : Type} [Group PP] [Finite PP] {p : ℕ}
    [hp : Fact p.Prime] (hcard : Nat.card PP = p ^ 3) (hnab : ∃ a b : PP, a * b ≠ b * a)
    (hnd8 : ¬ (p = 2 ∧ Nonempty (PP ≃* DihedralGroup 4))) :
    ∀ (K' : Subgroup PP) [K'.Normal], IsEmpty ((PP ⧸ K') ≃* Wr p) := by
  intro K' _
  refine ⟨fun e => ?_⟩
  have hc := Nat.card_congr e.toEquiv
  rw [card_Wr] at hc
  have hle : Nat.card (PP ⧸ K') ≤ p ^ 3 := by
    rw [← hcard]; exact Nat.card_le_card_of_surjective _ (QuotientGroup.mk_surjective)
  have hp2 := hp.out.two_le
  rcases Nat.lt_or_ge p 3 with h3 | h3
  · have hp2' : p = 2 := by omega
    subst hp2'
    -- `K' = ⊥` and `PP ≅ C₂ ≀ C₂`
    have hK : K' = ⊥ := by
      have h1 := K'.card_mul_index
      rw [Subgroup.index_eq_card, hc, hcard] at h1
      norm_num at h1
      first | exact h1 | exact Subgroup.card_eq_one.mp (by omega)
    have e' : PP ≃* Wr 2 :=
      (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hK.symm)).trans e
    rcases Order8Nonabelian.order8_nonabelian (by rw [hcard]; norm_num) hnab with hd | hq
    · exact hnd8 ⟨rfl, hd⟩
    · obtain ⟨q⟩ := hq
      exact not_q8_equiv_wr.false (q.symm.trans e')
  · have : p ^ 3 < p ^ p * p := by
      calc p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right hp.out.one_lt (by norm_num)
        _ = p ^ 3 * p := by ring
        _ ≤ p ^ p * p := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hp.out.pos h3)
    omega

end Wreath

variable {H : Type} [Group H] [Fintype H] {Z : Subgroup H} [hZ : Z.Normal] {χ : H → ℂ} {θ : Z → ℂ}
  {e : ℕ} {K R : Subgroup H} [hK : K.Normal]

/-- **Gagola, Lemma 4.4.** -/
theorem lemma_4_4 [YoshidaTransfer.{0}] [Order8Nonabelian] [ASevenOrExistsNormalPsl2]
    [CardMulAutPsl2GF] [SL2MinimalFaithfulZsigmondy] (hχ : χ ∈ Irr H) (hθ : θ ∈ Irr Z)
    (hres : pull Z.subtype χ = (e : ℂ) • θ) (he : e ^ 2 = Z.index) (hZK : Z ≤ K) (hZR : Z ≤ R)
    {p : ℕ} [hp : Fact p.Prime] (hRZ : Nat.card R = p ^ 4 * Nat.card Z) (hpR : ¬ p ∣ R.index)
    (hKR : ∀ h : H, ∃ x ∈ K, ∃ r ∈ R, h = x * r)
    (hD3 : Nat.card (R ⊓ K : Subgroup H) = p ^ 3 * Nat.card Z)
    (hnab : ∃ a ∈ R ⊓ K, ∃ b ∈ R ⊓ K, a * b * a⁻¹ * b⁻¹ ∉ Z)
    (hno : ∀ (M : Subgroup (K ⧸ Z.subgroupOf K)) [M.Normal],
      IsPGroup p ((K ⧸ Z.subgroupOf K) ⧸ M) → M = ⊤)
    {τ₁ τ₂ : K → ℂ} (hτ₁ : τ₁ ∈ Irr K) (hτ₂ : τ₂ ∈ Irr K)
    (hm₁ : mult (pull K.subtype χ) τ₁ ≠ 0) (hm₂ : mult (pull K.subtype χ) τ₂ ≠ 0) : τ₁ = τ₂ := by
  classical
  by_contra hne
  have hfr : FullyRamified Z χ := ⟨hZ, hχ, θ, e, hθ, hres, he⟩
  obtain ⟨⟨g, hgsp, hgZ⟩, hsurj, hcount⟩ := exists_special_of_two hχ hθ hres he hZK hZR hRZ hpR hKR
    hτ₁ hτ₂ hm₁ hm₂ hne
  obtain ⟨m, hm⟩ := nonfusion (ιDK K R) (θD_mem_irr hθ hZR hZK) (θD_inv hres he hχ) hsurj hgsp
  have hcardD : Nat.card (DD K R) = p ^ 3 * Nat.card Z := by
    have : Nat.card (DD K R) = Nat.card (R ⊓ K : Subgroup H) := by
      rw [show (DD K R) = (R ⊓ K).subgroupOf R from (Subgroup.inf_subgroupOf_left K R).symm]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    rw [this, hD3]
  have hcardND : Nat.card (ZD K R Z) = Nat.card Z := Nat.card_congr (eZD hZR hZK).toEquiv
  have hZ0 : 0 < Nat.card Z := Nat.card_pos
  have hDidx : (DD K R).index = p := by
    have h1 := (DD K R).card_mul_index
    rw [hcardD, hRZ] at h1
    have : p ^ 3 * Nat.card Z * (DD K R).index = p ^ 3 * Nat.card Z * p := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos (pow_pos hp.out.pos 3) hZ0) this
  haveI hNDn : (ZD K R Z).Normal := by
    exact hZ.comap (ιDH K R)
  have hQcard : Nat.card ((DD K R) ⧸ (ZD K R Z)) = p ^ 3 := by
    have h1 := (ZD K R Z).card_mul_index
    rw [Subgroup.index_eq_card, hcardND, hcardD] at h1
    exact Nat.eq_of_mul_eq_mul_left hZ0 (by rw [h1]; ring)
  obtain ⟨a₀, ha₀, b₀, hb₀, hab₀⟩ := hnab
  set a' : (DD K R) := ⟨⟨a₀, ha₀.1⟩, Subgroup.mem_subgroupOf.mpr ha₀.2⟩
  set b' : (DD K R) := ⟨⟨b₀, hb₀.1⟩, Subgroup.mem_subgroupOf.mpr hb₀.2⟩
  have hQnab : ∃ a b : (DD K R) ⧸ (ZD K R Z), a * b ≠ b * a := by
    refine ⟨(a' : (DD K R) ⧸ (ZD K R Z)), (b' : (DD K R) ⧸ (ZD K R Z)), fun h => hab₀ ?_⟩
    have := (comm_mem_iff_mk (N := (ZD K R Z)) a' b').mpr h
    exact this
  -- step (c): `g` is not central modulo `Z`
  have hgnc : ¬ ∀ d : (DD K R), d * g * d⁻¹ * g⁻¹ ∈ (ZD K R Z) := by
    intro hc
    obtain ⟨T, hTc, hTsp, hTdis⟩ := many_special_of_central (θD_mem_irr hθ hZR hZK)
      (θD_inv hres he hχ) hQcard hQnab hgsp hgZ hc
    have := hcount T hTsp hTdis
    omega
  -- the Sylow subgroup `S` of `X = K/Z`
  set ZK := Z.subgroupOf K
  set X := K ⧸ ZK
  set Q : K →* X := QuotientGroup.mk' ZK
  have hQ1 : ∀ x : K, Q x = 1 ↔ (x : H) ∈ Z := fun x => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  set P0 : Subgroup K := R.subgroupOf K
  set P : Subgroup X := P0.map Q
  have hRp : ∀ x : H, x ∈ R → x ^ p ^ 4 ∈ Z := by
    intro x hx
    have hc : Nat.card (R ⧸ Z.subgroupOf R) = p ^ 4 := by
      have h1 := (Z.subgroupOf R).card_mul_index
      rw [Subgroup.index_eq_card] at h1
      have hZc : Nat.card (Z.subgroupOf R) = Nat.card Z :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZR).toEquiv
      rw [hZc, hRZ, mul_comm] at h1
      exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
    have h2 : ((⟨x, hx⟩ : R) : R ⧸ Z.subgroupOf R) ^ p ^ 4 = 1 := by
      rw [← hc]; exact pow_card_eq_one'
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h2
    simpa using h2
  have hPp : IsPGroup p P := by
    rintro ⟨y, x, hx, rfl⟩
    refine ⟨4, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← map_pow, hQ1]
    simpa using hRp _ (Subgroup.mem_subgroupOf.mp hx)
  have hker : Q.ker ≤ P0 := by
    intro x hx
    rw [MonoidHom.mem_ker, hQ1] at hx
    exact Subgroup.mem_subgroupOf.mpr (hZR hx)
  have hP0idx : P0.index = R.index := by
    have h1 := P0.card_mul_index
    rw [card_eq_index_mul hKR, ← card_DD] at h1
    have hD0 : 0 < Nat.card (DD K R) := Nat.card_pos
    refine Nat.eq_of_mul_eq_mul_left hD0 ?_
    rw [h1]; ring
  have hPidx' : P.index = R.index := by
    rw [Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective ZK) hker, hP0idx]
  have hPidx : ¬ p ∣ P.index := by rw [hPidx']; exact hpR
  set S : Sylow p X := hPp.toSylow hPidx
  have hS : (S : Subgroup X) = P := rfl
  -- `|S| = p³`, `S` nonabelian
  have hcardK : Nat.card K = R.index * (p ^ 3 * Nat.card Z) := by
    rw [card_eq_index_mul hKR, hcardD]
  have hcardX : Nat.card X * Nat.card Z = Nat.card K := by
    have h1 := ZK.card_mul_index
    rw [Subgroup.index_eq_card] at h1
    have hZc : Nat.card ZK = Nat.card Z := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZK).toEquiv
    rw [hZc] at h1; rw [← h1]; ring
  have hScard : Nat.card (S : Subgroup X) = p ^ 3 := by
    have h1 : Nat.card P * P.index = Nat.card X := P.card_mul_index
    rw [hPidx'] at h1
    have hRi : 0 < R.index := Nat.pos_of_ne_zero R.index_ne_zero_of_finite
    have : Nat.card P * R.index * Nat.card Z = p ^ 3 * R.index * Nat.card Z := by
      rw [h1, hcardX, hcardK]; ring
    exact Nat.eq_of_mul_eq_mul_right hRi (Nat.eq_of_mul_eq_mul_right hZ0 this)
  set ιK : (DD K R) →* K := ιDK K R
  have hQι : ∀ d : (DD K R), Q (ιK d) ∈ (S : Subgroup X) :=
    fun d => ⟨ιK d, Subgroup.mem_subgroupOf.mpr (d : R).2, rfl⟩
  set Ψ : (DD K R) →* X := Q.comp ιK
  have hΨ1 : ∀ d : (DD K R), Ψ d = 1 ↔ d ∈ (ZD K R Z) := fun d => hQ1 (ιK d)
  have hcommQ : ∀ d d' : (DD K R), (Q (ιK d) * Q (ιK d') = Q (ιK d') * Q (ιK d)) ↔
      d * d' * d⁻¹ * d'⁻¹ ∈ (ZD K R Z) := by
    intro d d'
    rw [← hΨ1]
    show Ψ d * Ψ d' = Ψ d' * Ψ d ↔ _
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
  have hSnab : ∃ x y : (S : Subgroup X), x * y ≠ y * x := by
    refine ⟨⟨_, hQι a'⟩, ⟨_, hQι b'⟩, fun h => hab₀ ?_⟩
    have h' := congrArg Subtype.val h
    simp only [Subgroup.coe_mul] at h'
    exact (hcommQ a' b').mp h'
  set c := Q (ιK g)
  have hcS : c ∈ (S : Subgroup X) := hQι g
  -- `c` is not central in `S`
  have hcnc : ¬ ∀ y ∈ (S : Subgroup X), y * c = c * y := by
    intro hy
    apply hgnc
    intro d
    exact (hcommQ d g).mp (hy _ (hQι d))
  by_cases hD8 : p = 2 ∧ Nonempty ((S : Subgroup X) ≃* DihedralGroup 4)
  · -- the dihedral case
    obtain ⟨rfl, ⟨eD⟩⟩ := hD8
    have hidx : K.index = 2 := by
      have h1 := K.card_mul_index
      have h2 := R.card_mul_index
      rw [hcardK, hRZ] at *
      have : R.index * (2 ^ 3 * Nat.card Z) * K.index = R.index * (2 ^ 3 * Nat.card Z) * 2 := by
        rw [h1, ← h2]; ring
      exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos (Nat.pos_of_ne_zero R.index_ne_zero_of_finite)
        (Nat.mul_pos (by norm_num) hZ0)) this
    refine d8_branch hfr K hZK hidx (fun P' => ⟨(Sylow.equiv P' S).trans eD⟩) ?_
    intro N hN h2
    exact @hno N hN h2
  · -- Yoshida
    have hW := no_wreath_quotient (PP := (S : Subgroup X)) hScard hSnab (by
      rintro ⟨rfl, h⟩; exact hD8 ⟨rfl, h⟩)
    have hY := YoshidaTransfer.inf_commutator_eq_inf_map_commutator_normalizer S hW
    -- `S ≤ X'`
    have hSX : (S : Subgroup X) ≤ commutator X := by
      intro y hy
      by_contra hyX
      obtain ⟨M, hMn, hMtop, hMp⟩ :=
        exists_pQuotient_of_not_mem_commutator (pow_eq_one_of_mem_sylow hy) hyX
      exact hMtop (@hno M hMn hMp)
    set NS := Subgroup.normalizer ((S : Subgroup X) : Set X)
    have hcN : c ∈ (commutator NS).map NS.subtype := by
      have : c ∈ (S : Subgroup X) ⊓ commutator X := ⟨hcS, hSX hcS⟩
      rw [hY] at this
      exact this.2
    obtain ⟨cN, hcNmem, hcNc⟩ := hcN
    set P' : Subgroup NS := (S : Subgroup X).subgroupOf NS
    haveI : P'.Normal := Subgroup.normal_in_normalizer
    have hcNc' : ((cN : NS) : X) = c := hcNc
    have hcP' : cN ∈ P' := by
      rw [Subgroup.mem_subgroupOf, hcNc']; exact hcS
    set φ : P' →* Abelianization P' := Abelianization.of
    have hV1 : φ.transfer cN = 1 := Abelianization.commutator_subset_ker _ hcNmem
    have hconj : ∀ n₀ : NS, φ ⟨n₀⁻¹ * cN * n₀, by
        simpa using ‹P'.Normal›.conj_mem cN hcP' n₀⁻¹⟩ = φ ⟨cN, hcP'⟩ := by
      intro n₀
      obtain ⟨y, hy⟩ := n₀
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective ZK y
      -- `x⁻¹ (g m) x ∈ R`
      have hmem : Q (x⁻¹ * ιK g * x) ∈ (S : Subgroup X) := by
        have := (Subgroup.mem_normalizer_iff.mp (NS.inv_mem hy) c).mp hcS
        have e : Q (x⁻¹ * ιK g * x) = (Q x)⁻¹ * c * (Q x)⁻¹⁻¹ := by
          rw [inv_inv, map_mul, map_mul, map_inv]
        rw [e]; exact this
      obtain ⟨w, hw, hwx⟩ := hmem
      have hmZ : (((m : (DD K R)) : R) : H) ∈ Z := m.2
      have hxR : ((x⁻¹ * ιK (g * m) * x : K) : H) ∈ R := by
        have h1 : Q (w⁻¹ * (x⁻¹ * ιK g * x)) = 1 := by rw [map_mul, map_inv, hwx, inv_mul_cancel]
        rw [hQ1] at h1
        have h2 := R.mul_mem (R.mul_mem (Subgroup.mem_subgroupOf.mp hw) (hZR h1))
          (hZR (hZ.conj_mem _ hmZ (x⁻¹ : K)))
        convert h2 using 1
        simp only [ιK, map_mul, Subgroup.coe_mul, Subgroup.coe_inv, ιDK_apply]
        group
      set d' : (DD K R) := ⟨⟨_, hxR⟩, Subgroup.mem_subgroupOf.mpr (x⁻¹ * ιK (g * m) * x).2⟩
      obtain ⟨u, hu⟩ := hm x⁻¹ d' (by ext; simp [d', ιK])
      -- `x⁻¹ c x = Q(u) c Q(u)⁻¹` in `S`
      have key : (Q x)⁻¹ * c * Q x = Q (ιK u) * c * (Q (ιK u))⁻¹ := by
        have hu' : ιDH K R (u⁻¹ * d' * u * g⁻¹) ∈ Z := hu
        have e1 : ((x⁻¹ * ιK g * x * (ιK u * ιK g * (ιK u)⁻¹)⁻¹ : K) : H) =
            (((ιK u : K) : H) * (ιDH K R (u⁻¹ * d' * u * g⁻¹)) * ((ιK u : K) : H)⁻¹) *
            ((((ιK u : K) : H) * ((g : R) : H) * ((ιK u : K) : H)⁻¹) *
              (((x : K) : H)⁻¹ * (((m : (DD K R)) : R) : H)⁻¹ * ((x : K) : H)) *
              (((ιK u : K) : H) * ((g : R) : H) * ((ιK u : K) : H)⁻¹)⁻¹) := by
          simp only [d', ιK, ιDH_apply, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv,
            ιDK_apply]
          group
        have hz : ((x⁻¹ * ιK g * x * (ιK u * ιK g * (ιK u)⁻¹)⁻¹ : K) : H) ∈ Z := by
          rw [e1]
          refine Z.mul_mem ?_ ?_
          · have := hZ.conj_mem _ hu' ((ιK u : K) : H); simpa [mul_assoc] using this
          · have h1 := hZ.conj_mem _ (Z.inv_mem hmZ) ((x : K) : H)⁻¹
            have h2 := hZ.conj_mem _ h1 (((ιK u : K) : H) * ((g : R) : H) * ((ιK u : K) : H)⁻¹)
            simpa [mul_assoc] using h2
        have h1 := (hQ1 _).mpr hz
        rw [map_mul, map_inv, mul_inv_eq_one] at h1
        simpa [c, map_mul, map_inv] using h1
      -- the element `Q(u)` of `P'`
      have huN : Q (ιK u) ∈ NS := Subgroup.le_normalizer (hQι u)
      set uN : NS := ⟨Q (ιK u), huN⟩
      have huP' : uN ∈ P' := Subgroup.mem_subgroupOf.mpr (hQι u)
      have hel : (⟨(⟨Q x, hy⟩ : NS)⁻¹ * cN * ⟨Q x, hy⟩, by
          simpa using ‹P'.Normal›.conj_mem cN hcP' (⟨Q x, hy⟩ : NS)⁻¹⟩ : P') =
          ⟨uN, huP'⟩ * ⟨cN, hcP'⟩ * ⟨uN, huP'⟩⁻¹ := by
        apply Subtype.ext; apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, uN]
        rw [hcNc']
        exact key
      rw [hel, map_mul, map_mul, map_inv, mul_comm (φ _) (φ _), mul_inv_cancel_right]
    have hV := transfer_eq_pow_of_normal φ hcP' hconj
    rw [hV1] at hV
    -- `φ cN = 1`
    have hord : ∃ k : ℕ, (⟨cN, hcP'⟩ : P') ^ p ^ k = 1 := by
      obtain ⟨k, hk⟩ := pow_eq_one_of_mem_sylow hcS
      refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
      rw [show ((cN : NS) : X) = c from hcNc]; exact hk
    obtain ⟨k, hk⟩ := hord
    have hidxP' : ¬ p ∣ P'.index := by
      intro hd
      apply hPidx
      have : P'.index ∣ (S : Subgroup X).index :=
        Subgroup.relIndex_dvd_index_of_le Subgroup.le_normalizer
      exact hS ▸ hd.trans this
    have hφ1 : φ ⟨cN, hcP'⟩ = 1 := by
      have h1 : φ ⟨cN, hcP'⟩ ^ p ^ k = 1 := by rw [← map_pow, hk, map_one]
      have hcop : Nat.Coprime (p ^ k) P'.index :=
        Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hidxP')
      have := (pow_gcd_eq_one (a := φ ⟨cN, hcP'⟩)).mpr ⟨h1, hV.symm⟩
      rwa [hcop.gcd_eq_one, pow_one] at this
    have hcomm : (⟨cN, hcP'⟩ : P') ∈ commutator P' := by
      rw [← Abelianization.ker_of]; exact hφ1
    -- so `c` is central in `S`
    apply hcnc
    intro y hyS
    set eP : P' ≃* (S : Subgroup X) := Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer
    have hmap : (commutator P').map eP.toMonoidHom = commutator (S : Subgroup X) := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ eP.surjective]
    have hc' : (⟨c, hcS⟩ : (S : Subgroup X)) ∈ commutator (S : Subgroup X) := by
      rw [← hmap]
      refine ⟨⟨cN, hcP'⟩, hcomm, Subtype.ext ?_⟩
      exact hcNc'
    have hcen : (⟨c, hcS⟩ : (S : Subgroup X)) ∈ Subgroup.center (S : Subgroup X) := by
      refine (Subgroup.commutator_le.mpr fun a _ b _ =>
        pcube_comm_mem_center hScard hSnab a b) hc'
    have := Subgroup.mem_center_iff.mp hcen ⟨y, hyS⟩
    exact congrArg Subtype.val this

end

end CFSGOutside.Gagola
