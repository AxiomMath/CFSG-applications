import CFSGOutside.ChillagSonn.Lemma12
import CFSGOutside.ChillagSonn.Simple
import CFSGOutside.ChillagSonn.GLTwo
import CFSGOutside.ChillagSonn.DicksonCoprime
import CFSGOutside.ChillagSonn.CyclicSylow

/-!
# Lemma (1.9), one prime: a quasisimple group acting on a metacyclic `r`-group

Let `A₀ ⊴ A` be quasisimple with `|Z(A₀)| ≤ 2`, `|A : A₀| ≤ 2` and `C_A(A₀) ≤ A₀`, and let `A` act on a metacyclic
`r`-group `V` (`r` odd), with `r ∤ |A|` if `V` is not cyclic. Then `A₀` acts trivially on `V`, unless `A = A₀`,
`|Z(A₀)| = 2` and `|A₀/Z(A₀)| = 60` (the case `A ≅ SL(2,5)`).

* If `V` is cyclic, `Aut(V)` is abelian and the perfect group `A₀` acts trivially.
* Otherwise `A` acts on `W = V/Φ(V)`, of order `r²`, with the same kernel (Burnside: an automorphism trivial on `W`
  has `r`-power order). `Aut(W) ≤ GL(2, r)`, and the perfect image of `A₀` lies in `SL(2, r)`, whose only involution
  is `-1`. If `A₀` acts nontrivially, either its image is `A₀/Z(A₀)` (simple, with at least two involutions —
  impossible), or `A₀` acts faithfully and `A₀/Z(A₀)` embeds in `PSL(2, r) ≤ PSL(2, r²)`; Dickson's theorem then
  gives `|A₀/Z(A₀)| = 60`. If moreover `|A : A₀| = 2`, `A` acts faithfully and its image in `PSL(2, r²)` is a
  nonsolvable `r'`-group of order at least 120, contradicting Dickson's theorem again. This replaces the paper's
  appeal to Bloom's list of subgroups of `PSL(3, q)` and his Lemma 3.3 [2].
-/

namespace CFSGOutside.ChillagSonn

open CFSGOutside.Corpus CFSGOutside.Corpus.OrderReductions.FrattiniAutomorphisms
open scoped commutatorElement

/-- A homomorphism from a perfect group to a commutative group is trivial. -/
theorem map_eq_one_of_perfect {P M : Type*} [Group P] [Group M] (hP : commutator P = ⊤) (f : P →* M)
    (hM : ∀ a b : M, a * b = b * a) (x : P) : f x = 1 := by
  have hle : commutator P ≤ f.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hM _ _
  exact hle (hP ▸ Subgroup.mem_top x)

theorem orderOf_eq_one_of_coprime {M : Type*} [Group M] {r n k : ℕ} [Fact r.Prime] (x : M) (h1 : x ^ (r ^ k) = 1)
    (h2 : x ^ n = 1) (hr : ¬ r ∣ n) : x = 1 := by
  have h := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
  have hcop : Nat.Coprime (r ^ k) n := Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hr)
  rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at h
  exact h

variable [DicksonPsl2SubgroupClassification.{0}] [FrattiniElementaryQuotient.{0}] [FrattiniAutomorphismKernel.{0}]
  [TwoLePRankOfIsSimpleGroup.{0}] [MinimalNormalSimpleFactors.{0}]

/-- **Lemma (1.9), the case of an `r`-group.** -/
theorem le_ker_of_action {A V : Type} [Group A] [Finite A] [Group V] [Finite V] {r : ℕ} [hr : Fact r.Prime]
    (hr2 : r ≠ 2) (hV : IsPGroup r V) (hVm : IsMetacyclic V) (hcop : ¬ IsCyclic V → ¬ r ∣ Nat.card A)
    (φ : A →* MulAut V) (A₀ : Subgroup A) [A₀.Normal] (hq : IsQuasisimple A₀)
    (hZ : Nat.card (Subgroup.center A₀) ≤ 2) (hidx : A₀.index ≤ 2)
    (hCA : Subgroup.centralizer (A₀ : Set A) ≤ A₀)
    (hexc : A₀ = ⊤ → Nat.card (Subgroup.center A₀) = 2 →
      Nat.card (A₀ ⧸ Subgroup.center A₀) = 60 → IsCyclic V) :
    A₀ ≤ φ.ker := by
  classical
  have hperf : commutator A₀ = ⊤ := hq.1.commutator_eq_top
  by_cases hcyc : IsCyclic V
  · intro a ha
    exact map_eq_one_of_perfect hperf (φ.comp A₀.subtype) (fun σ τ => mulAut_comm_of_isCyclic σ τ) ⟨a, ha⟩
  have hrA := hcop hcyc
  -- the Frattini quotient `W`, of order `r²`
  set W := V ⧸ frattini V
  obtain ⟨-, hWc, hWe, -⟩ := FrattiniElementaryQuotient.frattini_elementary_quotient hV
  have hWcard : Nat.card W = r ^ 2 := card_quotient_frattini_eq hV hVm hcyc
  set ψ : A →* MulAut W := (quotientAutomorphism (frattini V)).comp φ
  have hker : ψ.ker ≤ φ.ker := by
    intro a ha
    obtain ⟨-, hK⟩ := FrattiniAutomorphismKernel.frattini_automorphism_kernel hV
    obtain ⟨k, hk⟩ := hK ⟨φ a, ha⟩
    have h1 : (φ a) ^ (r ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have h2 : (φ a) ^ (Nat.card A) = 1 := by rw [← map_pow, pow_card_eq_one', map_one]
    exact orderOf_eq_one_of_coprime (φ a) h1 h2 hrA
  refine le_trans ?_ hker
  obtain ⟨ρ, hρ⟩ := exists_injective_mulAut_to_GL (W := W) (fun a b => hWc.is_comm.comm a b) hWe hWcard
  set θ : A →* GL (Fin 2) (ZMod r) := ρ.comp ψ
  have hθker : θ.ker = ψ.ker := by
    ext a
    simp only [θ, MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact ⟨fun h => hρ (by rw [h, map_one]), fun h => by rw [h, map_one]⟩
  rw [← hθker]
  by_contra hnot
  have hchar : ringChar (ZMod r) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hr2
  -- the image of `A₀` lies in `SL(2, r)`
  have hdet : ∀ a ∈ A₀, ((θ a : GL (Fin 2) (ZMod r)) : Matrix (Fin 2) (Fin 2) (ZMod r)).det = 1 := by
    intro a ha
    have : Group.IsPerfect A₀ := hq.1
    have hP : Group.IsPerfect (A₀.map θ) :=
      Group.IsPerfect.ofSurjective (f := θ.subgroupMap A₀) (MonoidHom.subgroupMap_surjective _ _)
    exact det_eq_one_of_perfect (A₀.map θ) hP.commutator_eq_top (θ a) ⟨a, ha, rfl⟩
  have hinv : ∀ a ∈ A₀, θ a ^ 2 = 1 → θ a ≠ 1 → θ a = -1 := fun a ha h2 h1 =>
    (eq_one_or_eq_neg_one_of_sq_eq_one hchar (θ a) (hdet a ha) h2).resolve_left h1
  -- `C₀ = ker θ ∩ A₀` is central in `A₀`
  set C₀ : Subgroup A₀ := θ.ker.subgroupOf A₀
  have hC₀ : C₀ ≤ Subgroup.center A₀ := by
    rcases LocalCores.quasisimple_normal_subgroups hq (inferInstance : C₀.Normal) with h | h
    · exfalso
      apply hnot
      intro a ha
      have : (⟨a, ha⟩ : A₀) ∈ C₀ := h ▸ Subgroup.mem_top _
      exact this
    · exact h
  have hmemC₀ : ∀ a : A₀, a ∈ C₀ ↔ θ a = 1 := fun a => by
    simp [C₀, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
  set Q := A₀ ⧸ Subgroup.center A₀
  have : IsSimpleGroup Q := hq.2.1
  have hQnab : ∃ a b : Q, a * b ≠ b * a := hq.2.2
  by_cases hCZ : C₀ = Subgroup.center A₀
  · -- the image of `A₀` is `A₀/Z(A₀)`, which has two distinct involutions; `SL(2, r)` has only one
    obtain ⟨E, -, hEs, hE4⟩ := exists_elem4 Q hQnab
    have hEnt : ∃ t ∈ E, t ≠ 1 := by
      by_contra h
      push Not at h
      have : E = ⊥ := eq_bot_iff.mpr fun x hx => (Subgroup.mem_bot).mpr (h x hx)
      rw [this, Subgroup.card_bot] at hE4
      omega
    obtain ⟨t, ht, ht1⟩ := hEnt
    have hEu : ∃ u ∈ E, u ≠ 1 ∧ t ≠ u := by
      by_contra h
      push Not at h
      have hsub : (E : Set Q) ⊆ {1, t} := fun u hu => by
        by_cases hu1 : u = 1
        · exact Or.inl hu1
        · exact Or.inr (h u hu hu1).symm
      have := Set.ncard_le_ncard hsub
      rw [← Nat.card_coe_set_eq] at this
      have h2 : ({1, t} : Set Q).ncard ≤ 2 := by
        have := Set.ncard_insert_le (1 : Q) {t}
        rwa [Set.ncard_singleton] at this
      change Nat.card E ≤ _ at this
      omega
    obtain ⟨u, hu, hu1, htu⟩ := hEu
    obtain ⟨t', rfl⟩ := QuotientGroup.mk_surjective t
    obtain ⟨u', rfl⟩ := QuotientGroup.mk_surjective u
    have hsq : ∀ x : A₀, ((x : Q) ^ 2 = 1) → θ (x : A) ^ 2 = 1 := fun x hx => by
      have hx' : x ^ 2 ∈ C₀ := by
        rw [hCZ, ← QuotientGroup.eq_one_iff]
        simpa using hx
      rw [← map_pow, ← Subgroup.coe_pow]
      exact (hmemC₀ _).mp hx'
    have hne : ∀ x : A₀, (x : Q) ≠ 1 → θ (x : A) ≠ 1 := fun x hx h => hx (by
      rw [QuotientGroup.eq_one_iff, ← hCZ]
      exact (hmemC₀ x).mpr h)
    have h1 := hinv _ t'.2 (hsq t' (hEs _ ht)) (hne t' ht1)
    have h2 := hinv _ u'.2 (hsq u' (hEs _ hu)) (hne u' hu1)
    apply htu
    rw [QuotientGroup.eq]
    have : t'⁻¹ * u' ∈ C₀ := (hmemC₀ _).mpr (by simp [map_mul, map_inv, h1, h2])
    rwa [hCZ] at this
  · -- `C₀ = 1`, `|Z(A₀)| = 2`, and Dickson's theorem gives `|A₀ / Z(A₀)| = 60`
    have hC₀bot : C₀ = ⊥ := by
      by_contra h
      apply hCZ
      have h2 : 2 ≤ Nat.card C₀ := by
        have := Subgroup.one_lt_card_iff_ne_bot C₀ |>.mpr h
        omega
      exact Subgroup.eq_of_le_of_card_ge hC₀ (by omega)
    have hZ2 : Nat.card (Subgroup.center A₀) = 2 := by
      have hZ1 : Subgroup.center A₀ ≠ ⊥ := fun h => hCZ (by rw [hC₀bot, h])
      have := (Subgroup.one_lt_card_iff_ne_bot _).mpr hZ1
      omega
    have hθinj : ∀ a b : A₀, θ (a : A) = θ (b : A) → a = b := fun a b h => by
      have : a⁻¹ * b ∈ C₀ := (hmemC₀ _).mpr (by simp [map_mul, map_inv, h])
      rw [hC₀bot, Subgroup.mem_bot, inv_mul_eq_one] at this
      exact this
    obtain ⟨f, hf⟩ := exists_hom_GL_to_PSL_sq r hr2
    have hGF : Nat.card (GaloisField r 2) = r ^ 2 := GaloisField.card r 2 (by norm_num)
    -- `f ∘ θ` restricted to `A₀` has kernel `Z(A₀)`
    set κ : A₀ →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField r 2) := f.comp (θ.comp A₀.subtype)
    have hscalar_central : ∀ (a : A) (c : (ZMod r)ˣ), θ a = Matrix.GeneralLinearGroup.scalar (Fin 2) c →
        ∀ b : A, θ (a * b * a⁻¹ * b⁻¹) = 1 := by
      intro a c hc b
      have hcomm : θ a * θ b = θ b * θ a := by
        rw [hc]
        ext i j
        simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.smul_eq_diagonal_mul,
          Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]
      simp only [map_mul, map_inv]
      rw [hcomm]
      group
    have hκker : κ.ker = Subgroup.center A₀ := by
      ext a
      rw [MonoidHom.mem_ker]
      constructor
      · intro h
        obtain ⟨c, hc⟩ := (hf _).mp h
        rw [Subgroup.mem_center_iff]
        intro b
        have := hscalar_central a c hc b
        have hb : (⁅a, b⁆ : A₀) ∈ C₀ := (hmemC₀ _).mpr (by simpa [commutatorElement_def] using this)
        rw [hC₀bot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hb
        exact hb.symm
      · intro ha
        have ha2 : a ^ 2 = 1 := by
          have := pow_card_eq_one' (G := Subgroup.center A₀) (x := ⟨a, ha⟩)
          rw [hZ2] at this
          exact congrArg Subtype.val this
        by_cases h1 : θ (a : A) = 1
        · simp [κ, h1]
        · have hm := hinv _ a.2 (by rw [← map_pow, ← Subgroup.coe_pow, ha2]; simp) h1
          refine (hf _).mpr ⟨-1, ?_⟩
          change θ (a : A) = _
          rw [hm]
          ext i j
          fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.coe_scalar]
    set X := κ.range
    have eX : Q ≃* X := (QuotientGroup.quotientMulEquivOfEq hκker.symm).trans (QuotientGroup.quotientKerEquivRange κ)
    have hXns : ¬ Group.IsSolvable X := fun h => by
      have := h
      have : Group.IsSolvable Q := Group.isSolvable_of_isSolvable_injective (f := eX.toMonoidHom) eX.injective
      obtain ⟨a, b, hab⟩ := hQnab
      exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr this a b)
    have hXcard : Nat.card X = Nat.card Q := (Nat.card_congr eX.toEquiv).symm
    have hA₀card : Nat.card A₀ = 2 * Nat.card Q := by
      rw [← hZ2, mul_comm, ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
    have hdvdA : ∀ (Y : Type) [Group Y] (g : A →* Y), Nat.card g.range ∣ Nat.card A := fun Y _ g =>
      Subgroup.card_range_dvd g
    have hXr : ¬ r ∣ Nat.card X := fun h => hrA (h.trans (by
      have : Nat.card X ∣ Nat.card A₀ := Subgroup.card_range_dvd κ
      exact this.trans (Subgroup.card_subgroup_dvd_card A₀)))
    have h60 := card_eq_sixty_of_not_isSolvable (p := r) hGF X hXns hXr
    rw [hXcard] at h60
    by_cases htop : A₀ = ⊤
    · exact hcyc (hexc htop hZ2 h60)
    · -- `|A : A₀| = 2`: `A` acts faithfully, and its image in `PSL(2, r²)` has order at least 120
      have hidx2 : A₀.index = 2 := by
        have h1 : A₀.index ≠ 1 := fun h => htop (Subgroup.index_eq_one.mp h)
        have h0 : A₀.index ≠ 0 := Subgroup.index_ne_zero_of_finite
        omega
      have hkerθ : θ.ker = ⊥ := by
        have hinf : θ.ker ⊓ A₀ = ⊥ := by
          rw [eq_bot_iff]
          intro a ⟨ha1, ha2⟩
          have : (⟨a, ha2⟩ : A₀) ∈ C₀ := ha1
          rw [hC₀bot, Subgroup.mem_bot] at this
          exact (Subgroup.mem_bot).mpr (congrArg Subtype.val this)
        have hc : θ.ker ≤ Subgroup.centralizer (A₀ : Set A) := by
          intro a ha
          rw [Subgroup.mem_centralizer_iff]
          intro b hb
          have hcm : a * b * a⁻¹ * b⁻¹ ∈ θ.ker ⊓ A₀ :=
            ⟨Subgroup.mul_mem _ (θ.normal_ker.conj_mem a ha b) (Subgroup.inv_mem _ ha) |> fun h => by
                simpa [mul_assoc] using θ.ker.mul_mem ha (θ.normal_ker.conj_mem a⁻¹ (θ.ker.inv_mem ha) b),
              by
                have := (inferInstance : A₀.Normal).conj_mem b hb a
                exact A₀.mul_mem this (A₀.inv_mem hb)⟩
          rw [hinf, Subgroup.mem_bot] at hcm
          have : a * b = b * a := by
            calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
              _ = b * a := by rw [hcm, one_mul]
          exact this.symm
        rw [eq_bot_iff, ← hinf]
        exact le_inf le_rfl (hc.trans hCA)
      set κ' : A →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField r 2) := f.comp θ
      have hκ'ker : Nat.card κ'.ker ≤ 2 := by
        have hle : κ'.ker.map (MonoidHom.id A) ≤ A₀ := by
          intro a ha
          obtain ⟨a, ha, rfl⟩ := ha
          obtain ⟨c, hc⟩ := (hf _).mp ha
          apply hCA
          rw [Subgroup.mem_centralizer_iff]
          intro b _
          have := hscalar_central a c hc b
          rw [← MonoidHom.mem_ker, hkerθ, Subgroup.mem_bot] at this
          calc b * a = (a * b * a⁻¹ * b⁻¹)⁻¹ * (a * b) := by group
            _ = a * b := by rw [this, inv_one, one_mul]
        have hle' : κ'.ker ≤ A₀ := by simpa using hle
        have hZle : (κ'.ker).subgroupOf A₀ ≤ Subgroup.center A₀ := by
          intro a ha
          obtain ⟨c, hc⟩ := (hf _).mp ha
          rw [Subgroup.mem_center_iff]
          intro b
          have := hscalar_central a c hc b
          rw [← MonoidHom.mem_ker, hkerθ, Subgroup.mem_bot] at this
          apply Subtype.ext
          simp only [Subgroup.coe_mul]
          calc (b : A) * a = ((a : A) * b * (a : A)⁻¹ * (b : A)⁻¹)⁻¹ * (a * b) := by group
            _ = a * b := by rw [this, inv_one, one_mul]
        calc Nat.card κ'.ker = Nat.card ((κ'.ker).subgroupOf A₀) :=
              (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle').toEquiv).symm
          _ ≤ Nat.card (Subgroup.center A₀) := Subgroup.card_le_of_le hZle
          _ = 2 := hZ2
      set Y := κ'.range
      have hYcard : Nat.card Y * Nat.card κ'.ker = Nat.card A := by
        rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange κ').toEquiv,
          ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
      have hAcard : Nat.card A = 2 * Nat.card A₀ := by
        rw [← hidx2, mul_comm, Subgroup.card_mul_index]
      have hXY : X ≤ Y := by
        rintro _ ⟨a, rfl⟩
        exact ⟨a, rfl⟩
      have hYns : ¬ Group.IsSolvable Y := fun h => by
        have := h
        exact hXns (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hXY))
      have hYr : ¬ r ∣ Nat.card Y := fun h => hrA (h.trans (Subgroup.card_range_dvd κ'))
      have h60' := card_eq_sixty_of_not_isSolvable (p := r) hGF Y hYns hYr
      have hpos : 0 < Nat.card κ'.ker := Nat.card_pos
      rw [h60', hAcard, hA₀card, h60] at hYcard
      nlinarith

end CFSGOutside.ChillagSonn
