import Mathlib

/-!
# A finite simple group of order sixty is the alternating group on five letters

Used for Serre (2013), Théorème 5 (§6.4), where `A₅` is the group `PSL₂(𝔽₅)` of order sixty, which has the
shape `q ^ N * C / D` of the order of a group of Lie type in characteristic five.

The proof counts Sylow `2`-subgroups. Their number is the index `m` of the normaliser of a Sylow
`2`-subgroup `P`, a divisor of `15`. For `m = 1` the group has a normal subgroup of order four. For `m = 3` it
embeds in `S₃`. For `m = 15` the normaliser of `P` is `P`, which is abelian, so Burnside's transfer theorem gives
a normal subgroup of order fifteen. So `m = 5`, and the action on the five Sylow `2`-subgroups embeds the group
in `S₅`, in fact in `A₅`, since the sign of the image is trivial.
-/

namespace CFSGOutside.Serre

variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

/-- The action of a finite simple group on the cosets of a proper subgroup is faithful. -/
theorem toPermHom_injective {H : Subgroup G} (hH : H ≠ ⊤) :
    Function.Injective (MulAction.toPermHom G (G ⧸ H)) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases (MonoidHom.normal_ker (MulAction.toPermHom G (G ⧸ H))).eq_bot_or_eq_top with h | h
  · exact h
  · refine absurd ?_ hH
    rw [eq_top_iff]
    intro g _
    have hg : g ∈ (MulAction.toPermHom G (G ⧸ H)).ker := h ▸ Subgroup.mem_top g
    have h1 := congrArg (fun σ : Equiv.Perm (G ⧸ H) => σ ((1 : G) : G ⧸ H))
      (MonoidHom.mem_ker.1 hg)
    simpa [QuotientGroup.eq] using h1

/-- A finite simple group `G` with a proper subgroup `H` of index `n` embeds in `S_n`, so `|G| ≤ n!`. -/
theorem card_le_factorial_index {H : Subgroup G} (hH : H ≠ ⊤) :
    Nat.card G ≤ H.index.factorial := by
  have h := Nat.card_le_card_of_injective _ (toPermHom_injective hH)
  rwa [Nat.card_perm, ← Subgroup.index_eq_card] at h

/-- Every finite simple group of order sixty is isomorphic to the alternating group on five letters. -/
theorem nonempty_mulEquiv_alternatingGroup_five_of_card_sixty (hG : Nat.card G = 60) :
    Nonempty (G ≃* alternatingGroup (Fin 5)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 G) := inferInstance
  have hP : Nat.card (P : Subgroup G) = 4 := by
    have h2 : padicValNat 2 60 = 2 := by
      rw [show (60 : ℕ) = 2 ^ 2 * 15 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
        padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]
    rw [Sylow.card_eq_multiplicity, hG, Nat.factorization_def _ Nat.prime_two, h2]
    norm_num
  have hPindex : (P : Subgroup G).index = 15 := by
    have := (P : Subgroup G).card_mul_index
    rw [hP, hG] at this
    omega
  obtain ⟨N, hNdef⟩ : ∃ N : Subgroup G, N = Subgroup.normalizer (P : Set G) := ⟨_, rfl⟩
  have hle : (P : Subgroup G) ≤ N := hNdef ▸ Subgroup.le_normalizer
  have hdvd : N.index ∣ 15 := hPindex ▸ Subgroup.index_dvd_of_le hle
  have hNcard : Nat.card N * N.index = 60 := by
    rw [← hG]; exact Subgroup.card_mul_index _
  have hm : N.index = 1 ∨ N.index = 3 ∨
      N.index = 5 ∨ N.index = 15 := by
    have : N.index ∈ Nat.divisors 15 := by simpa using hdvd
    have h15 : Nat.divisors 15 = {1, 3, 5, 15} := by decide
    rw [h15] at this
    simpa using this
  rcases hm with hm | hm | hm | hm
  · -- the normaliser is the whole group, so `P` is a normal subgroup of order four
    have hnormal : (P : Subgroup G).Normal := by
      have h := Subgroup.index_eq_one.1 hm
      rw [hNdef] at h
      exact Subgroup.normalizer_eq_top_iff.1 h
    rcases hnormal.eq_bot_or_eq_top with h | h
    · rw [h, Subgroup.card_bot] at hP; omega
    · rw [h, Subgroup.card_top, hG] at hP; omega
  · -- an action on three points
    have hne : N ≠ ⊤ := fun h => by
      rw [h, Subgroup.index_top] at hm; omega
    have := card_le_factorial_index hne
    rw [hm, hG] at this
    norm_num [Nat.factorial] at this
  · -- the action on the five Sylow `2`-subgroups
    have hne : N ≠ ⊤ := fun h => by
      rw [h, Subgroup.index_top] at hm; omega
    have hcard : Nat.card (G ⧸ N) = 5 := by
      rw [← Subgroup.index_eq_card, hm]
    let e : G ⧸ N ≃ Fin 5 := Finite.equivFinOfCardEq hcard
    let ψ : G →* Equiv.Perm (Fin 5) :=
      (Equiv.permCongrHom e).toMonoidHom.comp (MulAction.toPermHom G _)
    have hψ : Function.Injective ψ :=
      (Equiv.permCongrHom e).injective.comp (toPermHom_injective hne)
    have hsign : (Equiv.Perm.sign.comp ψ).ker = ⊤ := by
      rcases (MonoidHom.normal_ker (Equiv.Perm.sign.comp ψ)).eq_bot_or_eq_top with h | h
      · exfalso
        have hinj : Function.Injective (Equiv.Perm.sign.comp ψ) :=
          (MonoidHom.ker_eq_bot_iff _).1 h
        have := Nat.card_le_card_of_injective _ hinj
        rw [hG] at this
        have h2 : Nat.card ℤˣ = 2 := by
          rw [Nat.card_eq_fintype_card]; exact Fintype.card_units_int
        omega
      · exact h
    have hrange : ψ.range ≤ alternatingGroup (Fin 5) := by
      rintro _ ⟨g, rfl⟩
      have : g ∈ (Equiv.Perm.sign.comp ψ).ker := hsign ▸ Subgroup.mem_top g
      exact (MonoidHom.mem_ker.1 this : Equiv.Perm.sign (ψ g) = 1)
    have hAcard : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup]
      decide
    have hrangecard : Nat.card ψ.range = 60 := by
      rw [← hG]; exact (Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv).symm
    have heq : ψ.range = alternatingGroup (Fin 5) :=
      Subgroup.eq_of_le_of_card_ge hrange (by rw [hAcard, hrangecard])
    exact ⟨(MonoidHom.ofInjective hψ).trans (MulEquiv.subgroupCongr heq)⟩
  · -- the normaliser of `P` is `P`; Burnside's transfer theorem gives a normal complement
    have hNP : N.index = 15 := hm
    have hNeq : (P : Subgroup G) = N :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hP]; rw [hNP] at hNcard; omega)
    have hab : ∀ a b : (P : Subgroup G), a * b = b * a :=
      IsPGroup.commutative_of_card_eq_prime_sq (p := 2) (by rw [hP]; norm_num)
    have hcent : Subgroup.normalizer (P : Set G) ≤ Subgroup.centralizer (P : Set G) := by
      intro x hx
      rw [← hNdef, ← hNeq] at hx
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact congrArg Subtype.val (hab ⟨h, hh⟩ ⟨x, hx⟩)
    have hcompl := MonoidHom.ker_transferSylow_isComplement' P hcent
    have hK := hcompl.card_mul
    rw [hP, hG] at hK
    haveI := (MonoidHom.transferSylow P hcent).normal_ker
    rcases (MonoidHom.normal_ker (MonoidHom.transferSylow P hcent)).eq_bot_or_eq_top with h | h
    · rw [h, Subgroup.card_bot] at hK; omega
    · rw [h, Subgroup.card_top, hG] at hK; omega

end CFSGOutside.Serre
