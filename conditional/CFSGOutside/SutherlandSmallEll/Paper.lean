import CFSGOutside.Sutherland.Paper

/-!
# Sutherland, Proposition 5.8 for all primes `ℓ ≥ 5`

A. V. Sutherland, *Computing images of Galois representations attached to elliptic curves*, Forum Math. Sigma 4
(2016), e4, Proposition 5.8 (`prop:maximal`), is stated for `ℓ > 7`. This file proves the sufficiency direction for
every prime `ℓ ≥ 5`: a subgroup `G ≤ GL₂(𝔽_ℓ)` containing elements `g₁, g₂, g₃` of nonzero trace with `χ(g₁) = 1`,
`χ(g₂) = -1`, `u(g₃) ∉ {1, 2, 4}` and `u(g₃)² - 3u(g₃) + 1 ≠ 0` contains `SL₂(𝔽_ℓ)`. The converse fails at
`ℓ = 5` and `ℓ = 7`, because `SL₂(𝔽_ℓ)` has no element of nonzero trace with `u ∉ {1, 2, 4}`.

The statistics `χ`, `u`, `tr` and the group `SL₂` are those of `CFSGOutside.Sutherland`, and the lemmas that do not
use `ℓ > 7` are imported from `CFSGOutside.Sutherland.Paper`. The two lemmas that do are reproved here for `ℓ ≥ 5`.
Conditional on the corpus inputs stated as classes in `CFSGOutside.Corpus`.
-/

open Matrix
open scoped MatrixGroups

namespace CFSGOutside.SutherlandSmallEll

open CFSGOutside.Sutherland

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

theorem two_ne_zero_of_five_le (h5 : 5 ≤ ℓ) : (2 : ZMod ℓ) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod ℓ) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  exact absurd (Nat.le_of_dvd (by norm_num) this) (by omega)

/-- Abelian case of Proposition 5.8: no abelian-by-index-two subgroup of order prime to `ℓ` has elements with `χ = 1` and `χ = -1`. -/
theorem abelian_case_of_five_le (h7 : 5 ≤ ℓ) (G : Subgroup (GL (Fin 2) (ZMod ℓ)))
    (hcop : ¬ ℓ ∣ Nat.card G) (C : Subgroup (GL (Fin 2) (ZMod ℓ))) (hCG : C ≤ G)
    (hCab : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a) (hnorm : ∀ g ∈ G, ∀ c ∈ C, g * c * g⁻¹ ∈ C)
    (hsq : ∀ g ∈ G, g ^ 2 ∈ C) {g₁ g₂ : GL (Fin 2) (ZMod ℓ)} (hg₁ : g₁ ∈ G) (hg₂ : g₂ ∈ G)
    (ht₁ : tr g₁ ≠ 0) (ht₂ : tr g₂ ≠ 0) (hc₁ : chi g₁ = 1) (hc₂ : chi g₂ = -1) : False := by
  classical
  have h2 := two_ne_zero_of_five_le h7
  by_cases hs : ∀ c ∈ C, IsScalar (c : Matrix (Fin 2) (Fin 2) (ZMod ℓ))
  · -- all of `C` is scalar: an element of nonzero trace whose square is scalar is scalar
    have hsc := hs _ (hsq g₁ hg₁)
    rw [Units.val_pow_eq_pow_val, pow_two_eq] at hsc
    by_cases hM : IsScalar (g₁ : Matrix (Fin 2) (Fin 2) (ZMod ℓ))
    · rw [chi, disc_eq_zero_of_isScalar hM] at hc₁
      simp at hc₁
    · exact ht₁ (eq_zero_of_isScalar hM hsc)
  · push Not at hs
    obtain ⟨c, hcC, hcs⟩ := hs
    set Cm := (c : Matrix (Fin 2) (Fin 2) (ZMod ℓ))
    -- `c` has nonzero discriminant, since `ℓ ∤ |G|`
    have hd : disc Cm ≠ 0 := by
      intro hd
      set c' : G := ⟨c, hCG hcC⟩
      have hm : Cm ^ orderOf c' = 1 := by
        have h : c' ^ orderOf c' = 1 := pow_orderOf_eq_one c'
        have h' : c ^ orderOf c' = 1 := by
          have := congrArg Subtype.val h
          rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
        rw [← Units.val_pow_eq_pow_val, h', Units.val_one]
      have h0 := natCast_eq_zero_of_disc_eq_zero h2 hcs hd (coe_det_ne_zero c) hm
      rw [ZMod.natCast_eq_zero_iff] at h0
      exact hcop (h0.trans (orderOf_dvd_natCard c'))
    -- every element of nonzero trace and `χ ≠ 0` has `χ = χ(disc c)`
    have key : ∀ g ∈ G, tr g ≠ 0 → chi g ≠ 0 → chi g = quadraticChar (ZMod ℓ) (disc Cm) := by
      intro g hg htg hcg
      set Gm := (g : Matrix (Fin 2) (Fin 2) (ZMod ℓ))
      have hc' := hnorm g hg c hcC
      have hcomm := hCab _ hc' c hcC
      have hcommM : ((g * c * g⁻¹ : GL (Fin 2) (ZMod ℓ)) : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) *
          Cm = Cm * ((g * c * g⁻¹ : GL (Fin 2) (ZMod ℓ)) : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) := by
        rw [← Units.val_mul, hcomm, Units.val_mul]
      rcases eq_or_eq_of_commute h2 hcs hd hcommM (trace_conj g c) (det_conj g c) with h | h
      · -- `g` commutes with `c`
        have hgc : Gm * Cm = Cm * Gm := by
          have h' : g * c * g⁻¹ = c := Units.ext h
          have : g * c = c * g := by
            calc g * c = g * c * g⁻¹ * g := by group
              _ = c * g := by rw [h']
          have := congrArg Units.val this
          simpa [Gm, Cm] using this
        obtain ⟨a, b, hab⟩ := exists_eq_of_commute hcs hgc
        have hdg : disc Gm = b ^ 2 * disc Cm := by rw [hab, disc_smul_one_add]
        rw [chi] at hcg ⊢
        rw [hdg, map_mul] at hcg ⊢
        have hb : b ≠ 0 := by
          rintro rfl
          simp at hcg
        rw [quadraticChar_sq_one' hb, one_mul]
      · -- `g` conjugates `c` to `tr c - c`, so `tr g = 0`
        exfalso
        apply htg
        apply trace_eq_zero_of_anticommute h2 hd
        have h' : ((g * c * g⁻¹ : GL (Fin 2) (ZMod ℓ)) : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) * Gm =
            Gm * Cm := by
          rw [← Units.val_mul, ← Units.val_mul]
          congr 1
          group
        rw [h, sub_mul, smul_mul_assoc, one_mul] at h'
        rw [← h']
        abel
    have e₁ := key g₁ hg₁ ht₁ (by rw [hc₁]; decide)
    have e₂ := key g₂ hg₂ ht₂ (by rw [hc₂]; decide)
    rw [hc₁] at e₁
    rw [hc₂, ← e₁] at e₂
    exact absurd e₂ (by decide)

/-- If a power `g ^ k`, `1 ≤ k ≤ 5`, is scalar, then `g` violates condition (3). -/
theorem exceptional_case_of_five_le (h7 : 5 ≤ ℓ) {g : GL (Fin 2) (ZMod ℓ)} {k : ℕ} (hk1 : 1 ≤ k)
    (hk5 : k ≤ 5) (hgk : Matrix.ProjGenLinGroup.mk g ^ k = 1) (ht : tr g ≠ 0)
    (hu : uInv g ∉ ({1, 2, 4} : Set (ZMod ℓ))) (hu2 : uInv g ^ 2 - 3 * uInv g + 1 ≠ 0) :
    False := by
  have hc : g ^ k ∈ Subgroup.center (GL (Fin 2) (ZMod ℓ)) := by
    rw [← map_pow] at hgk
    exact (QuotientGroup.eq_one_iff _).mp hgk
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hc
  obtain ⟨a, ha⟩ := hc
  have hs : IsScalar ((g : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) ^ k) := by
    rw [← Units.val_pow_eq_pow_val, ← ha]
    refine ⟨?_, ?_, ?_⟩ <;> simp [Matrix.GeneralLinearGroup.scalar]
  rcases u_cases (two_ne_zero_of_five_le h7) (coe_det_ne_zero g) hk1 hk5 hs with h | h | h | h | h
  · apply ht
    have := div_eq_zero_iff.mp h
    rcases this with h' | h'
    · exact pow_eq_zero_iff (by norm_num) |>.mp h'
    · exact absurd h' (coe_det_ne_zero g)
  · exact hu (by simp [uInv, h])
  · exact hu (by simp [uInv, h])
  · exact hu (by simp [uInv, h])
  · exact hu2 h

/-- **Sutherland's sufficient criterion for `ℓ ≥ 5`.** Let `ℓ ≥ 5` be prime and `G ≤ GL₂(𝔽_ℓ)`. If `G` contains
elements `g₁, g₂, g₃` of nonzero trace with `χ(g₁) = 1`, `χ(g₂) = -1`, `u(g₃) ∉ {1, 2, 4}` and
`u(g₃)² - 3u(g₃) + 1 ≠ 0`, then `G` contains `SL₂(𝔽_ℓ)`. -/
theorem sl2_le_of_elements [CFSGOutside.Corpus.DicksonGlTwo]
    [CFSGOutside.Corpus.Uc22s2112r34PglTameCasesIso.{0}] (h7 : 5 ≤ ℓ) (G : Subgroup (GL (Fin 2) (ZMod ℓ)))
    (h : ∃ g₁ ∈ G, ∃ g₂ ∈ G, ∃ g₃ ∈ G, tr g₁ ≠ 0 ∧ tr g₂ ≠ 0 ∧ tr g₃ ≠ 0 ∧
      chi g₁ = 1 ∧ chi g₂ = -1 ∧ uInv g₃ ∉ ({1, 2, 4} : Set (ZMod ℓ)) ∧
      uInv g₃ ^ 2 - 3 * uInv g₃ + 1 ≠ 0) : SL2 ℓ ≤ G := by
  classical
  revert h
  rintro ⟨g₁, hg₁, g₂, hg₂, g₃, hg₃, ht₁, ht₂, ht₃, hc₁, hc₂, hu₃, hu₃'⟩
  by_cases hdvd : ℓ ∣ Nat.card G
  · rcases CFSGOutside.Corpus.DicksonGlTwo.dickson_gl_two G hdvd with ⟨P, hPn, hP⟩ | h
    · exact absurd hc₂ (chi_ne_neg_one_of_normal_sylow G P hPn hP hg₂)
    · exact SL2_le_iff G h
  · exfalso
    have : Finite (Matrix.ProjGenLinGroup (Fin 2) (ZMod ℓ)) :=
      Finite.of_surjective _ Matrix.ProjGenLinGroup.mk_surjective
    set J := G.map Matrix.ProjGenLinGroup.mk
    set π := Matrix.ProjGenLinGroup.mk.subgroupMap G
    have hπ : Function.Surjective π := Matrix.ProjGenLinGroup.mk.subgroupMap_surjective G
    have hJ : ¬ ℓ ∣ Nat.card J := fun h => hdvd (h.trans (Subgroup.card_map_dvd _ _))
    set j₃ : J := ⟨_, Subgroup.mem_map_of_mem _ hg₃⟩
    have hj₃ : ∀ k : ℕ, j₃ ^ k = 1 → Matrix.ProjGenLinGroup.mk g₃ ^ k = 1 := fun k h => by
      have := congrArg Subtype.val h
      simpa [j₃] using this
    rcases CFSGOutside.Corpus.Uc22s2112r34PglTameCasesIso.uc22s2112r34_pgl_tame_cases_iso (p := ℓ) J hJ with
      hcyc | ⟨z, ⟨e⟩⟩ | he | he | he
    · -- cyclic image: `G` is abelian
      have := MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center π (ker_le_center' G)
      obtain ⟨C, hCG, hab, hn, hsq⟩ := exists_C G ⊤
        (fun a _ b _ => this.is_comm.comm a b) (by simp)
      exact abelian_case_of_five_le h7 G hdvd C hCG hab hn hsq hg₁ hg₂ ht₁ ht₂ hc₁ hc₂
    · -- dihedral image: the preimage of the rotations is abelian of index two
      set C₀ := ((Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup z)).comap
        e.toMonoidHom).comap π
      have hab : ∀ a ∈ C₀, ∀ b ∈ C₀, a * b = b * a := by
        intro a ha b hb
        let ψ : C₀ →* Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup z) :=
          ((e.toMonoidHom.comp π).comp C₀.subtype).codRestrict _ fun c => c.2
        have hψ : ψ.ker ≤ Subgroup.center C₀ := by
          intro c hc
          have h1 : e (π c) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hc)
          have h2 : π c = 1 := by simpa using h1
          have h3 : (c : G) ∈ Subgroup.center G := ker_le_center' G (MonoidHom.mem_ker.2 h2)
          exact Subgroup.mem_center_iff.2 fun y =>
            Subtype.ext (Subgroup.mem_center_iff.1 h3 (y : G))
        have := MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center ψ hψ
        exact congrArg Subtype.val (this.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
      have hidx : C₀.index ∣ 2 := by
        rw [Subgroup.index_comap_of_surjective _ hπ,
          Subgroup.index_comap_of_surjective _ e.surjective]
        have hz : z ≠ 0 := by
          rintro rfl
          have h1 := Nat.card_congr e.toEquiv
          rw [DihedralGroup.nat_card, mul_zero] at h1
          exact Nat.card_pos.ne' h1
        have : NeZero z := ⟨hz⟩
        have h := (Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup z)).card_mul_index
        rw [Nat.card_zpowers, DihedralGroup.orderOf_r_one, DihedralGroup.nat_card] at h
        rw [show (Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup z)).index = 2 by
          have := Nat.pos_of_ne_zero hz
          nlinarith]
      obtain ⟨C, hCG, hab', hn, hsq⟩ := exists_C G C₀ hab hidx
      exact abelian_case_of_five_le h7 G hdvd C hCG hab' hn hsq hg₁ hg₂ ht₁ ht₂ hc₁ hc₂
    · -- `A₄`
      obtain ⟨e⟩ := he
      have hσ := perm4_pow ((e j₃ : alternatingGroup (Fin 4)) : Equiv.Perm (Fin 4))
      have hk : ∀ k : ℕ, ((e j₃ : alternatingGroup (Fin 4)) : Equiv.Perm (Fin 4)) ^ k = 1 →
          j₃ ^ k = 1 := fun k h => by
        apply e.injective
        rw [map_pow, map_one]
        exact Subtype.ext (by simpa using h)
      rcases hσ with h | h | h
      · exact exceptional_case_of_five_le h7 (by norm_num) (by norm_num) (hj₃ 2 (hk 2 h)) ht₃ hu₃ hu₃'
      · exact exceptional_case_of_five_le h7 (by norm_num) (by norm_num) (hj₃ 3 (hk 3 h)) ht₃ hu₃ hu₃'
      · exact exceptional_case_of_five_le h7 (by norm_num) (by norm_num) (hj₃ 4 (hk 4 h)) ht₃ hu₃ hu₃'
    · -- `S₄`
      obtain ⟨e⟩ := he
      have hk : ∀ k : ℕ, (e j₃) ^ k = 1 → j₃ ^ k = 1 := fun k h => by
        apply e.injective
        rw [map_pow, map_one, h]
      rcases perm4_pow (e j₃) with h | h | h
      · exact exceptional_case_of_five_le h7 (by norm_num) (by norm_num) (hj₃ 2 (hk 2 h)) ht₃ hu₃ hu₃'
      · exact exceptional_case_of_five_le h7 (by norm_num) (by norm_num) (hj₃ 3 (hk 3 h)) ht₃ hu₃ hu₃'
      · exact exceptional_case_of_five_le h7 (by norm_num) (by norm_num) (hj₃ 4 (hk 4 h)) ht₃ hu₃ hu₃'
    · -- `A₅`
      obtain ⟨e⟩ := he
      have hsign : Equiv.Perm.sign ((e j₃ : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) = 1 :=
        Equiv.Perm.mem_alternatingGroup.mp (e j₃).2
      have hk : ∀ k : ℕ, ((e j₃ : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) ^ k = 1 →
          j₃ ^ k = 1 := fun k h => by
        apply e.injective
        rw [map_pow, map_one]
        exact Subtype.ext (by simpa using h)
      rcases perm5_pow _ hsign with h | h | h
      · exact exceptional_case_of_five_le h7 (by norm_num) (by norm_num) (hj₃ 2 (hk 2 h)) ht₃ hu₃ hu₃'
      · exact exceptional_case_of_five_le h7 (by norm_num) (by norm_num) (hj₃ 3 (hk 3 h)) ht₃ hu₃ hu₃'
      · exact exceptional_case_of_five_le h7 (by norm_num) (by norm_num) (hj₃ 5 (hk 5 h)) ht₃ hu₃ hu₃'

theorem sq_cases5 : ∀ t : ZMod 5, t ≠ 0 → t ^ 2 = 1 ∨ t ^ 2 = 2 ∨ t ^ 2 = 4 := by decide

theorem sq_cases7 : ∀ t : ZMod 7, t ≠ 0 → t ^ 2 = 1 ∨ t ^ 2 = 2 ∨ t ^ 2 = 4 := by decide

/-- Sharpness: for `ℓ = 5, 7` the converse fails, since `SL₂(𝔽_ℓ)` has no element of nonzero trace with
`u ∉ {1, 2, 4}`. -/
theorem no_third_element_in_sl2 (hℓ : ℓ = 5 ∨ ℓ = 7) (g : GL (Fin 2) (ZMod ℓ)) (hg : g ∈ SL2 ℓ)
    (ht : tr g ≠ 0) : uInv g ∈ ({1, 2, 4} : Set (ZMod ℓ)) := by
  obtain ⟨A, rfl⟩ := hg
  have hdet : ((Matrix.SpecialLinearGroup.toGL A : GL (Fin 2) (ZMod ℓ)) : Matrix (Fin 2) (Fin 2) (ZMod ℓ)).det = 1 := by
    simp
  unfold uInv
  rw [hdet, div_one]
  unfold tr at ht
  generalize ((Matrix.SpecialLinearGroup.toGL A : GL (Fin 2) (ZMod ℓ)) : Matrix (Fin 2) (Fin 2) (ZMod ℓ)).trace = t at ht ⊢
  have key : ∀ t : ZMod ℓ, t ≠ 0 → t ^ 2 = 1 ∨ t ^ 2 = 2 ∨ t ^ 2 = 4 := by
    rcases hℓ with rfl | rfl
    · exact sq_cases5
    · exact sq_cases7
  simpa using key t ht

end CFSGOutside.SutherlandSmallEll
