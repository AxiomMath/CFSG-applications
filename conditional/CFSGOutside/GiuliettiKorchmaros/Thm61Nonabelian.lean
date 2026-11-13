import CFSGOutside.Corpus.RankTwoSylowShapes
import CFSGOutside.Corpus.UnitaryFourSylowStructure
import CFSGOutside.Corpus.GorensteinWalterSimple
import CFSGOutside.Corpus.LrSemidihedralSimpleRecognition
import CFSGOutside.Corpus.SemilinearEquivAut
import CFSGOutside.Corpus.AutAlternatingBijectiveConj
import CFSGOutside.Corpus.M11AutInner
import CFSGOutside.GiuliettiKorchmaros.Thm61Basic
import CFSGOutside.GiuliettiKorchmaros.Thm61Defs
import CFSGOutside.GiuliettiKorchmaros.Wreathed

/-!
# Theorem 6.1, case of a nonabelian minimal normal subgroup (Lemmas 6.9 and 6.13)
-/

namespace CFSGOutside.GiuliettiKorchmaros

open CFSGOutside.Corpus
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

section Shapes

variable [MinimalNormalSimpleFactors.{0}] [TwoLePRankOfIsSimpleGroup.{0}] [RankTwoSylowShapes]
  [UnitaryFourSylowStructure]

/-- Under `CyclicIndexTwo`, a Sylow 2-subgroup of a nonabelian simple normal subgroup of 2-rank 2 is dihedral or
semidihedral. -/
theorem sylow_dihedral_or_semidihedral (hP : CyclicIndexTwo G) (N : Subgroup G) [IsSimpleGroup N]
    (hnab : ∃ a b : N, a * b ≠ b * a) (hr : Open.twoRank N = 2) (S₀ : Sylow 2 N) :
    (∃ n : ℕ, 2 ≤ n ∧ Nonempty ((S₀ : Subgroup N) ≃* DihedralGroup (2 ^ (n - 1)))) ∨
    (∃ n : ℕ, 4 ≤ n ∧ Nonempty ((S₀ : Subgroup N) ≃* Open.SemidihedralGroup n)) := by
  rcases RankTwoSylowShapes.rank_two_sylow_shapes hnab hr S₀ with h | h | ⟨n, hn, ⟨e⟩⟩ |
      ⟨H, _, U, hH, hSU⟩
  · exact Or.inl h
  · exact Or.inr h
  · exfalso
    obtain ⟨g, hgS, hcard⟩ := exists_large_order hP N S₀ S₀.isPGroup'
    have hS : Nat.card (S₀ : Subgroup N) = 2 ^ (2 * n + 1) := by
      rw [Nat.card_congr e.toEquiv, card_wreathed]
    have hord : orderOf g ∣ 2 ^ (n + 1) := by
      have h1 : orderOf (e ⟨g, hgS⟩) ∣ 2 ^ (n + 1) :=
        orderOf_dvd_of_pow_eq_one (wreathed_pow_eq_one n _)
      rwa [MulEquiv.orderOf_eq, Subgroup.orderOf_mk] at h1
    have hle := Nat.le_of_dvd (by positivity) hord
    rw [hS] at hcard
    have : 2 ^ (2 * n + 1) ≤ 2 ^ (n + 2) := by
      calc 2 ^ (2 * n + 1) ≤ 2 * orderOf g := hcard
        _ ≤ 2 * 2 ^ (n + 1) := Nat.mul_le_mul_left _ hle
        _ = 2 ^ (n + 2) := by ring
    have := (Nat.pow_le_pow_iff_right (by norm_num)).mp this
    omega
  · exfalso
    obtain ⟨h64, -, hsq1, hsqZ, -⟩ := UnitaryFourSylowStructure.unitary_four_sylow_structure hH S₀ U hSU
    obtain ⟨g, hgS, hcard⟩ := exists_large_order hP N S₀ S₀.isPGroup'
    have h4 : (⟨g, hgS⟩ : (S₀ : Subgroup N)) ^ 4 = 1 := by
      have := (hsq1 (⟨g, hgS⟩ ^ 2)).mpr (hsqZ _)
      rw [← pow_mul] at this
      exact this
    have hord : orderOf g ∣ 4 := by
      have := orderOf_dvd_of_pow_eq_one h4
      rwa [Subgroup.orderOf_mk] at this
    have hle := Nat.le_of_dvd (by norm_num) hord
    rw [h64] at hcard
    omega

variable [GorensteinWalterSimple] [LrSemidihedralSimpleRecognition]

/-- The isomorphism types of a nonabelian minimal normal subgroup (Lemma 6.9, with the `PSL(2,q)` case in
`GaloisField` form). -/
theorem nonabelian_minimalNormal_cases (hP : CyclicIndexTwo G) {N : Subgroup G} (hN : IsMinimalNormal N)
    (hnab : ∃ a b : N, a * b ≠ b * a) :
    IsSimpleGroup N ∧
      (Nonempty (N ≃* alternatingGroup (Fin 7)) ∨
        (∃ p k : ℕ, ∃ _hp : Fact p.Prime, Odd p ∧ 5 ≤ p ^ k ∧
          Nonempty (N ≃* PSL(2, GaloisField p k))) ∨
        (∃ p k : ℕ, ∃ _hp : Fact p.Prime, 0 < k ∧ p ^ k % 4 = 3 ∧
          Nonempty (N ≃* PSL(3, GaloisField p k))) ∨
        (∃ p k : ℕ, ∃ _hp : Fact p.Prime, 0 < k ∧ p ^ k % 4 = 1 ∧
          Nonempty (N ≃* Open.PSU3 p k)) ∨
        Nonempty (N ≃* Open.M11)) := by
  obtain ⟨hNn, hN1, hmin⟩ := hN
  obtain ⟨hs, hr⟩ := simple_and_twoRank hP hNn hN1 hmin hnab
  refine ⟨hs, ?_⟩
  obtain ⟨S₀⟩ : Nonempty (Sylow 2 N) := inferInstance
  rcases sylow_dihedral_or_semidihedral hP N hnab hr S₀ with ⟨n, -, hS⟩ | ⟨n, hn, hS⟩
  · rcases GorensteinWalterSimple.gorenstein_walter N hnab S₀ ⟨_, hS⟩ with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases LrSemidihedralSimpleRecognition.lr_semidihedral_simple_recognition_2 N hnab S₀ ⟨n, hn, hS⟩ with
      h | h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

/-- Lemma 6.13: a nonabelian minimal normal subgroup has trivial centralizer. -/
theorem centralizer_minimalNormal_eq_bot (hP : CyclicIndexTwo G) (hO : OddCoreFree G) {N : Subgroup G}
    (hN : IsMinimalNormal N) (hnab : ∃ a b : N, a * b ≠ b * a) :
    Subgroup.centralizer (N : Set G) = ⊥ := by
  obtain ⟨hNn, hN1, hmin⟩ := hN
  obtain ⟨hs, -⟩ := simple_and_twoRank hP hNn hN1 hmin hnab
  haveI := hNn
  set C := Subgroup.centralizer (N : Set G)
  rcases Nat.even_or_odd (Nat.card C) with heven | hodd
  · exfalso
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 (even_iff_two_dvd.mp heven)
    -- `u` is an involution centralizing `N`
    obtain ⟨E, hEc, hEs, hE4⟩ := exists_elem4 N hnab
    set F0 := E.map N.subtype
    set F1 := Subgroup.zpowers (u : G)
    have hu2 : (u : G) ^ 2 = 1 := by
      have := pow_orderOf_eq_one u
      rw [hu] at this
      exact_mod_cast congrArg Subtype.val this
    have hb := sup_elem_bound hP F0 F1
      (by rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
          simpa using congrArg N.subtype (hEc a ha b hb))
      (by intro a ha b hb
          obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
          obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
          rw [← zpow_add, ← zpow_add, add_comm])
      (by rintro _ ⟨a, ha, rfl⟩
          rw [← map_pow, hEs a ha, map_one])
      (by intro x hx
          obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
          rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu2, one_zpow])
      (by rintro _ ⟨a, -, rfl⟩ b hb
          obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
          exact (Subgroup.mem_centralizer_iff.mp (Subgroup.zpow_mem _ u.2 i) _ a.2))
    have hcard0 : Nat.card F0 = 4 := by
      rw [Subgroup.card_map_of_injective N.subtype_injective, hE4]
    have heq := Subgroup.eq_of_le_of_card_ge (le_sup_left : F0 ≤ F0 ⊔ F1) (by omega)
    have huF0 : (u : G) ∈ F0 := by rw [heq]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    obtain ⟨n, -, hn⟩ := Subgroup.mem_map.mp huF0
    -- `u = n ∈ N` is central in `N`, but `N` has trivial center
    have hcen : n ∈ Subgroup.center N := by
      rw [Subgroup.mem_center_iff]
      intro m
      apply Subtype.ext
      have := Subgroup.mem_centralizer_iff.mp u.2 m m.2
      simp only [Subgroup.coe_subtype] at hn
      simp only [Subgroup.coe_mul, hn]
      exact this
    have hcbot : Subgroup.center N = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center N) with h | h
      · exact h
      · exfalso
        obtain ⟨a, b, hab⟩ := hnab
        exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
    rw [hcbot, Subgroup.mem_bot] at hcen
    have hu1 : (u : G) = 1 := by rw [← hn, hcen]; rfl
    have : u = 1 := Subtype.ext hu1
    rw [this, orderOf_one] at hu
    exact absurd hu (by norm_num)
  · exact hO C inferInstance hodd

/-- Conjugation of `G` on a normal subgroup with trivial centralizer is injective. -/
theorem conjNormal_injective {N : Subgroup G} [N.Normal] (hC : Subgroup.centralizer (N : Set G) = ⊥) :
    Function.Injective (MulAut.conjNormal : G →* MulAut N) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hC]
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  rw [Subgroup.mem_centralizer_iff]
  intro n hn
  have := congrArg (fun φ : MulAut N => ((φ ⟨n, hn⟩ : N) : G)) hg
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
  calc n * g = (g * n * g⁻¹) * g := by rw [this]
    _ = g * n := by group

/-- Case (iv) from a normal `PSL(2,K)` with trivial centralizer. -/
theorem embedding_PGammaL2 [SemilinearEquivAut.{0}] {K : Type} [Field K] [Finite K] {N : Subgroup G}
    [N.Normal] (e : N ≃* PSL(2, K)) (hC : Subgroup.centralizer (N : Set G) = ⊥) :
    ∃ φ : G →* GorensteinWalter.PGammaL2 K, Function.Injective φ ∧
      ((Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range).map
        SemidirectProduct.inl ≤ φ.range := by
  obtain ⟨e', he'⟩ := SemilinearEquivAut.semilinearEquivAut K
  refine ⟨e'.symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp MulAut.conjNormal),
    e'.symm.injective.comp ((MulAut.congr e).injective.comp (conjNormal_injective hC)), ?_⟩
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  refine ⟨((e.symm x : N) : G), ?_⟩
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply]
  rw [← he' x]
  congr 1
  apply MulEquiv.ext
  intro y
  obtain ⟨n, rfl⟩ := e.surjective y
  have hc : (MulAut.conjNormal ((e.symm x : N) : G)) n = e.symm x * n * (e.symm x)⁻¹ :=
    Subtype.ext (by simp [MulAut.conjNormal_apply])
  change e ((MulAut.conjNormal ((e.symm x : N) : G)) (e.symm (e n))) = x * e n * x⁻¹
  rw [MulEquiv.symm_apply_apply, hc, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

/-- An element of `S₇` whose order divides 16 has order dividing 4 (no cycles of length 8). -/
theorem perm_seven_orderOf_dvd_four (σ : Equiv.Perm (Fin 7)) (h : orderOf σ ∣ 16) : orderOf σ ∣ 4 := by
  rw [← Equiv.Perm.lcm_cycleType]
  apply Multiset.lcm_dvd.mpr
  intro n hn
  have h1 : n ∣ 16 := (Equiv.Perm.dvd_of_mem_cycleType hn).trans h
  have h2 : 2 ≤ n := Equiv.Perm.two_le_of_mem_cycleType hn
  have h3 : n ≤ 7 := by
    have := Equiv.Perm.le_card_support_of_mem_cycleType hn
    have h4 : σ.support.card ≤ 7 := by
      calc σ.support.card ≤ Finset.univ.card := Finset.card_le_univ _
        _ = 7 := by simp
    omega
  interval_cases n <;> revert h1 <;> decide

/-- `S₇` violates `CyclicIndexTwo`: its Sylow 2-subgroups (order 16) have no cyclic subgroup of index 2. -/
theorem not_cyclicIndexTwo_perm_seven : ¬ CyclicIndexTwo (Equiv.Perm (Fin 7)) := by
  intro hP
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd : 2 ^ 4 ∣ Nat.card (Equiv.Perm (Fin 7)) := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]; decide
  obtain ⟨P, hPc⟩ := Sylow.exists_subgroup_card_pow_prime 2 hd
  obtain ⟨C, hCP, hC, hidx⟩ := hP P (IsPGroup.of_card hPc)
  obtain ⟨g, hg⟩ := hC.exists_generator
  have hord : Nat.card C = orderOf g := (orderOf_eq_card_of_forall_mem_zpowers hg).symm
  have h1 := Subgroup.relIndex_mul_card C P
  rw [inf_of_le_left hCP, hPc] at h1
  have hdvd : orderOf (g : Equiv.Perm (Fin 7)) ∣ 16 := by
    rw [Subgroup.orderOf_coe, ← hord]
    exact ⟨C.relIndex P, by rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← h1]; ring⟩
  have h4 := Nat.le_of_dvd (by norm_num) (perm_seven_orderOf_dvd_four _ hdvd)
  rw [Subgroup.orderOf_coe, ← hord] at h4
  have : C.relIndex P * Nat.card C ≤ 2 * 4 := Nat.mul_le_mul hidx h4
  omega

/-- Lemma 6.13, `A₇` case: `G = N`. -/
theorem eq_top_of_alternatingSeven [AutAlternatingBijectiveConj] (hP : CyclicIndexTwo G)
    {N : Subgroup G} [N.Normal] (e : N ≃* alternatingGroup (Fin 7))
    (hC : Subgroup.centralizer (N : Set G) = ⊥) : N = ⊤ := by
  classical
  let Φ : Equiv.Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) := MulEquiv.ofBijective
    (MulAut.conjNormal (H := alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7) →* MulAut _)
    (AutAlternatingBijectiveConj.aut_alternatingGroup_bijective_conj 7 (by norm_num) (by norm_num))
  let ψ : G →* Equiv.Perm (Fin 7) :=
    Φ.symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp MulAut.conjNormal)
  have hψ : Function.Injective ψ :=
    Φ.symm.injective.comp ((MulAut.congr e).injective.comp (conjNormal_injective hC))
  have hψN : ∀ n : N, ψ n = (e n : Equiv.Perm (Fin 7)) := by
    intro n
    have : Φ (e n) = MulAut.congr e (MulAut.conjNormal (n : G)) := by
      apply MulEquiv.ext
      intro y
      obtain ⟨m, rfl⟩ := e.surjective y
      apply Subtype.ext
      have hc : (MulAut.conjNormal (n : G)) m = n * m * n⁻¹ :=
        Subtype.ext (by simp [MulAut.conjNormal_apply])
      change ((e n : Equiv.Perm (Fin 7)) * (e m) * (e n)⁻¹ : Equiv.Perm (Fin 7)) =
        ((e ((MulAut.conjNormal (n : G)) (e.symm (e m)))) : Equiv.Perm (Fin 7))
      rw [MulEquiv.symm_apply_apply, hc, map_mul, map_mul, map_inv]
      rfl
    change Φ.symm (MulAut.congr e (MulAut.conjNormal (n : G))) = _
    rw [← this, MulEquiv.symm_apply_apply]
  by_contra hNtop
  obtain ⟨g, hg⟩ : ∃ g : G, g ∉ N := by
    by_contra h; push Not at h; exact hNtop (eq_top_iff.2 fun g _ => h g)
  -- `ψ g` is an odd permutation
  have hgodd : ψ g ∉ alternatingGroup (Fin 7) := by
    intro hgA
    obtain ⟨n, hn⟩ := e.surjective ⟨ψ g, hgA⟩
    have : ψ g = ψ n := by rw [hψN, hn]
    exact hg (hψ this ▸ n.2)
  have hrange : ψ.range = ⊤ := by
    have hle : alternatingGroup (Fin 7) ≤ ψ.range := by
      intro σ hσ
      obtain ⟨n, hn⟩ := e.surjective ⟨σ, hσ⟩
      exact ⟨n, by rw [hψN, hn]⟩
    have hidx := Subgroup.index_dvd_of_le hle
    rw [alternatingGroup.index_eq_two] at hidx
    rcases (Nat.dvd_prime Nat.prime_two).mp hidx with h1 | h2
    · exact Subgroup.index_eq_one.mp h1
    · exfalso
      have hrel := Subgroup.relIndex_mul_index hle
      rw [h2, alternatingGroup.index_eq_two] at hrel
      have hrel1 : (alternatingGroup (Fin 7)).relIndex ψ.range = 1 := by omega
      exact hgodd (Subgroup.relIndex_eq_one.mp hrel1 ⟨g, rfl⟩)
  let eG : G ≃* Equiv.Perm (Fin 7) := MulEquiv.ofBijective ψ ⟨hψ, MonoidHom.range_eq_top.mp hrange⟩
  exact not_cyclicIndexTwo_perm_seven (cyclicIndexTwo_of_mulEquiv eG hP)

/-- Lemma 6.13, `M₁₁` case: `G = N`. -/
theorem eq_top_of_M11 [M11AutInner] [NativeM11EquivOpen] {N : Subgroup G} [N.Normal]
    (e : N ≃* Open.M11) (hC : Subgroup.centralizer (N : Set G) = ⊥) : N = ⊤ := by
  obtain ⟨en⟩ := NativeM11EquivOpen.nativeEquivOpen
  let f : N ≃* Blueprint.NativeSporadic.M11 := e.trans en.symm
  apply eq_top_iff.2
  intro g _
  obtain ⟨k, hk⟩ := M11AutInner.m11_aut_inner (MulAut.congr f (MulAut.conjNormal g))
  set n : N := f.symm k
  have h2 : ∀ m ∈ N, g * m * g⁻¹ = n * m * (n : G)⁻¹ := by
    intro m hm
    have h1 := congrArg (fun φ : MulAut Blueprint.NativeSporadic.M11 => f.symm (φ (f ⟨m, hm⟩))) hk
    change f.symm (f ((MulAut.conjNormal g) (f.symm (f ⟨m, hm⟩)))) = f.symm (k * f ⟨m, hm⟩ * k⁻¹) at h1
    rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply, map_mul, map_mul, map_inv,
      MulEquiv.symm_apply_apply] at h1
    have := congrArg Subtype.val h1
    simpa [MulAut.conjNormal_apply, n] using this
  have hc : (n : G)⁻¹ * g ∈ Subgroup.centralizer (N : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have := h2 m hm
    calc m * ((n : G)⁻¹ * g) = (n : G)⁻¹ * (n * m * (n : G)⁻¹) * g := by group
      _ = (n : G)⁻¹ * (g * m * g⁻¹) * g := by rw [this]
      _ = (n : G)⁻¹ * g * m := by group
  rw [hC, Subgroup.mem_bot] at hc
  have : g = n := by
    calc g = (n : G) * ((n : G)⁻¹ * g) := by group
      _ = n := by rw [hc, mul_one]
  rw [this]
  exact n.2

/-- `GaloisField p k` for an odd prime `p` and `p ^ k ≥ 3`: odd characteristic and at least 3 elements. -/
theorem galoisField_facts (p k : ℕ) [Fact p.Prime] (hp : Odd p) (hk : 3 ≤ p ^ k) :
    ringChar (GaloisField p k) ≠ 2 ∧ 3 ≤ Nat.card (GaloisField p k) := by
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk
  refine ⟨?_, by rw [GaloisField.card p k hk0]; exact hk⟩
  rw [ringChar.eq (GaloisField p k) p]
  rintro rfl
  exact (Nat.not_even_iff_odd.mpr hp) even_two

variable [SemilinearEquivAut.{0}] [AutAlternatingBijectiveConj] [M11AutInner] [NativeM11EquivOpen]

/-- Theorem 6.1 when `G` has a nonabelian minimal normal subgroup. -/
theorem theorem61_of_nonabelian (hP : CyclicIndexTwo G) (hO : OddCoreFree G) {N : Subgroup G}
    (hN : IsMinimalNormal N) (hnab : ∃ a b : N, a * b ≠ b * a) : Theorem61Conclusion G := by
  have hC := centralizer_minimalNormal_eq_bot hP hO hN hnab
  haveI := hN.1
  obtain ⟨-, hcases⟩ := nonabelian_minimalNormal_cases hP hN hnab
  unfold Theorem61Conclusion
  rcases hcases with ⟨⟨e⟩⟩ | ⟨p, k, hp, hpo, h5, ⟨e⟩⟩ | ⟨p, k, hp, hk, h3, ⟨e⟩⟩ | ⟨p, k, hp, hk, h1, ⟨e⟩⟩ | ⟨⟨e⟩⟩
  · -- (vii) `A₇`
    have htop := eq_top_of_alternatingSeven hP e hC
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))
    exact ⟨(Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm)).trans e⟩
  · -- (iv) `PSL(2,q)`
    obtain ⟨hchar, hcard⟩ := galoisField_facts p k hpo (by omega)
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨GaloisField p k, inferInstance, inferInstance, hchar, hcard,
      embedding_PGammaL2 e hC⟩)))
  · -- (v) `PSL(3,q)`
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, k, hp, hk, h3, N, inferInstance, ⟨e⟩, hC⟩))))
  · -- (vi) `PSU(3,q)`
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, k, hp, hk, h1, N, inferInstance, ⟨e⟩, hC⟩)))))
  · -- (viii) `M₁₁`
    have htop := eq_top_of_M11 e hC
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))
    exact ⟨(Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm)).trans e⟩

end Shapes

end CFSGOutside.GiuliettiKorchmaros
