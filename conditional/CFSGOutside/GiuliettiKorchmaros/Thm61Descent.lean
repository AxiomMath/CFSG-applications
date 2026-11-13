import CFSGOutside.GiuliettiKorchmaros.Thm61Quaternion
import CFSGOutside.GiuliettiKorchmaros.Thm61Centralizer

/-!
# Theorem 6.1: descent lemmas (`SL(2,3)` inside order 96, double cover of `A₇`)
-/

namespace CFSGOutside.GiuliettiKorchmaros

open CFSGOutside.Corpus
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

/-- (1) Involutions of `SL(2,3)`. -/
theorem sl23_sq_eq_one : ∀ x : SL(2, ZMod 3), x ^ 2 = 1 → x = 1 ∨ x = -1 := by
  have key : ∀ a b c d : ZMod 3, a * d - b * c = 1 →
      !![a, b; c, d] * !![a, b; c, d] = 1 → !![a, b; c, d] = 1 ∨ !![a, b; c, d] = -1 := by
    decide
  intro x hx
  have h := congrArg (fun y : SL(2, ZMod 3) => (y : Matrix (Fin 2) (Fin 2) (ZMod 3))) hx
  have hd := x.2
  simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, pow_two,
    Matrix.SpecialLinearGroup.coe_mul] at h
  rw [Matrix.det_fin_two] at hd
  have hx' : (x : Matrix (Fin 2) (Fin 2) (ZMod 3)) = !![x 0 0, x 0 1; x 1 0, x 1 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  rw [hx'] at h
  have := key _ _ _ _ hd h
  rcases this with h1 | h1
  · left; ext i j; rw [hx']; rw [h1]; simp
  · right; apply Subtype.ext; rw [hx', h1]; simp [Matrix.SpecialLinearGroup.coe_neg]; rfl

/-- (2) A subgroup isomorphic to `SL(2,3)` has at most one involution. -/
theorem involution_unique_of_sl23 {J : Subgroup G} (e : J ≃* SL(2, ZMod 3)) {x y : G} (hx : x ∈ J)
    (hy : y ∈ J) (hx2 : x ^ 2 = 1) (hy2 : y ^ 2 = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  have h1 : (e ⟨x, hx⟩) ^ 2 = 1 := by
    rw [← map_pow]; convert map_one e; exact Subtype.ext hx2
  have h2 : (e ⟨y, hy⟩) ^ 2 = 1 := by
    rw [← map_pow]; convert map_one e; exact Subtype.ext hy2
  have hne : ∀ z (hz : z ∈ J), z ≠ 1 → e ⟨z, hz⟩ ≠ 1 := by
    intro z hz hz1 h
    apply hz1
    have := e.injective (h.trans (map_one e).symm)
    exact congrArg Subtype.val this
  have hx3 : e ⟨x, hx⟩ = -1 := (sl23_sq_eq_one _ h1).resolve_left (hne x hx hx1)
  have hy3 : e ⟨y, hy⟩ = -1 := (sl23_sq_eq_one _ h2).resolve_left (hne y hy hy1)
  exact congrArg Subtype.val (e.injective (hx3.trans hy3.symm))

/-- (3) An index-2 subgroup isomorphic to `SL(2,3)` of a normal subgroup is normal. -/
theorem normal_of_sl23_index_two (M J : Subgroup G) [M.Normal] (hJM : J ≤ M)
    (hcard : Nat.card M = 2 * Nat.card J) (e : J ≃* SL(2, ZMod 3)) : J.Normal := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : ringChar (ZMod 3) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; norm_num
  -- every conjugate of `J` is contained in `J`
  have key : ∀ g : G, ∀ j ∈ J, g * j * g⁻¹ ∈ J := by
    intro g
    set K : Subgroup G := J.map (MulAut.conj g).toMonoidHom with hK
    have hKM : K ≤ M := by
      rintro _ ⟨j, hj, rfl⟩
      exact Subgroup.Normal.conj_mem inferInstance j (hJM hj) g
    have hKcard : Nat.card K = Nat.card J :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    set K' : Subgroup M := K.subgroupOf M with hK'
    have hidx : K'.index = 2 := by
      have h1 := Subgroup.relIndex_mul_card K M
      rw [inf_of_le_left hKM] at h1
      have : K.relIndex M = 2 := by
        have hpos : 0 < Nat.card J := Nat.card_pos
        rw [hKcard] at h1
        nlinarith
      exact this
    haveI : K'.Normal := Subgroup.normal_of_index_eq_two hidx
    have hQ : Nat.card (M ⧸ K') = 2 := hidx
    haveI : Finite (M ⧸ K') := inferInstance
    haveI : IsCyclic (M ⧸ K') := isCyclic_of_prime_card hQ
    letI : CommGroup (M ⧸ K') := IsCyclic.commGroup
    have hsq : ∀ a : M ⧸ K', a ^ 2 = 1 := by
      intro a; rw [← hQ]; exact pow_card_eq_one'
    let φ : SL(2, ZMod 3) →* M ⧸ K' :=
      (QuotientGroup.mk' K').comp ((Subgroup.inclusion hJM).comp e.symm.toMonoidHom)
    have hφ : φ = 1 := Key.sl2_hom_trivial (ZMod 3) hF hsq φ
    have hJK : J ≤ K := by
      intro j hj
      have h1 : φ (e ⟨j, hj⟩) = 1 := by rw [hφ]; rfl
      have h2 : (QuotientGroup.mk' K') (Subgroup.inclusion hJM ⟨j, hj⟩) = 1 := by
        simpa [φ] using h1
      have h3 := (QuotientGroup.eq_one_iff _).mp h2
      exact h3
    have hJK' : J = K := Subgroup.eq_of_le_of_card_ge hJK hKcard.le
    intro j hj
    have : g * j * g⁻¹ ∈ K := ⟨j, hj, rfl⟩
    rwa [← hJK'] at this
  refine ⟨fun n hn g => ?_⟩
  exact key g n hn

variable [SemilinearEquivAut.{0}] [SpecialLinearGroupSylowQuaternion.{0}]

/-- (4) No group of order 96 with `CyclicIndexTwo`, odd core-free, contains a normal subgroup `M` of order 48 with an
index-2 subgroup isomorphic to `SL(2,3)`. -/
theorem false_of_card_96 (hP : CyclicIndexTwo G) (hO : OddCoreFree G) (hG : Nat.card G = 96)
    (M J : Subgroup G) [M.Normal] (hJM : J ≤ M) (hM : Nat.card M = 48) (e : J ≃* SL(2, ZMod 3)) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF : ringChar (ZMod 3) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; norm_num
  have h3 : Nat.card (ZMod 3) = 3 := Nat.card_zmod 3
  have hJ : Nat.card J = 24 := by
    rw [Nat.card_congr e.toEquiv, card_sl2_of_card_three (ZMod 3) h3]
  haveI : J.Normal := normal_of_sl23_index_two M J hJM (by omega) e
  have hC := (centralizer_le_of_normal_sl2' hP hO hF J e).2
  have hcard := Key.card_le_of_normal_sl2 hF J e
  rw [Key.card_PGammaL2_of_card_three (ZMod 3) h3] at hcard
  have : Nat.card G ≤ 2 * 24 := le_trans hcard (Nat.mul_le_mul_right 24 hC)
  omega

/-- (5) An element of `S₇` whose order is a power of 2 has order dividing 4. -/
theorem perm_seven_orderOf_dvd_four' (σ : Equiv.Perm (Fin 7)) (n : ℕ) (h : orderOf σ ∣ 2 ^ n) :
    orderOf σ ∣ 4 := by
  have h1 : orderOf σ ∣ Nat.card (Equiv.Perm (Fin 7)) := orderOf_dvd_natCard σ
  rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
  have h2 : orderOf σ ∣ 16 := by
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h
    have hk4 : k ≤ 4 := by
      by_contra hc
      have h5 : 2 ^ 5 ∣ 5040 := by
        have := pow_dvd_pow 2 (not_le.mp hc)
        rw [hk'] at h1
        exact this.trans h1
      norm_num at h5
    rw [hk']
    exact pow_dvd_pow 2 hk4
  rw [← Equiv.Perm.lcm_cycleType]
  apply Multiset.lcm_dvd.mpr
  intro n hn
  have h1 : n ∣ 16 := (Equiv.Perm.dvd_of_mem_cycleType hn).trans h2
  have h2 : 2 ≤ n := Equiv.Perm.two_le_of_mem_cycleType hn
  have h3 : n ≤ 7 := by
    have := Equiv.Perm.le_card_support_of_mem_cycleType hn
    have h4 : σ.support.card ≤ 7 := by
      calc σ.support.card ≤ Finset.univ.card := Finset.card_le_univ _
        _ = 7 := by simp
    omega
  interval_cases n <;> revert h1 <;> decide

variable [AutAlternatingBijectiveConj]

/-- (6) No odd core-free group with `CyclicIndexTwo` contains, as a subgroup of index 2, a perfect normal subgroup
`M` of order 5040 with `M / Z(M) ≅ A₇`. -/
theorem false_of_double_cover_A7 (hP : CyclicIndexTwo G) (hO : OddCoreFree G) (M : Subgroup G) [M.Normal]
    (hidx : M.index = 2) (hperf : commutator M = ⊤) (hcard : Nat.card M = 5040)
    (e : M ⧸ Subgroup.center M ≃* alternatingGroup (Fin 7)) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- `|Z(M)| = 2`
  have hZ : Nat.card (Subgroup.center M) = 2 := by
    have h1 := Subgroup.card_mul_index (Subgroup.center M)
    rw [Subgroup.index_eq_card, Nat.card_congr e.toEquiv, nat_card_alternatingGroup] at h1
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at h1
    rw [hcard] at h1
    have : Nat.factorial 7 / 2 = 2520 := by decide
    rw [this] at h1
    omega
  -- exponent
  have hexp : ∀ x : M, x ^ 16 = 1 → x ^ 8 = 1 := by
    intro x hx
    have h1 : orderOf (e (QuotientGroup.mk x) : Equiv.Perm (Fin 7)) ∣ 2 ^ 4 := by
      rw [Subgroup.orderOf_coe]
      apply orderOf_dvd_of_pow_eq_one
      rw [← map_pow, ← QuotientGroup.mk_pow, show (2 : ℕ) ^ 4 = 16 by norm_num, hx]
      simp
    have h2 := orderOf_dvd_iff_pow_eq_one.mp (perm_seven_orderOf_dvd_four' _ 4 h1)
    have h3 : (e (QuotientGroup.mk x)) ^ 4 = 1 := Subtype.ext h2
    rw [← map_pow, ← QuotientGroup.mk_pow] at h3
    have h5 : x ^ 4 ∈ Subgroup.center M := (QuotientGroup.eq_one_iff _).mp (e.injective (h3.trans (map_one e).symm))
    have h6 : (⟨x ^ 4, h5⟩ : Subgroup.center M) ^ 2 = 1 := by
      rw [← hZ]; exact pow_card_eq_one'
    have h7 := congrArg Subtype.val h6
    simpa [← pow_mul] using h7
  -- a Sylow 2-subgroup of `M`, viewed in `G`
  have hd16 : 2 ^ 4 ∣ Nat.card M := by rw [hcard]; norm_num
  obtain ⟨P, hPc⟩ := Sylow.exists_subgroup_card_pow_prime 2 hd16
  set Q : Subgroup G := P.map M.subtype with hQ
  have hQcard : Nat.card Q = 16 := by
    rw [hQ, Subgroup.card_map_of_injective M.subtype_injective, hPc]; norm_num
  have hQ2 : IsPGroup 2 Q := (IsPGroup.of_card hPc).map M.subtype
  have hQM : Q ≤ M := by rintro _ ⟨x, _, rfl⟩; exact x.2
  have hQexp : ∀ q ∈ Q, q ^ (Nat.card Q / 2) = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hQcard]
    have h16 : x ^ 16 = 1 := by
      have := orderOf_dvd_natCard (⟨x, hx⟩ : P)
      rw [hPc, Subgroup.orderOf_mk] at this
      exact orderOf_dvd_iff_pow_eq_one.mp (this.trans (by norm_num))
    have := congrArg Subtype.val (hexp x h16)
    simpa using this
  have hYC : Nat.card (M ⊓ Subgroup.centralizer (M : Set G) : Subgroup G) ≤ 2 := by
    have hle : (M ⊓ Subgroup.centralizer (M : Set G) : Subgroup G) ≤ (Subgroup.center M).map M.subtype := by
      rintro g ⟨hgM, hgC⟩
      refine ⟨⟨g, hgM⟩, ?_, rfl⟩
      apply Subgroup.mem_center_iff.mpr
      intro m
      have := Subgroup.mem_centralizer_iff.mp hgC m m.2
      exact Subtype.ext this
    refine (Subgroup.card_le_of_le hle).trans ?_
    rw [Subgroup.card_map_of_injective M.subtype_injective, hZ]
  have hC2 := card_centralizer_le_two hP hO M hQM hQ2 (by rw [hQcard]; norm_num) hQexp hYC
  obtain ⟨ψ, hψ⟩ := Key.exists_hom_perm_seven M hperf e
  -- a subgroup of order 32 of `G`
  have hG : Nat.card G = 10080 := by
    have := Subgroup.card_mul_index M
    rw [hidx, hcard] at this; omega
  have hd32 : 2 ^ 5 ∣ Nat.card G := by rw [hG]; norm_num
  obtain ⟨P', hP'c⟩ := Sylow.exists_subgroup_card_pow_prime 2 hd32
  obtain ⟨C, hCP, hC, hCi⟩ := hP P' (IsPGroup.of_card hP'c)
  obtain ⟨g, hg⟩ := hC.exists_generator
  have hord : Nat.card C = orderOf g := (orderOf_eq_card_of_forall_mem_zpowers hg).symm
  have h1 := Subgroup.relIndex_mul_card C P'
  rw [inf_of_le_left hCP, hP'c] at h1
  have hdvd : orderOf (g : G) ∣ 2 ^ 5 := by
    rw [Subgroup.orderOf_coe, ← hord]
    exact ⟨C.relIndex P', by rw [← h1]; ring⟩
  have hge : 16 ≤ orderOf (g : G) := by
    rw [Subgroup.orderOf_coe, ← hord]
    have : C.relIndex P' * Nat.card C = 32 := by rw [h1]; norm_num
    nlinarith
  have hψo : orderOf (ψ g) ∣ 2 ^ 5 := (orderOf_map_dvd ψ (g : G)).trans hdvd
  have h4 := orderOf_dvd_iff_pow_eq_one.mp (perm_seven_orderOf_dvd_four' _ 5 hψo)
  have hg4 : (g : G) ^ 4 ∈ Subgroup.centralizer (M : Set G) := by
    rw [← hψ, MonoidHom.mem_ker, map_pow]; exact h4
  have h8 : (g : G) ^ 8 = 1 := by
    have h6 : (⟨(g : G) ^ 4, hg4⟩ : Subgroup.centralizer (M : Set G)) ^ Nat.card (Subgroup.centralizer (M : Set G)) = 1 :=
      pow_card_eq_one'
    have hpos : 0 < Nat.card (Subgroup.centralizer (M : Set G)) := Nat.card_pos
    have h7 : (⟨(g : G) ^ 4, hg4⟩ : Subgroup.centralizer (M : Set G)) ^ 2 = 1 := by
      generalize Nat.card (Subgroup.centralizer (M : Set G)) = c at h6 hpos hC2
      interval_cases c
      · have := congrArg Subtype.val h6
        have h' : (⟨(g : G) ^ 4, hg4⟩ : Subgroup.centralizer (M : Set G)) = 1 := by simpa using h6
        rw [h']; simp
      · exact h6
    have := congrArg Subtype.val h7
    simpa [← pow_mul] using this
  have := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h8)
  omega

end CFSGOutside.GiuliettiKorchmaros
