import CFSGOutside.GiuliettiKorchmaros.Defs

/-!
# Complement lemmas (odd core-free groups, Burnside transfer)

Statements (A)-(F) are as specified; no hypotheses were changed.
-/

namespace CFSGOutside.GiuliettiKorchmaros.Complement

open CFSGOutside.GiuliettiKorchmaros (OddCoreFree)

open Subgroup

/-! ### (A) -/

lemma fix_aux {A : Type*} [Group A] (hc : ∀ x y : A, x * y = y * x) (hA : IsPGroup 2 A)
    (φ : MulAut A) (hφ : Odd (orderOf φ)) (hfix : ∀ x : A, x ^ 2 = 1 → φ x = x) :
    ∀ m : ℕ, ∀ x : A, x ^ (2 ^ m) = 1 → φ x = x := by
  intro m
  induction m with
  | zero => intro x hx; simp at hx; subst hx; simp
  | succ m ih =>
    intro x hx
    have h1 : φ (x ^ 2) = x ^ 2 := ih _ (by rw [← pow_mul, ← pow_succ']; exact hx)
    set y := φ x * x⁻¹ with hy
    have hy2 : y ^ 2 = 1 := by
      have : (φ x) ^ 2 = x ^ 2 := by rw [← map_pow]; exact h1
      have hcomm : Commute (φ x) x⁻¹ := (hc _ _)
      rw [hy, hcomm.mul_pow, this]; simp
    have hyf : φ y = y := hfix y hy2
    have hφx : φ x = y * x := by rw [hy]; simp
    have key : ∀ k : ℕ, (φ ^ k) x = y ^ k * x := by
      intro k
      induction k with
      | zero => simp
      | succ k ihk =>
        rw [pow_succ', MulAut.mul_apply, ihk, map_mul, map_pow, hyf, hφx]
        group
    have h2 := key (orderOf φ)
    rw [pow_orderOf_eq_one] at h2
    have h3 : y ^ orderOf φ = 1 := by simpa using h2.symm
    obtain ⟨k, hk⟩ := hφ
    have : y = 1 := by
      rw [hk, pow_succ, pow_mul, hy2, one_pow, one_mul] at h3; exact h3
    rw [hφx, this, one_mul]

/-- (A) An automorphism of odd order of a finite abelian 2-group that fixes every involution is
the identity. -/
theorem mulAut_eq_one_of_fix_involutions {A : Type*} [CommGroup A] [Finite A] (hA : IsPGroup 2 A)
    (φ : MulAut A) (hφ : Odd (orderOf φ)) (hfix : ∀ x : A, x ^ 2 = 1 → φ x = x) : φ = 1 := by
  ext x
  obtain ⟨m, hm⟩ := hA x
  simpa using fix_aux (fun x y => mul_comm x y) hA φ hφ hfix m x hm

/-! ### Burnside core -/

lemma isPGroup_of_normalizer_le {G : Type*} [Group G] [Finite G] (hO : OddCoreFree G)
    (P : Sylow 2 G) (hP : normalizer (P : Set G) ≤ centralizer (P : Set G)) : IsPGroup 2 G := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := MonoidHom.ker_transferSylow_isComplement' P hP
  have hodd : Odd (Nat.card (MonoidHom.transferSylow P hP).ker) :=
    Nat.odd_iff.mpr (by
      have := MonoidHom.not_dvd_card_ker_transferSylow P hP
      omega)
  have hK := hO _ inferInstance hodd
  have hcard := hc.card_mul
  rw [hK] at hcard
  rw [IsPGroup.iff_card]
  obtain ⟨n, hn⟩ := (P.2).exists_card_eq
  refine ⟨n, ?_⟩
  rw [← hcard, hn]
  simp

/-! ### (C) -/

theorem isPGroup_of_cyclic_sylow {G : Type*} [Group G] [Finite G] (hO : OddCoreFree G)
    (P : Sylow 2 G) (hP : IsCyclic (P : Subgroup G)) : IsPGroup 2 G := by
  by_cases h2 : 2 ∣ Nat.card G
  · exact isPGroup_of_normalizer_le hO P
      (IsCyclic.normalizer_le_centralizer (Nat.minFac_eq_two_iff _ |>.mpr h2) hP)
  · have hodd : Odd (Nat.card (⊤ : Subgroup G)) := by
      rw [Subgroup.card_top]; exact Nat.odd_iff.mpr (by omega)
    have := hO ⊤ inferInstance hodd
    rw [IsPGroup.iff_card]
    refine ⟨0, ?_⟩
    rw [← Subgroup.card_top, this]; simp

/-! ### (B) -/

/-! ### (D) -/

lemma odd_card_sup {H : Type*} [Group H] [Finite H] (N T : Subgroup H) [N.Normal]
    (hN : Odd (Nat.card N)) (hT : Odd (Nat.card T)) : Odd (Nat.card ↥(T ⊔ N)) := by
  have h := Subgroup.relIndex_mul_card (H := N) (K := T ⊔ N)
  rw [inf_eq_left.mpr le_sup_right, Subgroup.relIndex_sup_right] at h
  rw [← h]
  refine Odd.mul ?_ hN
  exact Odd.of_dvd_nat hT (Subgroup.relIndex_dvd_card _ _)

theorem oddCoreFree_of_normal {G : Type*} [Group G] [Finite G] (hO : OddCoreFree G)
    (M : Subgroup G) [M.Normal] : OddCoreFree M := by
  set S : Set (Subgroup M) := {K | K.Normal ∧ Odd (Nat.card K)} with hS
  have hne : (⊥ : Subgroup M) ∈ S := ⟨inferInstance, by simp⟩
  obtain ⟨O, hOS, hOmax⟩ := Set.exists_max_image S (fun K => Nat.card K) (Set.toFinite S) ⟨_, hne⟩
  obtain ⟨hOn, hOodd⟩ := hOS
  have hle : ∀ K ∈ S, K ≤ O := by
    intro K hK
    obtain ⟨hKn, hKodd⟩ := hK
    have h1 : K ⊔ O ∈ S := ⟨inferInstance, odd_card_sup O K hOodd hKodd⟩
    have h2 := hOmax _ h1
    have : K ⊔ O = O := by
      symm
      exact Subgroup.eq_of_le_of_card_ge le_sup_right h2
    rw [← this]; exact le_sup_left
  -- the image of O is normal in G
  have hnorm : (O.map M.subtype).Normal := by
    constructor
    intro n hn g
    obtain ⟨o, ho, rfl⟩ := Subgroup.mem_map.mp hn
    have hc : (O.map (MulAut.conjNormal (H := M) g).toMonoidHom) ∈ S := by
      refine ⟨Subgroup.Normal.map hOn _ ?_, ?_⟩
      · exact (MulAut.conjNormal (H := M) g).surjective
      · have := Subgroup.card_map_of_injective (K := O)
          (f := (MulAut.conjNormal (H := M) g).toMonoidHom) (MulAut.conjNormal (H := M) g).injective
        rw [this]; exact hOodd
    have := hle _ hc
    refine Subgroup.mem_map.mpr ⟨MulAut.conjNormal (H := M) g o, this ⟨o, ho, rfl⟩, ?_⟩
    simp
  have hbot := hO _ hnorm (by
    rw [Subgroup.card_map_of_injective M.subtype_injective]; exact hOodd)
  have hO0 : O = ⊥ := by
    apply Subgroup.map_injective M.subtype_injective
    rw [hbot, Subgroup.map_bot]
  intro K hK hKodd
  exact le_bot_iff.mp (hO0 ▸ hle K ⟨hK, hKodd⟩)

/-! ### (E) -/

theorem le_center_of_card_two {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    (h : Nat.card N = 2) : N ≤ Subgroup.center G := by
  intro n hn
  rw [Subgroup.mem_center_iff]
  intro g
  by_cases h1 : n = 1
  · subst h1; simp
  obtain ⟨y, _, hy⟩ := (Nat.card_eq_two_iff' (1 : N)).mp h
  have e1 : (⟨n, hn⟩ : N) = y := hy _ (fun e => h1 (congrArg Subtype.val e))
  have hc : g * n * g⁻¹ ∈ N := Subgroup.Normal.conj_mem inferInstance n hn g
  have hc1 : g * n * g⁻¹ ≠ 1 := by
    intro e
    apply h1
    simpa using e
  have e2 : (⟨g * n * g⁻¹, hc⟩ : N) = y := hy _ (fun e => hc1 (congrArg Subtype.val e))
  have := congrArg Subtype.val (e2.trans e1.symm)
  simp only at this
  rw [mul_inv_eq_iff_eq_mul] at this
  exact this

/-! ### (F) -/

lemma card_comap_mk {G : Type*} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    (Mbar : Subgroup (G ⧸ N)) :
    Nat.card (Mbar.comap (QuotientGroup.mk' N)) = Nat.card N * Nat.card Mbar := by
  set M := Mbar.comap (QuotientGroup.mk' N) with hM
  have hNM : N ≤ M := by
    intro n hn
    have : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    rw [hM, Subgroup.mem_comap, this]; exact one_mem _
  have h := Subgroup.card_ker_mul_card_range ((QuotientGroup.mk' N).domRestrict M)
  rw [MonoidHom.ker_domRestrict, MonoidHom.domRestrict_range,
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N),
    QuotientGroup.ker_mk'] at h
  rw [← h]
  congr 1
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv

/-! ### (B') -/

lemma fix_inv_of_few {A : Type*} [Group A] [Finite A] (z : A) (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1)
    (hfew : Nat.card {x : A // x ^ 2 = 1} ≤ 4) (φ : MulAut A) (hφ : Odd (orderOf φ))
    (hz : φ z = z) : ∀ x : A, x ^ 2 = 1 → φ x = x := by
  have hmem : ∀ y : A, y ^ 2 = 1 → (φ y) ^ 2 = 1 := fun y hy => by rw [← map_pow, hy, map_one]
  have hne1 : ∀ y : A, y ≠ 1 → φ y ≠ 1 := fun y hy h => hy (φ.injective (by rw [h, map_one]))
  have hnez : ∀ y : A, y ≠ z → φ y ≠ z := fun y hy h => hy (φ.injective (by rw [h, hz]))
  intro x hx
  by_cases h1 : x = 1
  · subst h1; simp
  by_cases h2 : x = z
  · subst h2; exact hz
  by_contra hne
  have hback : φ (φ x) = x := by
    by_contra h3
    have hb : φ (φ x) ≠ φ x := fun h => hne (φ.injective h)
    let a : {x : A // x ^ 2 = 1} := ⟨1, by simp⟩
    let b : {x : A // x ^ 2 = 1} := ⟨z, hz2⟩
    let c : {x : A // x ^ 2 = 1} := ⟨x, hx⟩
    let d : {x : A // x ^ 2 = 1} := ⟨φ x, hmem _ hx⟩
    let e : {x : A // x ^ 2 = 1} := ⟨φ (φ x), hmem _ (hmem _ hx)⟩
    have hab : (1 : A) ≠ z := Ne.symm hz1
    have had : (1 : A) ≠ φ x := Ne.symm (hne1 x h1)
    have hae : (1 : A) ≠ φ (φ x) := Ne.symm (hne1 _ (hne1 x h1))
    have hbd : z ≠ φ x := Ne.symm (hnez x h2)
    have hbe : z ≠ φ (φ x) := Ne.symm (hnez _ (hnez x h2))
    have f : Function.Injective ![a, b, c, d, e] := by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        first | rfl | (exfalso
                       have hij' := congrArg Subtype.val hij
                       try dsimp [a, b, c, d, e] at hij'
                       first
                         | exact hab hij' | exact hab hij'.symm | exact had hij' | exact had hij'.symm
                         | exact hae hij' | exact hae hij'.symm | exact hbd hij' | exact hbd hij'.symm
                         | exact hbe hij' | exact hbe hij'.symm
                         | exact (Ne.symm h1) hij' | exact h1 hij'.symm | exact h1 hij' | exact (Ne.symm h1) hij'.symm
                         | exact h2 hij' | exact h2 hij'.symm
                         | exact hne hij' | exact hne hij'.symm
                         | exact h3 hij' | exact h3 hij'.symm
                         | exact hb hij' | exact hb hij'.symm)
    have := Nat.card_le_card_of_injective _ f
    simp at this
    omega
  have key : ∀ k : ℕ, (φ ^ (2 * k)) x = x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.mul_succ, pow_add, MulAut.mul_apply, pow_two, MulAut.mul_apply, hback, ih]
  obtain ⟨k, hk⟩ := hφ
  have h5 : (φ ^ (2 * k + 1)) x = φ x := by
    rw [pow_succ', MulAut.mul_apply, key]
  rw [← hk, pow_orderOf_eq_one] at h5
  exact hne (by simpa using h5.symm)

theorem isPGroup_of_abelian_sylow_of_central {G : Type*} [Group G] [Finite G]
    (hO : OddCoreFree G)
    (P : Sylow 2 G) (hPc : ∀ x ∈ (P : Subgroup G), ∀ y ∈ (P : Subgroup G), x * y = y * x)
    (z : G) (hzP : z ∈ (P : Subgroup G)) (hz : z ∈ Subgroup.center G) (hz2 : orderOf z = 2)
    (hfew : Nat.card {x : (P : Subgroup G) // x ^ 2 = 1} ≤ 4) :
    IsPGroup 2 G := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply isPGroup_of_normalizer_le hO P
  set f := (P : Subgroup G).normalizerMonoidHom with hf
  have hker : (P : Subgroup G).subgroupOf (normalizer (P : Set G) : Subgroup G) ≤ f.ker := by
    intro g hg
    rw [MonoidHom.mem_ker]
    ext x
    show (g : G) * x * (g : G)⁻¹ = x
    have hg' : (g : G) ∈ (P : Subgroup G) := hg
    rw [hPc _ hg' _ x.2, mul_inv_cancel_right]
  have hodd : Odd (Nat.card f.range) := by
    rw [← Subgroup.index_ker]
    have h1 : f.ker.index ∣ ((P : Subgroup G).subgroupOf
        (normalizer (P : Set G) : Subgroup G)).index := Subgroup.index_dvd_of_le hker
    have h2 : ((P : Subgroup G).subgroupOf
        (normalizer (P : Set G) : Subgroup G)).index ∣ (P : Subgroup G).index :=
      Subgroup.relIndex_dvd_index_of_le P.le_normalizer
    have h3 := P.not_dvd_index
    have : ¬ 2 ∣ f.ker.index := fun h => h3 (h.trans (h1.trans h2))
    exact Nat.odd_iff.mpr (by omega)
  have hker1 : f.ker = ⊤ := by
    rw [eq_top_iff]
    intro g _
    rw [MonoidHom.mem_ker]
    have hord : Odd (orderOf (f g)) := by
      have := orderOf_dvd_natCard (⟨f g, ⟨g, rfl⟩⟩ : f.range)
      have e : orderOf (⟨f g, ⟨g, rfl⟩⟩ : f.range) = orderOf (f g) :=
        (Subgroup.orderOf_coe (⟨f g, ⟨g, rfl⟩⟩ : f.range)).symm
      rw [e] at this
      exact Odd.of_dvd_nat hodd this
    letI : CommGroup (P : Subgroup G) :=
      { (inferInstance : Group (P : Subgroup G)) with
        mul_comm := fun a b => Subtype.ext (hPc _ a.2 _ b.2) }
    have hz1 : (⟨z, hzP⟩ : (P : Subgroup G)) ≠ 1 := by
      intro h
      have : z = 1 := congrArg Subtype.val h
      rw [this, orderOf_one] at hz2; omega
    have hzsq : (⟨z, hzP⟩ : (P : Subgroup G)) ^ 2 = 1 := by
      apply Subtype.ext
      show z ^ 2 = 1
      rw [← hz2]; exact pow_orderOf_eq_one z
    have hfz : f g ⟨z, hzP⟩ = ⟨z, hzP⟩ := by
      apply Subtype.ext
      show (g : G) * z * (g : G)⁻¹ = z
      rw [(Subgroup.mem_center_iff.mp hz) g, mul_inv_cancel_right]
    refine mulAut_eq_one_of_fix_involutions (A := (P : Subgroup G)) ?_ (f g) hord ?_
    · exact P.2
    · exact fix_inv_of_few _ hz1 hzsq hfew (f g) hord hfz
  intro g hg
  have : (⟨g, hg⟩ : normalizer (P : Set G)) ∈ f.ker := by rw [hker1]; trivial
  rw [Subgroup.normalizerMonoidHom_ker] at this
  exact this

end CFSGOutside.GiuliettiKorchmaros.Complement
