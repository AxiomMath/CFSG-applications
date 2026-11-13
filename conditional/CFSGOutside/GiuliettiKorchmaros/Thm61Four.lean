import CFSGOutside.GiuliettiKorchmaros.Thm61Nonabelian
import CFSGOutside.GiuliettiKorchmaros.TwoGroups
import CFSGOutside.GiuliettiKorchmaros.PSL23

/-!
# Theorem 6.1: abelian minimal normal subgroups (Lemma 6.5) and the case `|N| = 4` (Lemma 6.8)
-/

namespace CFSGOutside.GiuliettiKorchmaros

open CFSGOutside.Corpus
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

section

variable [MinimalNormalSimpleFactors.{0}] [TwoLePRankOfIsSimpleGroup.{0}]

/-- Lemma 6.5, abelian case: an abelian minimal normal subgroup of an odd core-free group with `CyclicIndexTwo` is an
elementary abelian 2-group of order 2 or 4. -/
theorem abelian_minimalNormal (hP : CyclicIndexTwo G) (hO : OddCoreFree G) {N : Subgroup G}
    (hN : IsMinimalNormal N) (hab : ∀ a b : N, a * b = b * a) :
    (Nat.card N = 2 ∨ Nat.card N = 4) ∧ ∀ x ∈ N, x ^ 2 = 1 := by
  obtain ⟨hNn, hN1, hmin⟩ := hN
  have hcomm : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hab ⟨x, hx⟩ ⟨y, hy⟩)
  have hNt : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hN1
  obtain ⟨p, hp, hpN⟩ := Nat.exists_prime_and_dvd (Finite.one_lt_card_iff_nontrivial.mpr hNt).ne'
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := N) p hpN
  -- the elements of `N` of order dividing `p`
  let K : Subgroup G :=
    { carrier := {y | y ∈ N ∧ y ^ p = 1}
      mul_mem' := fun {a b} ha hb => ⟨N.mul_mem ha.1 hb.1, by
        rw [(Commute.mul_pow (hcomm a ha.1 b hb.1) p), ha.2, hb.2, one_mul]⟩
      one_mem' := ⟨N.one_mem, one_pow p⟩
      inv_mem' := fun {a} ha => ⟨N.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hKn : K.Normal := ⟨fun y hy g => ⟨hNn.conj_mem y hy.1 g, by
    rw [conj_pow, hy.2, mul_one, mul_inv_cancel]⟩⟩
  have hKN : K ≤ N := fun y hy => hy.1
  have hK1 : K ≠ ⊥ := by
    intro h
    have hxK : (x : G) ∈ K := ⟨x.2, by
      have := pow_orderOf_eq_one x
      rw [hx] at this
      exact_mod_cast congrArg Subtype.val this⟩
    rw [h, Subgroup.mem_bot] at hxK
    have : x = 1 := Subtype.ext hxK
    rw [this, orderOf_one] at hx
    exact hp.one_lt.ne' hx.symm
  have hKeq : K = N := (hmin K hKn hKN).resolve_left hK1
  have hexp : ∀ y ∈ N, y ^ p = 1 := fun y hy => (hKeq ▸ hy : y ∈ K).2
  have hpgrp : IsPGroup p N := fun y => ⟨1, by
    rw [pow_one]; exact Subtype.ext (by simpa using hexp y y.2)⟩
  obtain ⟨m, hm⟩ := hpgrp.exists_card_eq
  have hp2 : p = 2 := by
    by_contra hp2
    have hodd : Odd (Nat.card N) := by
      rw [hm]
      exact (hp.odd_of_ne_two hp2).pow
    exact hN1 (hO N hNn hodd)
  subst hp2
  refine ⟨?_, hexp⟩
  have h4 := card_le_four_of_elem hP N (isMulComm_of N hcomm) hexp
  have h1 : 1 < Nat.card N := Finite.one_lt_card_iff_nontrivial.mpr hNt
  rw [hm] at h4 h1 ⊢
  rcases m with _ | _ | _ | m
  · simp at h1
  · left; rfl
  · right; rfl
  · exfalso
    have : 2 ^ 3 ≤ 2 ^ (m + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

end

/-- The automorphism group of a group of order 4 of exponent 2 has order dividing 6. -/
theorem card_mulAut_dvd_six {N : Type*} [Group N] [Finite N] (hN : Nat.card N = 4) :
    Nat.card (MulAut N) ∣ 6 := by
  classical
  haveI := Fintype.ofFinite N
  let f : MulAut N →* Equiv.Perm {x : N // x ≠ 1} :=
    { toFun := fun φ => φ.toEquiv.subtypeEquiv (fun x => by simp)
      map_one' := by ext; rfl
      map_mul' := fun φ ψ => by ext; rfl }
  have hf : Function.Injective f := by
    intro φ ψ h
    apply MulEquiv.ext
    intro x
    by_cases hx : x = 1
    · subst hx; simp
    · have := congrArg (fun σ : Equiv.Perm {x : N // x ≠ 1} => (σ ⟨x, hx⟩ : N)) h
      simpa [f] using this
  have h1 : Nat.card (MulAut N) ∣ Nat.card (Equiv.Perm {x : N // x ≠ 1}) := by
    rw [Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  have h3 : Nat.card {x : N // x ≠ 1} = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
      ← Nat.card_eq_fintype_card, hN]
  rw [Nat.card_perm, h3] at h1
  simpa [Nat.factorial] using h1


/-- A group of exponent 2 is commutative. -/
theorem comm_of_sq_eq_one {N : Subgroup G} (hexp : ∀ x ∈ N, x ^ 2 = 1) :
    ∀ x ∈ N, ∀ y ∈ N, x * y = y * x := by
  have hinv : ∀ z ∈ N, z⁻¹ = z := fun z hz =>
    inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hexp z hz)
  intro x hx y hy
  calc x * y = (x * y)⁻¹ := (hinv _ (N.mul_mem hx hy)).symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [hinv y hy, hinv x hx]

/-- A subgroup of order 4 and exponent 2 is not contained in a cyclic subgroup. -/
theorem not_le_cyclic_of_klein {N C : Subgroup G} (hN4 : Nat.card N = 4) (hexp : ∀ x ∈ N, x ^ 2 = 1)
    (hC : IsCyclic C) (hNC : N ≤ C) : False := by
  have hcyc : IsCyclic (N.subgroupOf C) := Subgroup.isCyclic _
  obtain ⟨x, hx⟩ := hcyc.exists_generator
  have hord : orderOf x = 4 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNC).toEquiv, hN4]
  have hx2 : x ^ 2 = 1 := by
    have := hexp ((x : C) : G) (Subgroup.mem_subgroupOf.mp x.2)
    apply Subtype.ext; apply Subtype.ext
    simpa using this
  have := orderOf_dvd_of_pow_eq_one hx2
  rw [hord] at this
  norm_num at this

/-- Under `CyclicIndexTwo`, a 2-subgroup centralizing a Klein four-group contained in it is abelian. -/
theorem comm_of_centralizes_klein (hP : CyclicIndexTwo G) {V N : Subgroup G} (hV : IsPGroup 2 V)
    (hNV : N ≤ V) (hcen : ∀ n ∈ N, ∀ v ∈ V, n * v = v * n) (hN4 : Nat.card N = 4)
    (hexp : ∀ x ∈ N, x ^ 2 = 1) : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := by
  obtain ⟨C, hCV, hC, hidx⟩ := hP V hV
  by_contra hnab
  push Not at hnab
  obtain ⟨x, hx, y, hy, hxy⟩ := hnab
  have hidx2 : C.relIndex V = 2 := by
    rcases Nat.lt_or_ge (C.relIndex V) 2 with h | h
    · exfalso
      have h1 : C.relIndex V = 1 := by
        have hm := Subgroup.relIndex_mul_card C V
        rw [inf_of_le_left hCV] at hm
        have : C.relIndex V ≠ 0 := by
          intro h0; rw [h0, zero_mul] at hm; exact (Nat.card_pos (α := V)).ne' hm.symm
        omega
      have hVC : V ≤ C := Subgroup.relIndex_eq_one.mp h1
      exact not_le_cyclic_of_klein hN4 hexp hC (hNV.trans hVC)
    · omega
  -- in `↥V`, the center lies in the cyclic subgroup of index 2
  have hU : IsCyclic (C.subgroupOf V) := by
    have e : C.subgroupOf V ≃* C := Subgroup.subgroupOfEquivOfLe hCV
    exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  have hcl := TwoGroups.center_le_of_index_two hU (by rw [← Subgroup.relIndex]; exact hidx2)
    ⟨⟨x, hx⟩, ⟨y, hy⟩, fun h => hxy (congrArg Subtype.val h)⟩
  have hNC : N ≤ C := by
    intro n hn
    have hnZ : (⟨n, hNV hn⟩ : V) ∈ Subgroup.center V := by
      rw [Subgroup.mem_center_iff]
      intro v
      exact Subtype.ext (hcen n hn v v.2).symm
    exact Subgroup.mem_subgroupOf.mp (hcl hnZ)
  exact not_le_cyclic_of_klein hN4 hexp hC hNC

/-- Under `CyclicIndexTwo`, an abelian subgroup has at most 4 elements of order dividing 2. -/
theorem card_sq_eq_one_le_four (hP : CyclicIndexTwo G) (V : Subgroup G)
    (hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) :
    Nat.card {x : V // x ^ 2 = 1} ≤ 4 := by
  let Ω : Subgroup G :=
    { carrier := {x | x ∈ V ∧ x ^ 2 = 1}
      mul_mem' := fun {a b} ha hb => ⟨V.mul_mem ha.1 hb.1, by
        rw [(Commute.mul_pow (hVc a ha.1 b hb.1) 2), ha.2, hb.2, one_mul]⟩
      one_mem' := ⟨V.one_mem, one_pow 2⟩
      inv_mem' := fun {a} ha => ⟨V.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have h4 : Nat.card Ω ≤ 4 :=
    card_le_four_of_elem hP Ω (isMulComm_of Ω fun a ha b hb => hVc a ha.1 b hb.1) fun x hx => hx.2
  refine le_trans (Nat.card_le_card_of_injective (fun x => (⟨(x.1 : G), x.1.2, by
    simpa using congrArg Subtype.val x.2⟩ : Ω)) ?_) h4
  intro a b h
  apply Subtype.ext; apply Subtype.ext
  exact congrArg (fun t : Ω => (t : G)) h

/-- An element of order dividing 3 normalizing a Klein four-group and fixing a nonidentity element of it
centralizes it. -/
theorem klein_fix {N : Subgroup G} (hN4 : Nat.card N = 4) (hexp : ∀ x ∈ N, x ^ 2 = 1) {g : G}
    (hg3 : g ^ 3 = 1) (hgN : ∀ x ∈ N, g * x * g⁻¹ ∈ N) {c : G} (hc : c ∈ N) (hc1 : c ≠ 1)
    (hgc : g * c * g⁻¹ = c) : ∀ x ∈ N, g * x * g⁻¹ = x := by
  classical
  intro x hx
  by_cases hx1 : x = 1
  · subst hx1; group
  by_cases hxc : x = c
  · subst hxc; exact hgc
  have hc2 : c * c = 1 := by rw [← pow_two]; exact hexp c hc
  have hxc1 : x * c ≠ 1 := fun h => hxc (by
    calc x = x * c * c := by rw [mul_assoc, hc2, mul_one]
      _ = c := by rw [h, one_mul])
  have hxcc : x * c ≠ c := fun h => hx1 (by
    calc x = x * c * c⁻¹ := by group
      _ = 1 := by rw [h, mul_inv_cancel])
  have hxcx : x * c ≠ x := fun h => hc1 (by
    calc c = x⁻¹ * (x * c) := by group
      _ = 1 := by rw [h, inv_mul_cancel])
  -- every element of `N` is `1`, `c`, `x` or `x * c`
  have hall : ∀ y ∈ N, y = 1 ∨ y = c ∨ y = x ∨ y = x * c := by
    intro y hy
    by_contra hne
    push Not at hne
    obtain ⟨h1, h2, h3, h4⟩ := hne
    let f : Fin 5 → N := ![⟨1, N.one_mem⟩, ⟨c, hc⟩, ⟨x, hx⟩, ⟨x * c, N.mul_mem hx hc⟩, ⟨y, hy⟩]
    have hf : Function.Injective f := by
      intro i j hij
      have hij' := congrArg Subtype.val hij
      fin_cases i <;> fin_cases j <;> simp [f] at hij' ⊢ <;>
        first
        | exact absurd hij' hc1
        | exact absurd hij' (Ne.symm hc1)
        | exact absurd hij' hx1
        | exact absurd hij' (Ne.symm hx1)
        | exact absurd hij' hxc1
        | exact absurd hij' (Ne.symm hxc1)
        | exact absurd hij' hxc
        | exact absurd hij' (Ne.symm hxc)
        | exact absurd hij' hxcc
        | exact absurd hij' (Ne.symm hxcc)
        | exact absurd hij' hxcx
        | exact absurd hij' (Ne.symm hxcx)
        | exact absurd hij' h1
        | exact absurd hij' (Ne.symm h1)
        | exact absurd hij' h2
        | exact absurd hij' (Ne.symm h2)
        | exact absurd hij' h3
        | exact absurd hij' (Ne.symm h3)
        | exact absurd hij' h4
        | exact absurd hij' (Ne.symm h4)
    have := Nat.card_le_card_of_injective f hf
    rw [Nat.card_eq_fintype_card, Fintype.card_fin, hN4] at this
    omega
  have hσx : g * x * g⁻¹ ∈ N := hgN x hx
  have hσx1 : g * x * g⁻¹ ≠ 1 := fun h => hx1 (by
    calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group)
  have hσxc : g * x * g⁻¹ ≠ c := fun h => hxc (by
    have h' : g * x * g⁻¹ = g * c * g⁻¹ := by rw [hgc]; exact h
    calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = g⁻¹ * (g * c * g⁻¹) * g := by rw [h']
      _ = c := by group)
  rcases hall _ hσx with h | h | h | h
  · exact absurd h hσx1
  · exact absurd h hσxc
  · exact h
  · exfalso
    -- conjugation by `g` swaps `x` and `x * c`, so `g ^ 3` does not fix `x`
    have h2 : g * (x * c) * g⁻¹ = x := by
      calc g * (x * c) * g⁻¹ = (g * x * g⁻¹) * (g * c * g⁻¹) := by group
        _ = x * c * c := by rw [h, hgc]
        _ = x := by rw [mul_assoc, hc2, mul_one]
    have h3 : g ^ 3 * x * (g ^ 3)⁻¹ = x * c := by
      calc g ^ 3 * x * (g ^ 3)⁻¹ = g * (g * (g * x * g⁻¹) * g⁻¹) * g⁻¹ := by
            rw [show g ^ 3 = g * g * g by rw [pow_succ, pow_succ, pow_one]]; group
        _ = x * c := by rw [h, h2, h]
    rw [hg3] at h3
    simp only [one_mul, inv_one, mul_one] at h3
    exact hxcx h3.symm

/-- A cyclic subgroup has at most one involution. -/
theorem cyclic_involution_unique {H : Subgroup G} (hH : IsCyclic H) {a b : G} (ha : a ∈ H) (hb : b ∈ H)
    (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  classical
  haveI := Fintype.ofFinite H
  by_contra hab
  have hle := IsCyclic.card_pow_eq_one_le (α := H) (n := 2) (by norm_num)
  have hsub : ({1, ⟨a, ha⟩, ⟨b, hb⟩} : Finset H) ⊆ Finset.univ.filter (fun x : H => x ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl
    · exact one_pow 2
    · exact Subtype.ext (by simpa using ha2)
    · exact Subtype.ext (by simpa using hb2)
  have hcard : ({1, ⟨a, ha⟩, ⟨b, hb⟩} : Finset H).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp only [Finset.mem_singleton, Subtype.mk.injEq]; exact hab
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨fun h => ha1 ?_, fun h => hb1 ?_⟩
      · have := congrArg Subtype.val h; simpa using this.symm
      · have := congrArg Subtype.val h; simpa using this.symm
  have := Finset.card_le_card hsub
  omega

section Four

variable [MinimalNormalSimpleFactors.{0}] [TwoLePRankOfIsSimpleGroup.{0}]

/-- Lemma 6.8: if `G` has a minimal normal subgroup of order 4, then `G` is a 2-group, or `G` has a normal
subgroup isomorphic to `PSL(2,3)` with trivial centralizer. -/
theorem four_cases (hP : CyclicIndexTwo G) (hO : OddCoreFree G) {N : Subgroup G} (hN : IsMinimalNormal N)
    (hN4 : Nat.card N = 4) (hexp : ∀ x ∈ N, x ^ 2 = 1) :
    IsPGroup 2 G ∨ ∃ M : Subgroup G, M.Normal ∧ Nonempty (M ≃* PSL(2, ZMod 3)) ∧
      Subgroup.centralizer (M : Set G) = ⊥ := by
  classical
  haveI := hN.1
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm := comm_of_sq_eq_one hexp
  set T := Subgroup.centralizer (N : Set G) with hTdef
  have hNT : N ≤ T := fun n hn m hm => hcomm m hm n hn
  have hcenT : ∀ n ∈ N, ∀ t ∈ T, n * t = t * n := fun n hn t ht =>
    Subgroup.mem_centralizer_iff.mp ht n hn
  -- a nonidentity element of `N`
  obtain ⟨z, hzN, hz1⟩ : ∃ z ∈ N, z ≠ 1 := by
    by_contra h
    push Not at h
    have : N = ⊥ := eq_bot_iff.2 fun x hx => (Subgroup.mem_bot).2 (h x hx)
    rw [this, Subgroup.card_bot] at hN4
    norm_num at hN4
  have hz2 : orderOf z = 2 := orderOf_eq_prime (hexp z hzN) hz1
  -- `T = C_G(N)` is a 2-group
  have hT2 : IsPGroup 2 T := by
    have hOT := Complement.oddCoreFree_of_normal hO T
    obtain ⟨V⟩ : Nonempty (Sylow 2 T) := inferInstance
    let NT : Subgroup T := N.comap T.subtype
    have hNTn : NT.Normal := Subgroup.Normal.comap inferInstance _
    have hNT2 : IsPGroup 2 NT := by
      apply IsPGroup.of_card (n := 2)
      have : Nat.card NT = Nat.card N := by
        apply Nat.card_congr
        exact (Subgroup.equivMapOfInjective NT T.subtype T.subtype_injective).toEquiv.trans
          (Equiv.subtypeEquivRight fun x => by
            simp only [NT, Subgroup.map_comap_eq, Subgroup.range_subtype, Subgroup.mem_inf]
            exact ⟨fun h => h.2, fun h => ⟨hNT h, h⟩⟩)
      rw [this, hN4]; norm_num
    have hNTV : NT ≤ V := hNT2.le_sylow_of_normal V
    let V' : Subgroup G := (V : Subgroup T).map T.subtype
    have hV'2 : IsPGroup 2 V' := V.isPGroup'.map _
    have hNV' : N ≤ V' := fun n hn => ⟨⟨n, hNT hn⟩, hNTV (show (⟨n, hNT hn⟩ : T) ∈ NT from hn), rfl⟩
    have hcen' : ∀ n ∈ N, ∀ v ∈ V', n * v = v * n := by
      rintro n hn _ ⟨t, -, rfl⟩
      exact hcenT n hn t t.2
    have hV'c := comm_of_centralizes_klein hP hV'2 hNV' hcen' hN4 hexp
    have hmemV' : ∀ x ∈ (V : Subgroup T), (x : G) ∈ V' := fun x hx => ⟨x, hx, rfl⟩
    refine Complement.isPGroup_of_abelian_sylow_of_central hOT V ?_ ⟨z, hNT hzN⟩
      (hNTV (show (⟨z, hNT hzN⟩ : T) ∈ NT from hzN)) ?_ ?_ ?_
    · intro x hx y hy
      exact Subtype.ext (hV'c _ (hmemV' x hx) _ (hmemV' y hy))
    · rw [Subgroup.mem_center_iff]
      intro t
      exact Subtype.ext (hcenT z hzN t t.2).symm
    · rw [← Subgroup.orderOf_mk (H := T) z (hNT hzN)] at hz2
      exact hz2
    · have h4 := card_sq_eq_one_le_four hP V' hV'c
      refine le_trans (Nat.card_le_card_of_injective (fun x => (⟨⟨((x.1 : T) : G), hmemV' x.1 x.1.2⟩, by
        apply Subtype.ext
        simpa using congrArg (fun t : (V : Subgroup T) => ((t : T) : G)) x.2⟩ :
          {y : V' // y ^ 2 = 1})) ?_) h4
      intro a b h
      apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
      exact congrArg (fun y : {y : V' // y ^ 2 = 1} => ((y : V') : G)) h
  -- `G / T` embeds in `Aut N`, of order dividing 6
  have hker : (MulAut.conjNormal : G →* MulAut N).ker = T := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
    constructor
    · intro h n hn
      have := congrArg (fun φ : MulAut N => ((φ ⟨n, hn⟩ : N) : G)) h
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
      calc n * g = (g * n * g⁻¹) * g := by rw [this]
        _ = g * n := by group
    · intro h
      apply MulEquiv.ext
      intro n
      apply Subtype.ext
      simp only [MulAut.conjNormal_apply, MulAut.one_apply]
      rw [← h n n.2]; group
  have hidx : T.index ∣ 6 := by
    rw [← hker, Subgroup.index_ker]
    exact (Subgroup.card_subgroup_dvd_card _).trans (card_mulAut_dvd_six hN4)
  obtain ⟨m, hm⟩ := hT2.exists_card_eq
  by_cases h3 : 3 ∣ T.index
  · right
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h3G : 3 ∣ Nat.card G := h3.trans (Subgroup.index_dvd_card T)
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := G) 3 h3G
    have hg3 : g ^ 3 = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
    have hgN : ∀ x ∈ N, g * x * g⁻¹ ∈ N := fun x hx => (inferInstance : N.Normal).conj_mem x hx g
    have hgT : g ∉ T := by
      intro hgT
      obtain ⟨k, hk⟩ := hT2 ⟨g, hgT⟩
      have h1 : orderOf (⟨g, hgT⟩ : T) = 3 := by rw [Subgroup.orderOf_mk]; exact hg
      have := orderOf_dvd_of_pow_eq_one hk
      rw [h1] at this
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.Prime.dvd_of_dvd_pow Nat.prime_three this)
      norm_num at this
    -- `g` fixes no nonidentity element of `N`
    have hnofix : ∀ c ∈ N, c ≠ 1 → g * c * g⁻¹ ≠ c := fun c hc hc1 hgc =>
      hgT (Subgroup.mem_centralizer_iff.mpr fun x hx => by
        have := klein_fix hN4 hexp hg3 hgN hc hc1 hgc x hx
        calc x * g = (g * x * g⁻¹) * g := by rw [this]
          _ = g * x := by group)
    -- `T = N`
    have hTc := comm_of_centralizes_klein hP hT2 hNT hcenT hN4 hexp
    have hTN : T = N := by
      by_contra hTN
      -- the involutions of `T` are those of `N`
      have hΩ : ∀ x ∈ T, x ^ 2 = 1 → x ∈ N := by
        intro x hxT hx2
        let Ω : Subgroup G :=
          { carrier := {y | y ∈ T ∧ y ^ 2 = 1}
            mul_mem' := fun {a b} ha hb => ⟨T.mul_mem ha.1 hb.1, by
              rw [(Commute.mul_pow (hTc a ha.1 b hb.1) 2), ha.2, hb.2, one_mul]⟩
            one_mem' := ⟨T.one_mem, one_pow 2⟩
            inv_mem' := fun {a} ha => ⟨T.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
        have hNΩ : N ≤ Ω := fun y hy => ⟨hNT hy, hexp y hy⟩
        have h4 : Nat.card Ω ≤ 4 := card_le_four_of_elem hP Ω
          (isMulComm_of Ω fun a ha b hb => hTc a ha.1 b hb.1) fun x hx => hx.2
        have := Subgroup.eq_of_le_of_card_ge hNΩ (by omega)
        rw [this]; exact ⟨hxT, hx2⟩
      -- the subgroup of squares of `T`
      let Sq : Subgroup G :=
        { carrier := {y | ∃ t ∈ T, y = t ^ 2}
          mul_mem' := by
            rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
            exact ⟨a * b, T.mul_mem ha hb, (Commute.mul_pow (hTc a ha b hb) 2).symm⟩
          one_mem' := ⟨1, T.one_mem, (one_pow 2).symm⟩
          inv_mem' := by
            rintro _ ⟨a, ha, rfl⟩
            exact ⟨a⁻¹, T.inv_mem ha, (inv_pow a 2).symm⟩ }
      -- `Sq` lies in a cyclic subgroup
      obtain ⟨C, hCT, hC, hCidx⟩ := hP T hT2
      have hSqC : Sq ≤ C := by
        rintro _ ⟨t, ht, rfl⟩
        rcases Nat.lt_or_ge (C.relIndex T) 2 with h | h
        · have h1 : C.relIndex T = 1 := by
            have hm' := Subgroup.relIndex_mul_card C T
            rw [inf_of_le_left hCT] at hm'
            have : C.relIndex T ≠ 0 := by
              intro h0; rw [h0, zero_mul] at hm'; exact (Nat.card_pos (α := T)).ne' hm'.symm
            omega
          exact Subgroup.relIndex_eq_one.mp h1 (T.pow_mem ht 2)
        · have h2 : (C.subgroupOf T).index = 2 := by
            rw [← Subgroup.relIndex]; omega
          have := Subgroup.sq_mem_of_index_two h2 ⟨t, ht⟩
          exact Subgroup.mem_subgroupOf.mp this
      have hSqcyc : IsCyclic Sq := by
        have hcyc : IsCyclic (Sq.subgroupOf C) := Subgroup.isCyclic _
        exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hSqC).toMonoidHom
          (Subgroup.subgroupOfEquivOfLe hSqC).surjective
      -- `Sq` is nontrivial, since `T ≠ N`
      have hSq1 : ∃ s ∈ Sq, s ≠ 1 := by
        by_contra h
        push Not at h
        have hexpT : ∀ x ∈ T, x ^ 2 = 1 := fun x hx => (h _ ⟨x, hx, rfl⟩)
        apply hTN
        refine (Subgroup.eq_of_le_of_card_ge hNT ?_).symm
        have := card_le_four_of_elem hP T (isMulComm_of T hTc) hexpT
        omega
      -- an involution in `Sq`
      obtain ⟨s, hsSq, hs1⟩ := hSq1
      have hSq2 : IsPGroup 2 Sq := fun y => by
        obtain ⟨t, ht, hyt⟩ := y.2
        obtain ⟨k, hk⟩ := hT2 ⟨t, ht⟩
        refine ⟨k, Subtype.ext ?_⟩
        rw [Subgroup.coe_pow, hyt, ← pow_mul, mul_comm, pow_mul]
        have := congrArg Subtype.val hk
        simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
        rw [this, one_pow, Subgroup.coe_one]
      have hSqnt : Nontrivial Sq := ⟨⟨⟨s, hsSq⟩, 1, fun h => hs1 (congrArg Subtype.val h)⟩⟩
      obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := Sq) 2 (by
        obtain ⟨k, hk⟩ := hSq2.exists_card_eq
        rw [hk]
        rcases k with _ | k
        · exfalso; rw [pow_zero] at hk
          exact (Finite.one_lt_card_iff_nontrivial.mpr hSqnt).ne' hk
        · exact dvd_pow_self 2 (Nat.succ_ne_zero k))
      have hc2 : (c : G) ^ 2 = 1 := by
        have := pow_orderOf_eq_one c; rw [hc] at this
        simpa using congrArg Subtype.val this
      have hc1 : (c : G) ≠ 1 := fun h => by
        have : c = 1 := Subtype.ext h
        rw [this, orderOf_one] at hc; norm_num at hc
      have hcT : (c : G) ∈ T := by obtain ⟨t, ht, ht'⟩ := c.2; rw [ht']; exact T.pow_mem ht 2
      have hcN : (c : G) ∈ N := hΩ _ hcT hc2
      -- conjugation by `g` preserves `Sq`, so fixes its unique involution
      have hgSq : g * c * g⁻¹ ∈ Sq := by
        obtain ⟨t, ht, ht'⟩ := c.2
        refine ⟨g * t * g⁻¹, (inferInstance : T.Normal).conj_mem t ht g, ?_⟩
        rw [ht', conj_pow]
      have hgc : g * c * g⁻¹ = c := cyclic_involution_unique hSqcyc hgSq c.2
        (by rw [conj_pow, hc2, mul_one, mul_inv_cancel]) hc2
        (fun h => hc1 (by
          calc (c : G) = g⁻¹ * (g * c * g⁻¹) * g := by group
            _ = 1 := by rw [h]; group)) hc1
      exact hnofix c hcN hc1 hgc
    -- the subgroup `N' = ⟨g⟩ N` of order 12
    obtain ⟨N', hN'⟩ : ∃ N' : Subgroup G, N' = Subgroup.zpowers g ⊔ N := ⟨_, rfl⟩
    have hNN' : N ≤ N' := hN' ▸ le_sup_right
    have hgN' : g ∈ N' := hN' ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers g)
    have hinf : N ⊓ Subgroup.zpowers g = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxN, hxg⟩ := Subgroup.mem_inf.mp hx
      rw [Subgroup.mem_bot]
      have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (hexp x hxN)
      have h3 : orderOf x ∣ 3 := by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxg
        exact orderOf_dvd_of_pow_eq_one (by
          rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg3, one_zpow])
      have : orderOf x ∣ Nat.gcd 2 3 := Nat.dvd_gcd h2 h3
      rw [orderOf_dvd_iff_pow_eq_one] at this
      simpa using this
    have hcardN' : Nat.card N' = 12 := by
      have h1 := Subgroup.relIndex_mul_card N (Subgroup.zpowers g)
      rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, hg] at h1
      have h2 : N.relIndex N' * Nat.card N = Nat.card N' := by
        have := Subgroup.relIndex_mul_card N N'
        rwa [inf_of_le_left hNN'] at this
      have h3' : N.relIndex N' = 3 := by
        rw [hN', Subgroup.relIndex_sup_right]; omega
      rw [h3', hN4] at h2
      omega
    have hcardG : Nat.card G = 4 * T.index := by
      rw [← Subgroup.card_mul_index T, hTN, hN4]
    have hN'n : N'.Normal := by
      have h6 : T.index = 3 ∨ T.index = 6 := by
        have hle := Nat.le_of_dvd (by norm_num) hidx
        have hpos : 0 < T.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
        interval_cases hT : T.index <;> first | (left; rfl) | (right; rfl) | omega
      rcases h6 with h | h
      · have : N' = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hcardN', hcardG, h])
        rw [this]; infer_instance
      · apply Subgroup.normal_of_index_eq_two
        have := Subgroup.card_mul_index N'
        rw [hcardN', hcardG, h] at this
        omega
    refine ⟨N', hN'n, ?_, ?_⟩
    · -- `N' ≅ PSL(2,3)`
      apply PSL23.nonempty_mulEquiv_psl23 hcardN' (N.subgroupOf N') (Subgroup.Normal.subgroupOf inferInstance _)
      · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNN').toEquiv, hN4]
      · apply le_antisymm
        · intro x hx
          rw [Subgroup.mem_subgroupOf, ← hTN, hTdef, Subgroup.mem_centralizer_iff]
          intro n hn
          have := Subgroup.mem_centralizer_iff.mp hx ⟨n, hNN' hn⟩ (by
            rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]; exact hn)
          exact congrArg Subtype.val this
        · intro x hx
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          rw [Subgroup.mem_subgroupOf] at hx
          rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hy
          exact Subtype.ext (hcomm _ hy _ hx)
    · -- trivial centralizer
      rw [eq_bot_iff]
      intro c hc
      rw [Subgroup.mem_bot]
      have hcT : c ∈ T := Subgroup.mem_centralizer_iff.mpr fun n hn =>
        Subgroup.mem_centralizer_iff.mp hc n (hNN' hn)
      rw [hTN] at hcT
      by_contra hc1
      have hgc : g * c * g⁻¹ = c := by
        have := Subgroup.mem_centralizer_iff.mp hc g hgN'
        rw [this]; group
      exact hnofix c hcT hc1 hgc
  · left
    have hidx2 : T.index ∣ 2 := by
      have : Nat.Coprime 3 T.index := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
      have h6 : (6 : ℕ) = 2 * 3 := by norm_num
      rw [h6] at hidx
      exact (Nat.Coprime.symm this).dvd_of_dvd_mul_right hidx
    rcases (Nat.dvd_prime Nat.prime_two).mp hidx2 with h1 | h2
    · apply IsPGroup.of_card (n := m)
      rw [← Subgroup.card_mul_index T, hm, h1, mul_one]
    · apply IsPGroup.of_card (n := m + 1)
      rw [← Subgroup.card_mul_index T, hm, h2, pow_succ]

end Four

end CFSGOutside.GiuliettiKorchmaros
