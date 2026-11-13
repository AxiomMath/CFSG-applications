import CFSGOutside.Corpus.MinimalNormalSimpleFactors
import CFSGOutside.Corpus.TwoLePRankOfIsSimpleGroup
import CFSGOutside.ChillagSonn.Metacyclic

/-!
# A nonabelian minimal normal subgroup of a Sylow-metacyclic group is simple

As in the proof of Lemma (1.6): a minimal normal subgroup is a direct product of conjugate simple groups, each of
2-rank at least 2, and two factors would give an elementary abelian subgroup of order 16. Adapted from
`GiuliettiKorchmaros/Simple.lean`, with "no elementary abelian subgroup of order 8" coming from
`SylowMetacyclic.card_le_four`.
-/

namespace CFSGOutside.ChillagSonn

open CFSGOutside.Corpus

section A

variable {G : Type} [Group G] [Finite G] [MinimalNormalSimpleFactors.{0}] [TwoLePRankOfIsSimpleGroup.{0}]

omit [MinimalNormalSimpleFactors.{0}] [TwoLePRankOfIsSimpleGroup.{0}] in
theorem elemAb_sq {H : Type} [Group H] (A : Subgroup H) [hA : IsElementaryAbelian 2 A] (x : A) :
    x ^ 2 = 1 := by
  have h := hA.exponent_dvd_p
  obtain ⟨k, hk⟩ := h
  rw [hk, pow_mul, Monoid.pow_exponent_eq_one, one_pow]

theorem exists_elemAb_big (H : Type) [Group H] [Finite H] [IsSimpleGroup H]
    (hab : ∃ a b : H, a * b ≠ b * a) :
    ∃ A : Subgroup H, (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ (∀ x ∈ A, x ^ 2 = 1) ∧
      ∃ m, 2 ≤ m ∧ Nat.card A = 2 ^ m := by
  have h2 := TwoLePRankOfIsSimpleGroup.two_le_pRank_of_isSimpleGroup hab
  unfold pRank at h2
  have hne : {r : ℕ | ∃ A : Subgroup H, IsElementaryAbelian 2 A ∧ Nat.card A = 2 ^ r}.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h] at h2
    simp at h2
  have hbdd : BddAbove {r : ℕ | ∃ A : Subgroup H, IsElementaryAbelian 2 A ∧ Nat.card A = 2 ^ r} := by
    refine ⟨Nat.card H, fun r ⟨A, _, hA⟩ => ?_⟩
    have := Subgroup.card_le_card_group A
    have h3 : r < 2 ^ r := Nat.lt_two_pow_self
    omega
  obtain ⟨A, hA, hcard⟩ := Nat.sSup_mem hne hbdd
  refine ⟨A, ?_, ?_, _, h2, hcard⟩
  · intro a ha b hb
    have := hA.toIsMulCommutative
    exact congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨a, ha⟩ : A) ⟨b, hb⟩)
  · intro x hx
    exact congrArg Subtype.val (elemAb_sq A ⟨x, hx⟩)

theorem exists_elem4 (H : Type) [Group H] [Finite H] [IsSimpleGroup H]
    (hab : ∃ a b : H, a * b ≠ b * a) :
    ∃ E : Subgroup H, (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ x ∈ E, x ^ 2 = 1) ∧
      Nat.card E = 4 := by
  obtain ⟨A, hc, hs, m, hm, hcard⟩ := exists_elemAb_big H hab
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd : 2 ^ 2 ∣ Nat.card A := hcard ▸ pow_dvd_pow 2 hm
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := A) 2 hd
  refine ⟨K.map A.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨k1, _, rfl⟩ _ ⟨k2, _, rfl⟩
    exact hc _ k1.2 _ k2.2
  · rintro _ ⟨k, _, rfl⟩
    exact hs _ k.2
  · rw [Subgroup.card_map_of_injective A.subtype_injective, hK]; norm_num

omit [MinimalNormalSimpleFactors.{0}] [TwoLePRankOfIsSimpleGroup.{0}] in
theorem isMulComm_of {G : Type*} [Group G] (E : Subgroup G) (h : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) :
    IsMulCommutative E := ⟨⟨fun a b => Subtype.ext (h a.1 a.2 b.1 b.2)⟩⟩

omit [MinimalNormalSimpleFactors.{0}] [TwoLePRankOfIsSimpleGroup.{0}] in
theorem comm_of_isMulComm {G : Type*} [Group G] (E : Subgroup G) [IsMulCommutative E] :
    ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
  congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨a, ha⟩ : E) ⟨b, hb⟩)

omit [MinimalNormalSimpleFactors.{0}] [TwoLePRankOfIsSimpleGroup.{0}] in
theorem sup_elem_bound (hG : SylowMetacyclic G) (F0 F1 : Subgroup G)
    (h0 : ∀ a ∈ F0, ∀ b ∈ F0, a * b = b * a) (h1 : ∀ a ∈ F1, ∀ b ∈ F1, a * b = b * a)
    (s0 : ∀ x ∈ F0, x ^ 2 = 1) (s1 : ∀ x ∈ F1, x ^ 2 = 1)
    (hx : ∀ a ∈ F0, ∀ b ∈ F1, a * b = b * a) : Nat.card (F0 ⊔ F1 : Subgroup G) ≤ 4 := by
  have c0 : F0 ≤ Subgroup.centralizer (F0 : Set G) := fun a ha b hb => (h0 b hb a ha)
  have c1 : F1 ≤ Subgroup.centralizer (F0 : Set G) := fun a ha b hb => (hx b hb a ha)
  have c1' : F1 ≤ Subgroup.centralizer (F1 : Set G) := fun a ha b hb => (h1 b hb a ha)
  have c0' : F0 ≤ Subgroup.centralizer (F1 : Set G) := fun a ha b hb => (hx a ha b hb).symm
  have t0 : (F0 ⊔ F1) ≤ Subgroup.centralizer (F0 : Set G) := sup_le c0 c1
  have t1 : (F0 ⊔ F1) ≤ Subgroup.centralizer (F1 : Set G) := sup_le c0' c1'
  have u0 : F0 ≤ Subgroup.centralizer ((F0 ⊔ F1 : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.mpr t0
  have u1 : F1 ≤ Subgroup.centralizer ((F0 ⊔ F1 : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.mpr t1
  have hT : (F0 ⊔ F1) ≤ Subgroup.centralizer ((F0 ⊔ F1 : Subgroup G) : Set G) := sup_le u0 u1
  have hcomm : ∀ a ∈ (F0 ⊔ F1 : Subgroup G), ∀ b ∈ (F0 ⊔ F1 : Subgroup G), a * b = b * a :=
    fun a ha b hb => (hT hb a ha)
  refine hG.card_le_four _ ?_
  intro x hxT
  rw [Subgroup.sup_eq_closure] at hxT
  induction hxT using Subgroup.closure_induction with
  | mem y hy =>
      rcases hy with hy | hy
      · exact s0 y hy
      · exact s1 y hy
  | one => simp
  | mul y z hy hz ihy ihz =>
      rw [Subgroup.sup_eq_closure] at hcomm
      have := hcomm y hy z hz
      rw [pow_two] at ihy ihz ⊢
      calc y * z * (y * z) = y * (z * y) * z := by group
        _ = y * (y * z) * z := by rw [this]
        _ = (y * y) * (z * z) := by group
        _ = 1 := by rw [ihy, ihz, one_mul]
  | inv y hy ihy =>
      rw [inv_pow, ihy, inv_one]


/-- A nonabelian minimal normal subgroup of a Sylow-metacyclic group is simple. -/
theorem simple_main (hG : SylowMetacyclic G) {N : Subgroup G} (hN : N.Normal)
    (hN1 : N ≠ ⊥) (hmin : ∀ M : Subgroup G, M.Normal → M ≤ N → M = ⊥ ∨ M = N)
    (hnab : ∃ a b : N, a * b ≠ b * a) : IsSimpleGroup N := by
  obtain ⟨r, S, hr, hSN, hSs, hconj, -, e, he⟩ := MinimalNormalSimpleFactors.minimal_normal_simple_factors hN hN1 hmin
  have hnabS : ∀ i, ∃ a b : S i, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    obtain ⟨i0, hi0⟩ := hcon
    have hall : ∀ j, ∀ a ∈ S j, ∀ b ∈ S j, a * b = b * a := by
      intro j a ha b hb
      obtain ⟨g, hg⟩ := hconj i0 j
      rw [hg] at ha hb
      obtain ⟨y1, hy1, rfl⟩ := Subgroup.mem_map.mp ha
      obtain ⟨y2, hy2, rfl⟩ := Subgroup.mem_map.mp hb
      rw [← map_mul, ← map_mul]
      congr 1
      exact congrArg Subtype.val (hi0 ⟨y1, hy1⟩ ⟨y2, hy2⟩)
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have hxy : e.symm a * e.symm b = e.symm b * e.symm a :=
      funext fun j => Subtype.ext (hall j _ (e.symm a j).2 _ (e.symm b j).2)
    have := congrArg e hxy
    simpa [map_mul] using this
  have cross : ∀ i j, i ≠ j → ∀ a ∈ S i, ∀ b ∈ S j, a * b = b * a := by
    intro i j hij a ha b hb
    have h1 := he i (Pi.mulSingle i (⟨a, ha⟩ : S i)) (fun k hk => Pi.mulSingle_eq_of_ne hk _)
    have h2 := he j (Pi.mulSingle j (⟨b, hb⟩ : S j)) (fun k hk => Pi.mulSingle_eq_of_ne hk _)
    have h3 := congrArg e (Pi.mulSingle_commute hij (⟨a, ha⟩ : S i) (⟨b, hb⟩ : S j) |>.eq)
    rw [map_mul, map_mul] at h3
    have h4 := congrArg Subtype.val h3
    simpa [h1, h2] using h4
  have inter : ∀ i j, i ≠ j → ∀ x ∈ S i, x ∈ S j → x = 1 := by
    intro i j hij x hi hj
    have h1 := he i (Pi.mulSingle i (⟨x, hi⟩ : S i)) (fun k hk => Pi.mulSingle_eq_of_ne hk _)
    have h2 := he j (Pi.mulSingle j (⟨x, hj⟩ : S j)) (fun k hk => Pi.mulSingle_eq_of_ne hk _)
    have h3 : e (Pi.mulSingle i (⟨x, hi⟩ : S i)) = e (Pi.mulSingle j (⟨x, hj⟩ : S j)) :=
      Subtype.ext (by simpa [h1, h2] )
    have h4 := e.injective h3
    have h5 := congrFun h4 i
    rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hij] at h5
    exact congrArg Subtype.val h5
  have hr1 : ¬ 2 ≤ r := by
    intro h2
    let i0 : Fin r := ⟨0, by omega⟩
    let i1 : Fin r := ⟨1, by omega⟩
    have hne : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
    have := hSs i0
    have := hSs i1
    obtain ⟨F0, c0, s0, k0⟩ := exists_elem4 (S i0) (hnabS i0)
    obtain ⟨F1, c1, s1, k1⟩ := exists_elem4 (S i1) (hnabS i1)
    have hF0 : ∀ x ∈ F0.map (S i0).subtype, x ∈ S i0 := by
      rintro _ ⟨k, _, rfl⟩; exact k.2
    have hF1 : ∀ x ∈ F1.map (S i1).subtype, x ∈ S i1 := by
      rintro _ ⟨k, _, rfl⟩; exact k.2
    have hb := sup_elem_bound hG (F0.map (S i0).subtype) (F1.map (S i1).subtype)
      (by rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
          have := c0 a ha b hb
          simpa using congrArg (S i0).subtype this)
      (by rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
          have := c1 a ha b hb
          simpa using congrArg (S i1).subtype this)
      (by rintro _ ⟨a, ha, rfl⟩
          rw [← map_pow, s0 a ha, map_one])
      (by rintro _ ⟨a, ha, rfl⟩
          rw [← map_pow, s1 a ha, map_one])
      (fun a ha b hb => cross i0 i1 hne a (hF0 a ha) b (hF1 b hb))
    have hle : F0.map (S i0).subtype ≤ F0.map (S i0).subtype ⊔ F1.map (S i1).subtype := le_sup_left
    have hcard0 : Nat.card (F0.map (S i0).subtype) = 4 := by
      rw [Subgroup.card_map_of_injective (S i0).subtype_injective, k0]
    have heq := Subgroup.eq_of_le_of_card_ge hle (by omega)
    have hF1le : F1.map (S i1).subtype ≤ F0.map (S i0).subtype := by
      rw [heq]; exact le_sup_right
    have hbot : F1.map (S i1).subtype = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      exact (Subgroup.mem_bot).mpr (inter i0 i1 hne x (hF0 x (hF1le hx)) (hF1 x hx))
    have : Nat.card (F1.map (S i1).subtype) = 4 := by
      rw [Subgroup.card_map_of_injective (S i1).subtype_injective, k1]
    rw [hbot] at this
    simp at this
  obtain rfl : r = 1 := by omega
  have := hSs default
  exact MulEquiv.isSimpleGroup (e.symm.trans (MulEquiv.piUnique (fun i : Fin 1 => (S i : Type))))


end A

end CFSGOutside.ChillagSonn
