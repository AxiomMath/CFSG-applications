import CFSGOutside.ChillagSonn.Theorem1Case1
import CFSGOutside.ChillagSonn.Lemma16B
import CFSGOutside.ChillagSonn.Fact5

/-!
# Theorem 1 of Chillag–Sonn when `G/S(G)` is not simple

By Lemma (1.6), `X = G/S(G)` is `PGL(2, pⁿ)` or `PGL*(2, p²)`, with a simple subgroup `Y ≅ PSL(2, pⁿ)` of index 2,
and by Lemma (1.10) `O(G)` has a complement `A`. Applying Case 1 to the preimage of `Y` gives `|S(G) : O(G)| ≤ 2`, so
`D = A ∩ S(G)` has order at most 2 and is central in `A`, and `A/D ≅ X`.

* `D ≤ A'`: otherwise `A' ∩ D = 1`, `A'` maps isomorphically onto `X' = Y`, and a Klein four-group of `Y` lifted to
  `A'` together with `D` is elementary abelian of order 8 in `A`.
* So `A` is `X` or a stem extension of `X` by a group of order 2; for `X = PGL*(2, p²)` the latter is impossible
  (fact 5). Hence `A` is in the list `PGL(2, pⁿ)`, `PGL(2, pⁿ)^±`, `PGL*(2, p²)`.
* `A₀ = A'` is the preimage of `Y`, of index 2, quasisimple with center `D`, and `C_A(A₀) ≤ A₀` because
  `C_X(Y) = 1`. Lemma (1.9) then gives `|A : C_A(O(G))| ≤ 2`, and the Sylow statements follow.
-/

namespace CFSGOutside.ChillagSonn

open CFSGOutside.Corpus CFSGOutside.Corpus.Open CFSGOutside.Corpus.RankThree.PerfectCover
  CFSGOutside.Corpus.GorensteinWalter

section Radical

variable [CardKerDvdHopfMultiplier] [PslTwoHopfMultiplier] [HopfMultiplierAlternating]
  [CardHopfMultiplierEqCardGriess] [FieldNineAlternatingSix.{0}] [HopfMultiplierM11]
  [MinimalNormalSimpleFactors.{0}] [TwoLePRankOfIsSimpleGroup.{0}] [LrRankTwoIsomorphismTypes]
  [CardStatedProjStatedSL] [CardPsuThreeMulGcd] [FrattiniElementaryQuotient.{0}]
  [FrattiniAutomorphismKernel.{0}] [HopfCentralCoverConsequences] [FrobeniusNormalPComplement.{0}]

/-- `|S(G)| ≤ 2 |O(G)|` if `G/S(G)` has a nonabelian simple subgroup of index 2: Case 1 applied to its preimage. -/
theorem card_solvableRadical_le {G : Type} [Group G] [Finite G] (hG : SylowMetacyclic G)
    (hY : HasSimpleIndexTwo (G ⧸ solvableRadical G)) :
    Nat.card (solvableRadical G) ≤ 2 * Nat.card (oddCore G) := by
  classical
  set S := solvableRadical G with hSdef
  have hSs : Group.IsSolvable S := isSolvable_solvableRadical
  have hOS : oddCore G ≤ S := le_solvableRadical inferInstance
    (isSolvable_of_odd_of_sylowMetacyclic (hG.subgroup _) odd_card_oddCore)
  obtain ⟨Y, hYn, hYi, hYs, hYnab⟩ := hY
  set G₁ := Y.comap (QuotientGroup.mk' S) with hG₁def
  have hSG₁ : S ≤ G₁ := fun x hx => by
    rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx]; exact one_mem _
  set f := (QuotientGroup.mk' S).subgroupComap Y
  have hf : Function.Surjective f := MonoidHom.subgroupComap_surjective _ _ (QuotientGroup.mk'_surjective S)
  have hker : f.ker = S.subgroupOf G₁ := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← QuotientGroup.eq_one_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  let e₁ : G₁ ⧸ S.subgroupOf G₁ ≃* Y :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have := hYs
  have : IsSimpleGroup (G₁ ⧸ S.subgroupOf G₁) := e₁.isSimpleGroup
  have hnab₁ : ∃ a b : G₁ ⧸ S.subgroupOf G₁, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hYnab
    exact ⟨e₁.symm a, e₁.symm b, fun h => hab (by simpa using congrArg e₁ h)⟩
  have hrad₁ : solvableRadical G₁ = S.subgroupOf G₁ :=
    solvableRadical_eq_of _ (isSolvable_subgroupOf hSs G₁) hnab₁
  have hns₁ : ¬ Group.IsSolvable G₁ := fun h => by
    have := h
    obtain ⟨a, b, hab⟩ := hYnab
    exact hab (comm_of_isSimpleGroup_of_isSolvable (Group.isSolvable_of_surjective hf) a b)
  obtain ⟨A₁, h1, h2, -, -, hZ, ⟨eZ⟩⟩ := case1_split (hG.subgroup G₁) hns₁
    (QuotientGroup.quotientMulEquivOfEq hrad₁).isSimpleGroup
  have hO₁ : oddCore G₁ = (oddCore G).subgroupOf G₁ :=
    oddCore_eq_subgroupOf odd_card_oddCore (hOS.trans hSG₁)
      (le_oddCore (normal_map_subtype_of_characteristic _)
        (by rw [Subgroup.card_map_of_injective G₁.subtype_injective]; exact odd_card_oddCore))
  have c1 := card_sup_of_normal A₁ (oddCore G₁) (by rw [inf_comm]; exact h1)
  rw [sup_comm, h2, Subgroup.card_top] at c1
  have c2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center A₁)
  have c3 := Subgroup.card_eq_card_quotient_mul_card_subgroup (solvableRadical G₁)
  rw [Nat.card_congr eZ.toEquiv] at c2
  have c5 : Nat.card (solvableRadical G₁) = Nat.card S := by
    rw [hrad₁]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSG₁).toEquiv
  have c6 : Nat.card (oddCore G₁) = Nat.card (oddCore G) := by
    rw [hO₁]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hOS.trans hSG₁)).toEquiv
  rw [c2, c6] at c1
  rw [c5, c1] at c3
  have hpos : 0 < Nat.card (G₁ ⧸ solvableRadical G₁) := Nat.card_pos
  have h3 : Nat.card S = Nat.card (Subgroup.center A₁) * Nat.card (oddCore G) := by
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    rw [← c3]; ring
  rw [h3]
  exact Nat.mul_le_mul_right _ hZ

end Radical

variable [CardKerDvdHopfMultiplier] [PslTwoHopfMultiplier] [HopfMultiplierAlternating]
  [CardHopfMultiplierEqCardGriess] [FieldNineAlternatingSix.{0}] [HopfMultiplierM11]
  [MinimalNormalSimpleFactors.{0}] [TwoLePRankOfIsSimpleGroup.{0}] [LrRankTwoIsomorphismTypes]
  [CardStatedProjStatedSL] [CardPsuThreeMulGcd] [FrattiniElementaryQuotient.{0}]
  [FrattiniAutomorphismKernel.{0}] [HopfCentralCoverConsequences] [FrobeniusNormalPComplement.{0}]
  [DicksonPsl2SubgroupClassification.{0}] [Gaschutz.{0}] [SemilinearEquivAut.{0}] [AutAlternatingBijectiveConj]
  [M11AutInner]

/-- **Theorem 1, `G/S(G)` not simple.** -/
theorem theorem_1_case2 {G : Type} [Group G] [Finite G] (hG : SylowMetacyclic G) (hns : ¬ Group.IsSolvable G)
    (hnot : ¬ IsSimpleGroup (G ⧸ solvableRadical G)) : Theorem1Conclusion G := by
  classical
  obtain ⟨F, _, _, p, n, hp, hn, hF, h5, hiso, Y, hYn, hYi, hYs, hYnab, ⟨eY⟩⟩ :=
    lemma_1_6_nonsimple hG hns hnot
  set S := solvableRadical G with hSdef
  have := hYn
  have := hYs
  have hY : HasSimpleIndexTwo (G ⧸ S) := ⟨Y, hYn, hYi, hYs, hYnab⟩
  obtain ⟨A, hinf, hsup⟩ := lemma_1_10 hG hns hY
  have hodd : Odd (Nat.card (oddCore G)) := odd_card_oddCore
  have hOS : oddCore G ≤ S := le_solvableRadical inferInstance
    (isSolvable_of_odd_of_sylowMetacyclic (hG.subgroup _) hodd)
  have hSA : S ⊔ A = ⊤ := eq_top_iff.2 (hsup ▸ sup_le_sup_right hOS A)
  obtain ⟨e⟩ := nonempty_quotient_subgroupOf_equiv hSA
  set D : Subgroup A := S.subgroupOf A with hDdef
  have : D.Normal := Subgroup.normal_subgroupOf
  -- `|D| ≤ 2`
  have hDcard : Nat.card D ≤ 2 := by
    have c1 := card_sup_of_normal A (oddCore G) (by rw [inf_comm]; exact hinf)
    rw [sup_comm, hsup, Subgroup.card_top] at c1
    have c2 := Subgroup.card_eq_card_quotient_mul_card_subgroup S
    have c3 := Subgroup.card_eq_card_quotient_mul_card_subgroup D
    rw [Nat.card_congr e.toEquiv] at c3
    have c4 := card_solvableRadical_le hG hY
    have hXpos : 0 < Nat.card (G ⧸ S) := Nat.card_pos
    have hOpos : 0 < Nat.card (oddCore G) := Nat.card_pos
    have h1 : Nat.card S = Nat.card D * Nat.card (oddCore G) := by
      refine Nat.eq_of_mul_eq_mul_left hXpos ?_
      rw [← c2, c1, c3]; ring
    rw [h1] at c4
    exact Nat.le_of_mul_le_mul_right c4 hOpos
  have hDc : D ≤ Subgroup.center A := le_center_of_card_le_two D hDcard
  set ψ : A →* G ⧸ S := e.toMonoidHom.comp (QuotientGroup.mk' D) with hψdef
  have hψ : Function.Surjective ψ := e.surjective.comp (QuotientGroup.mk'_surjective D)
  have hψker : ψ.ker = D := ker_comp_mk D e
  have hXrad : ∀ M : Subgroup (G ⧸ S), M.Normal → Group.IsSolvable M → M = ⊥ :=
    fun M hM hs => eq_bot_of_normal_solvable_quotient M hM hs
  -- `X' = Y`
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcY : IsCyclic ((G ⧸ S) ⧸ Y) := isCyclic_of_prime_card (p := 2) hYi
  have hYX : Y ≤ commutator (G ⧸ S) := by
    have h1 : (commutator Y).map Y.subtype = Y := by
      rw [commutator_eq_top_of_simple hYnab, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [← h1, Subgroup.map_subtype_commutator, commutator_def]
    exact Subgroup.commutator_mono le_top le_top
  have hXY : commutator (G ⧸ S) ≤ Y :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp ⟨⟨mul_comm_of_isCyclic hcY⟩⟩
  have hψA' : (commutator A).map ψ = commutator (G ⧸ S) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator, Subgroup.map_top, MonoidHom.range_eq_top.mpr hψ]
  -- `D ≤ A'`
  have hDA' : D ≤ commutator A := by
    by_contra hDA
    have hD2 : Nat.card D = 2 := by
      have h1 : Nat.card D ≠ 1 := fun h => hDA (by rw [Subgroup.eq_bot_of_card_eq D h]; exact bot_le)
      have := Nat.card_pos (α := D)
      omega
    have hbot : D ⊓ commutator A = ⊥ := by
      have hdvd := Subgroup.card_dvd_of_le (inf_le_left : D ⊓ commutator A ≤ D)
      rw [hD2, Nat.dvd_prime Nat.prime_two] at hdvd
      rcases hdvd with h1 | h2
      · exact Subgroup.eq_bot_of_card_eq _ h1
      · exact absurd ((Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h2, hD2])).symm.le.trans inf_le_right)
          hDA
    obtain ⟨E, -, hEs, hE4⟩ := exists_elem4 Y hYnab
    set E' : Subgroup A := (E.map Y.subtype).comap ψ ⊓ commutator A with hE'def
    have hEsq : ∀ x ∈ E', x ^ 2 = 1 := by
      intro x hx
      have h1 : ψ (x ^ 2) = 1 := by
        obtain ⟨y, hy, hyx⟩ := hx.1
        rw [map_pow, ← hyx, ← map_pow, hEs y hy, map_one]
      have : x ^ 2 ∈ D ⊓ commutator A := ⟨hψker ▸ h1, pow_mem hx.2 2⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    have hED : E' ⊓ D = ⊥ := eq_bot_iff.2 fun x hx => hbot ▸ ⟨hx.2, hx.1.2⟩
    have hEmap : E'.map ψ = E.map Y.subtype := by
      refine le_antisymm (Subgroup.map_le_iff_le_comap.2 inf_le_left) fun y hy => ?_
      have : y ∈ (commutator A).map ψ := hψA' ▸ hYX (Subgroup.map_subtype_le E hy)
      obtain ⟨a, ha, rfl⟩ := this
      exact ⟨a, ⟨hy, ha⟩, rfl⟩
    have hE4' : 4 ∣ Nat.card E' := by
      have := Subgroup.card_map_dvd (H := E') ψ
      rwa [hEmap, Subgroup.card_map_of_injective Y.subtype_injective, hE4] at this
    have hcardED : Nat.card (E' ⊔ D : Subgroup A) = Nat.card E' * 2 := by
      rw [card_sup_of_normal E' D hED, hD2]
    have hsq : ∀ x ∈ (E' ⊔ D : Subgroup A), x ^ 2 = 1 := by
      intro x hx
      obtain ⟨a, ha, d, hd, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
      have hdc : Commute a d := (Subgroup.mem_center_iff.mp (hDc hd) a)
      have hd2 : d ^ 2 = 1 := by
        have := pow_card_eq_one' (G := D) (x := ⟨d, hd⟩)
        rw [hD2] at this
        exact congrArg Subtype.val this
      rw [hdc.mul_pow, hEsq a ha, hd2, one_mul]
    have h4 := (hG.subgroup A).card_le_four _ hsq
    rw [hcardED] at h4
    obtain ⟨k, hk⟩ := hE4'
    have : 0 < Nat.card E' := Nat.card_pos
    omega
  -- `A₀ = ψ⁻¹(Y)`
  set A₀ : Subgroup A := Y.comap ψ with hA₀def
  have : A₀.Normal := hYn.comap ψ
  have hidx : A₀.index = 2 := by rw [hA₀def, Subgroup.index_comap_of_surjective (H := Y) hψ, hYi]
  have hDA₀ : D ≤ A₀ := fun d hd => by
    have h1 : ψ d = 1 := by rw [← MonoidHom.mem_ker, hψker]; exact hd
    show ψ d ∈ Y
    rw [h1]
    exact one_mem _
  set θ : A₀ →* Y := ψ.subgroupComap Y
  have hθ : Function.Surjective θ := MonoidHom.subgroupComap_surjective _ _ hψ
  have hθker : θ.ker = D.subgroupOf A₀ := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hψker, MonoidHom.mem_ker]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hperf₀ : commutator A₀ = ⊤ := by
    by_cases hD1 : Nat.card D = 1
    · have hθinj : Function.Injective θ := by
        rw [← MonoidHom.ker_eq_bot_iff, hθker, Subgroup.eq_bot_of_card_eq D hD1]
        exact Subgroup.bot_subgroupOf _
      apply Subgroup.map_injective hθinj
      rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, MonoidHom.range_eq_top.mpr hθ, ← commutator_def,
        commutator_eq_top_of_simple hYnab]
    · exact commutator_eq_top_of_stem hYnab D hDA' (by have := Nat.card_pos (α := D); omega) A₀ hidx θ hθ hθker
        hDA₀
  -- `A' = A₀`
  have hA'A₀ : commutator A = A₀ := by
    refine le_antisymm (Subgroup.map_le_iff_le_comap.mp (hψA'.le.trans hXY)) ?_
    have h1 : (commutator A₀).map A₀.subtype = A₀ := by
      rw [hperf₀, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [← h1, Subgroup.map_subtype_commutator, commutator_def]
    exact Subgroup.commutator_mono le_top le_top
  -- `A₀` is quasisimple with center `D`
  set D₀ : Subgroup A₀ := D.subgroupOf A₀
  have : D₀.Normal := Subgroup.normal_subgroupOf
  have hD₀c : D₀ ≤ Subgroup.center A₀ := fun d hd => Subgroup.mem_center_iff.mpr fun a =>
    Subtype.ext (Subgroup.mem_center_iff.mp (hDc (Subgroup.mem_subgroupOf.mp hd)) a)
  let e₀ : A₀ ⧸ D₀ ≃* Y :=
    (QuotientGroup.quotientMulEquivOfEq hθker.symm).trans (QuotientGroup.quotientKerEquivOfSurjective θ hθ)
  have hq₀ : IsQuasisimple A₀ := isQuasisimple_of_central hperf₀ D₀ hD₀c e₀ hYnab
  have hZ₀ : Nat.card (Subgroup.center A₀) ≤ 2 := by
    rw [center_eq_of_simple_quotient D₀ hD₀c e₀ hYnab,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDA₀).toEquiv]
    exact hDcard
  -- `C_X(Y) = 1` and `C_A(A₀) ≤ A₀`
  have hZY : Subgroup.center Y = ⊥ := by
    rcases (Subgroup.center Y).normal_of_characteristic.eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hYnab
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
  have hCX : Subgroup.centralizer (Y : Set (G ⧸ S)) = ⊥ := by
    refine hXrad _ inferInstance ?_
    let f : Subgroup.centralizer (Y : Set (G ⧸ S)) →* (G ⧸ S) ⧸ Y :=
      (QuotientGroup.mk' Y).comp (Subgroup.centralizer (Y : Set (G ⧸ S))).subtype
    have hfinj : Function.Injective f := by
      rw [injective_iff_map_eq_one]
      intro c hc
      have hcY : (c : G ⧸ S) ∈ Y := (QuotientGroup.eq_one_iff _).mp hc
      have hz : (⟨c, hcY⟩ : Y) ∈ Subgroup.center Y := Subgroup.mem_center_iff.mpr fun y =>
        Subtype.ext (Subgroup.mem_centralizer_iff.mp c.2 y y.2)
      rw [hZY, Subgroup.mem_bot] at hz
      have h2 : (c : G ⧸ S) = 1 := congrArg Subtype.val hz
      exact Subtype.ext h2
    have : Group.IsSolvable ((G ⧸ S) ⧸ Y) := Group.isSolvable_of_comm (mul_comm_of_isCyclic hcY)
    exact Group.isSolvable_of_isSolvable_injective hfinj
  have hCA : Subgroup.centralizer (A₀ : Set A) ≤ A₀ := by
    intro c hc
    have : ψ c ∈ Subgroup.centralizer (Y : Set (G ⧸ S)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨a, ha⟩ := hθ ⟨y, hy⟩
      have hay : ψ a = y := congrArg Subtype.val ha
      rw [← hay, ← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hc a a.2]
    rw [hCX, Subgroup.mem_bot, ← MonoidHom.mem_ker, hψker] at this
    exact hDA₀ this
  -- Lemma (1.9): `A₀` centralizes `O(G)`
  have hcent := le_centralizer_aux hG A A₀ hq₀ hZ₀ hidx.le hCA _ (oddCore G) rfl inferInstance hinf hodd
    (fun htop => by rw [htop, Subgroup.index_top] at hidx; exact absurd hidx (by norm_num))
  have hrel : (Subgroup.centralizer (oddCore G : Set G)).relIndex A ≤ 2 := by
    have hle : A₀ ≤ (Subgroup.centralizer (oddCore G : Set G)).subgroupOf A := fun a ha =>
      Subgroup.mem_subgroupOf.mpr (hcent a ha)
    have := Subgroup.index_dvd_of_le hle
    rw [hidx] at this
    exact Nat.le_of_dvd (by norm_num) this
  -- `A` is in the list
  have hp2 : p ≠ 2 := by rintro rfl; rcases hn with rfl | rfl <;> norm_num at h5
  have hPGL : PGLList A := by
    by_cases hD1 : Nat.card D = 1
    · have hDbot : D = ⊥ := Subgroup.eq_bot_of_card_eq D hD1
      let eA : A ≃* G ⧸ S :=
        QuotientGroup.quotientBot.symm.trans ((QuotientGroup.quotientMulEquivOfEq hDbot.symm).trans e)
      rcases hiso with ⟨⟨eX⟩⟩ | ⟨hn2, ⟨eX⟩⟩
      · exact ⟨F, inferInstance, inferInstance, p, n, hp, hn, hF, h5, Or.inl ⟨eA.trans eX⟩⟩
      · exact ⟨F, inferInstance, inferInstance, p, n, hp, hn, hF, h5, Or.inr (Or.inr ⟨hn2, ⟨eA.trans eX⟩⟩)⟩
    · have hD2 : Nat.card D = 2 := by have := Nat.card_pos (α := D); omega
      rcases hiso with ⟨⟨eX⟩⟩ | ⟨hn2, ⟨eX⟩⟩
      · exact ⟨F, inferInstance, inferInstance, p, n, hp, hn, hF, h5,
          Or.inr (Or.inl ⟨D, inferInstance, le_inf hDc hDA', hD2, ⟨e.trans eX⟩⟩)⟩
      · exfalso
        subst hn2
        have : IsSimpleGroup (PSL2 F) := eY.symm.isSimpleGroup
        have hnab' : ∃ a b : PSL2 F, a * b ≠ b * a := by
          obtain ⟨a, b, hab⟩ := hYnab
          exact ⟨eY a, eY b, fun h => hab (eY.injective (by simpa using h))⟩
        exact not_isDoubleStemCover_pglStar hp hp2 hF hnab' ⟨D, inferInstance, le_inf hDc hDA', hD2, ⟨e.trans eX⟩⟩
  refine ⟨oddCore G, A, inferInstance, hinf, hsup, hodd, hasSylowTower_of_odd (hG.subgroup _) hodd,
    Or.inr ⟨rfl, fun q hq hqA hqN _ => ?_, Or.inr ⟨hPGL, by rw [hA'A₀, hidx], hrel⟩⟩⟩
  have hq2 : q ≠ 2 := fun h => by
    rw [h] at hqN
    exact Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr hqN)
  refine sylow_claims hG (oddCore G) A hinf hsup hodd hqA hqN ⊥ (by rw [Subgroup.card_bot]; exact hq.not_dvd_one)
    fun a ha hk x hx => ?_
  have hac : a ∈ Subgroup.centralizer (oddCore G : Set G) := mem_of_relIndex_le_two hrel hq2 ha hk
  have h := Subgroup.mem_centralizer_iff.mp hac x hx
  rw [Subgroup.mem_bot]
  calc a * x * a⁻¹ * x⁻¹ = (x * a) * a⁻¹ * x⁻¹ := by rw [h]
    _ = 1 := by group

end CFSGOutside.ChillagSonn
