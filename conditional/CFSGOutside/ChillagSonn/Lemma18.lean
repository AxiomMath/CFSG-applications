import CFSGOutside.ChillagSonn.Lemma16
import CFSGOutside.ChillagSonn.Lemma17
import CFSGOutside.ChillagSonn.SmallActions
import CFSGOutside.ChillagSonn.Covers

/-!
# Lemma (1.8): `G` almost splits over `S(G)` when `G/S(G)` is simple

If `G` is a nonsolvable Sylow-metacyclic group with `G/S(G)` simple, then `G = S(G) A` with `|S(G) ∩ A| ≤ 2`.

The proof is the paper's minimal-counterexample argument (Steps 1–4). In Step 2 the Schur multipliers of the groups
of Lemma (1.5) are corpus inputs and Lemma (1.7) excludes kernels of order 3 and 6. Step 4 differs from the paper:
* if `|S|` is even, `S` is a metacyclic 2-group normal in the perfect group `G`, hence central
  (`le_center_of_perfect`), contradicting Step 2;
* if `|S|` is odd, `S` is elementary abelian of order `r` or `r²` with `C_G(S) = S`, so the simple group `G/S` acts
  faithfully on `S`; for `|S| = r` its automorphism group is abelian, and for `|S| = r²` a Klein four-subgroup of
  `G/S` would contain the (central) inversion map (`exists_inversion_of_klein`). This replaces the paper's use of the
  Schur–Zassenhaus theorem and of Huppert's theorem [Huppert IV.8.6].
-/

namespace CFSGOutside.ChillagSonn

open CFSGOutside.Corpus CFSGOutside.Corpus.Open CFSGOutside.Corpus.RankThree.PerfectCover
  CFSGOutside.Corpus.GorensteinWalter
open scoped commutatorElement

section Basics

/-- An abelian group of order 6 is cyclic. -/
theorem isCyclic_of_comm_of_card_six {Z : Type} [Group Z] [Finite Z] (hc : ∀ a b : Z, a * b = b * a)
    (h6 : Nat.card Z = 6) : IsCyclic Z := by
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := Z) 2 (by rw [h6]; norm_num)
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := Z) 3 (by rw [h6]; norm_num)
  have hab : orderOf (a * b) = 6 := by
    rw [(Commute.orderOf_mul_eq_mul_orderOf_of_coprime (hc a b) (by rw [ha, hb]; norm_num)), ha, hb]
  exact isCyclic_of_orderOf_eq_card (a * b) (by rw [hab, h6])

/-- A solvable group which is simple is commutative. -/
theorem comm_of_isSimpleGroup_of_isSolvable {X : Type} [Group X] [IsSimpleGroup X] (hs : Group.IsSolvable X) :
    ∀ a b : X, a * b = b * a := by
  have h := IsSimpleGroup.comm_iff_isSolvable.mpr hs
  exact fun a b => h a b

variable {G : Type} [Group G] [Finite G]

/-- If `M ⊴ H` is solvable and `H/M` is a nonabelian simple group, then `M` is the soluble radical of `H`. -/
theorem solvableRadical_eq_of {H : Type} [Group H] [Finite H] (M : Subgroup H) [M.Normal]
    (hM : Group.IsSolvable M) [IsSimpleGroup (H ⧸ M)] (hnab : ∃ a b : H ⧸ M, a * b ≠ b * a) :
    solvableRadical H = M := by
  refine le_antisymm ?_ (le_solvableRadical inferInstance hM)
  have : Group.IsSolvable (solvableRadical H) := isSolvable_solvableRadical
  set T := (solvableRadical H).map (QuotientGroup.mk' M)
  have hT : T.Normal := (solvableRadical_normal).map _ (QuotientGroup.mk'_surjective M)
  have hTs : Group.IsSolvable T :=
    Group.isSolvable_of_surjective (f := (QuotientGroup.mk' M).subgroupMap (solvableRadical H))
      (MonoidHom.subgroupMap_surjective _ _)
  rcases hT.eq_bot_or_eq_top with h | h
  · intro x hx
    have : QuotientGroup.mk' M x ∈ T := ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff x).mp this
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have hs : Group.IsSolvable (H ⧸ M) := by
      rw [h] at hTs
      exact Group.isSolvable_of_isSolvable_injective (f := (Subgroup.topEquiv (G := H ⧸ M)).symm.toMonoidHom)
        (MulEquiv.injective _)
    exact hab (comm_of_isSimpleGroup_of_isSolvable hs a b)

/-- If `S ⊴ G` is solvable and `S ⊔ B = ⊤` with `B` solvable, then `G` is solvable. -/
theorem isSolvable_of_sup {S B : Subgroup G} [S.Normal] (hS : Group.IsSolvable S) (hB : Group.IsSolvable B)
    (h : S ⊔ B = ⊤) : Group.IsSolvable G := by
  have hsurj : Function.Surjective ((QuotientGroup.mk' S).comp B.subtype) := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective S y
    obtain ⟨s, hs, b, hb, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp (h ▸ Subgroup.mem_top g)
    refine ⟨⟨b, hb⟩, ?_⟩
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq]
    simpa [mul_assoc] using (inferInstance : S.Normal).conj_mem s hs b⁻¹
  have : Group.IsSolvable (G ⧸ S) := Group.isSolvable_of_surjective hsurj
  exact Group.isSolvable_of_ker_le_range S.subtype (QuotientGroup.mk' S)
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

variable [CardKerDvdHopfMultiplier] [PslTwoHopfMultiplier] [HopfMultiplierAlternating]
  [CardHopfMultiplierEqCardGriess] [FieldNineAlternatingSix.{0}] [HopfMultiplierM11]

/-- Step 2 of Lemma (1.8): a central subgroup `Z` of a perfect Sylow-metacyclic group with `G/Z` in the list of
Lemma (1.5) has order at most 2 (Schur multipliers, and Lemma (1.7) for kernels of order 3 or 6). -/
theorem card_le_two_of_central {X : Type} [Group X] (hG : SylowMetacyclic G) (hperf : commutator G = ⊤)
    (Z : Subgroup G) [Z.Normal] (hZ : Z ≤ Subgroup.center G) (e : G ⧸ Z ≃* X) (hX : Lemma15Conclusion X) :
    Nat.card Z ≤ 2 := by
  have hdvd : ∀ {E : Type} [Group E] (f : X ≃* E), Nat.card Z ∣ Nat.card (griessHopfMultiplier E) := by
    intro E _ f
    have := CardKerDvdHopfMultiplier.card_ker_dvd_hopfMultiplier hperf
      ((e.trans f).toMonoidHom.comp (QuotientGroup.mk' Z))
      ((e.trans f).surjective.comp (QuotientGroup.mk'_surjective Z)) (by rw [ker_comp_mk]; exact hZ)
    rwa [ker_comp_mk] at this
  have hcomm : ∀ a b : Z, a * b = b * a := fun a b =>
    Subtype.ext (Subgroup.mem_center_iff.mp (hZ b.2) a)
  -- kernels of order dividing 6 over `A₇` or `PSL(2, 9)`
  have key : Nat.card Z ∣ 6 → ∀ {F : Type} [Field F] [Finite F], Nat.card F = 9 →
      (Nonempty (G ⧸ Z ≃* PSL2 F) ∨ Nonempty (G ⧸ Z ≃* PGL2 F) ∨ Nonempty (G ⧸ Z ≃* PGLStar F) ∨
        Nonempty (G ⧸ Z ≃* alternatingGroup (Fin 7))) → Nat.card Z ≤ 2 := by
    intro h6 F _ _ hF9 hiso
    by_contra hlt
    push Not at hlt
    have h36 : Nat.card Z = 3 ∨ Nat.card Z = 6 := by
      have := Nat.le_of_dvd (by norm_num) h6
      interval_cases h : Nat.card Z <;> first | omega | (exfalso; revert h6; decide)
    have hcyc : IsCyclic Z := by
      rcases h36 with h3 | h6'
      · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        exact isCyclic_of_prime_card h3
      · exact isCyclic_of_comm_of_card_six hcomm h6'
    exact lemma_1_7 Z hcyc h36 hF9 hiso hG
  have hF9 : Nat.card (GaloisField 3 2) = 9 := by
    rw [GaloisField.card 3 2 (by norm_num)]; norm_num
  rcases hX with ⟨⟨eX⟩⟩ | ⟨⟨eX⟩⟩ | ⟨F, _, _, p, n, hp, hn, hF, h5, ⟨eX⟩⟩
  · have h := hdvd eX
    rw [← CardHopfMultiplierEqCardGriess.card_hopfMultiplier_eq_card_griessHopfMultiplier,
      HopfMultiplierAlternating.hopfMultiplier_alternatingGroup_seven.2] at h
    exact key h hF9 (Or.inr (Or.inr (Or.inr ⟨e.trans eX⟩)))
  · have h := hdvd (E := Blueprint.NativeSporadic.M11) eX
    rw [← CardHopfMultiplierEqCardGriess.card_hopfMultiplier_eq_card_griessHopfMultiplier,
      HopfMultiplierM11.nativeRow_M11] at h
    have := Nat.le_of_dvd one_pos h
    omega
  · have := Fintype.ofFinite F
    by_cases h9 : Nat.card F = 9
    · obtain ⟨ψ⟩ := FieldNineAlternatingSix.unique_field_nine_projective_linear_alternating_six_isomorphism
        F (by rw [Fintype.card_eq_nat_card, h9])
      have h := hdvd (eX.trans ψ)
      rw [← CardHopfMultiplierEqCardGriess.card_hopfMultiplier_eq_card_griessHopfMultiplier,
        HopfMultiplierAlternating.hopfMultiplier_alternatingGroup_six.2] at h
      exact key h h9 (Or.inl ⟨e.trans eX⟩)
    · obtain ⟨-, ⟨eM⟩⟩ := PslTwoHopfMultiplier.psl_two_hopfMultiplier (k := F)
        (by rw [Fintype.card_eq_nat_card]; omega) (by rw [Fintype.card_eq_nat_card]; exact h9)
      have h := hdvd eX
      rw [Nat.card_congr eM.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod] at h
      exact (Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ (by norm_num)) h).trans (Nat.gcd_le_left _ (by norm_num))

end Basics

section Helpers

variable {G : Type} [Group G] [Finite G]

/-- If `S ⊔ B = ⊤` with `S` normal, then `B / (B ∩ S) ≅ G/S`. -/
theorem nonempty_quotient_subgroupOf_equiv {S B : Subgroup G} [S.Normal] (h : S ⊔ B = ⊤) :
    Nonempty (B ⧸ S.subgroupOf B ≃* G ⧸ S) := by
  set φ : B →* G ⧸ S := (QuotientGroup.mk' S).comp B.subtype
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective S y
    obtain ⟨s, hs, b, hb, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp (h ▸ Subgroup.mem_top g)
    refine ⟨⟨b, hb⟩, ?_⟩
    simp only [φ, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq]
    simpa [mul_assoc] using (inferInstance : S.Normal).conj_mem s hs b⁻¹
  have hker : φ.ker = S.subgroupOf B := by
    ext x
    simp [φ, MonoidHom.mem_ker, Subgroup.mem_subgroupOf, QuotientGroup.eq_one_iff]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hsurj)⟩

/-- A subgroup containing a normal `S` whose image in `G/S` is everything is `⊤`. -/
theorem sup_eq_top_of_map_eq_top {S N : Subgroup G} [S.Normal] (h : N.map (QuotientGroup.mk' S) = ⊤) :
    S ⊔ N = ⊤ := by
  rw [eq_top_iff]
  intro g _
  obtain ⟨c, hc, hcg⟩ := (h ▸ Subgroup.mem_top (QuotientGroup.mk' S g) : QuotientGroup.mk' S g ∈ N.map _)
  have : c⁻¹ * g ∈ S := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hcg
    exact hcg
  have hg : g = (c * (c⁻¹ * g) * c⁻¹) * c := by group
  rw [hg]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ((inferInstance : S.Normal).conj_mem _ this c))
    (Subgroup.mem_sup_right hc)

/-- If `G/G'` and `G'` are solvable, so is `G`. -/
theorem isSolvable_of_commutator (h : Group.IsSolvable (commutator G)) : Group.IsSolvable G := by
  have : Group.IsSolvable (G ⧸ commutator G) := Group.isSolvable_of_comm fun a b => by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have : (a * b)⁻¹ * (b * a) = ⁅b⁻¹, a⁻¹⁆ := by simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  exact Group.isSolvable_of_ker_le_range (commutator G).subtype (QuotientGroup.mk' (commutator G))
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

/-- The inversion map is central in `Aut(S)` for `S` abelian. -/
theorem commute_of_inversion {S : Type} [Group S] {ι σ : MulAut S} (hι : ∀ x, ι x = x⁻¹) :
    σ * ι = ι * σ := by
  ext x
  simp [MulAut.mul_apply, hι, map_inv]

end Helpers

variable [CardKerDvdHopfMultiplier] [PslTwoHopfMultiplier] [HopfMultiplierAlternating]
  [CardHopfMultiplierEqCardGriess] [FieldNineAlternatingSix.{0}] [HopfMultiplierM11]
  [MinimalNormalSimpleFactors.{0}] [TwoLePRankOfIsSimpleGroup.{0}] [LrRankTwoIsomorphismTypes]
  [CardStatedProjStatedSL] [CardPsuThreeMulGcd] [FrattiniElementaryQuotient.{0}] [FrattiniAutomorphismKernel.{0}]

/-- Lemma (1.8), by strong induction on the order. -/
theorem lemma_1_8_aux (n : ℕ) : ∀ (G : Type) [Group G] [Finite G], Nat.card G = n → SylowMetacyclic G →
    ¬ Group.IsSolvable G → IsSimpleGroup (G ⧸ solvableRadical G) →
    ∃ A : Subgroup G, solvableRadical G ⊔ A = ⊤ ∧ Nat.card (solvableRadical G ⊓ A : Subgroup G) ≤ 2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ _ hn hG hns hsimp
  classical
  set S := solvableRadical G with hSdef
  have hSs : Group.IsSolvable S := isSolvable_solvableRadical
  by_contra hcon
  push Not at hcon
  have hXnab : ∃ a b : G ⧸ S, a * b ≠ b * a := by
    by_contra h
    push Not at h
    have : Group.IsSolvable (G ⧸ S) := Group.isSolvable_of_comm h
    exact hns (Group.isSolvable_of_ker_le_range S.subtype (QuotientGroup.mk' S)
      (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype]))
  -- Step 1: no proper subgroup `B` with `G = S B`
  have step1 : ∀ B : Subgroup G, S ⊔ B = ⊤ → B = ⊤ := by
    intro B hB
    by_contra hBt
    have hBlt : Nat.card B < n := by
      have := Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hBt)
      rwa [Subgroup.card_top, hn] at this
    have hBns : ¬ Group.IsSolvable B := fun h => hns (isSolvable_of_sup hSs h hB)
    obtain ⟨eB⟩ := nonempty_quotient_subgroupOf_equiv hB
    have : IsSimpleGroup (B ⧸ S.subgroupOf B) := eB.isSimpleGroup
    have hnabB : ∃ a b : B ⧸ S.subgroupOf B, a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := hXnab
      exact ⟨eB.symm a, eB.symm b, fun h => hab (by simpa using congrArg eB h)⟩
    have hsolvSB : Group.IsSolvable (S.subgroupOf B) :=
      Group.isSolvable_of_isSolvable_injective (f := B.subtype.subgroupComap S)
        (fun x y hxy => by
          have h := congrArg (fun z : S => (z : G)) hxy
          exact Subtype.ext (Subtype.ext h))
    have hrad : solvableRadical B = S.subgroupOf B := solvableRadical_eq_of _ hsolvSB hnabB
    obtain ⟨A₁, hA₁, hA₁c⟩ := ih _ hBlt B rfl (hG.subgroup B) hBns
      (QuotientGroup.quotientMulEquivOfEq hrad).isSimpleGroup
    rw [hrad] at hA₁ hA₁c
    set A := A₁.map B.subtype
    have hBeq : (S ⊓ B) ⊔ A = B := by
      have := congrArg (Subgroup.map B.subtype) hA₁
      rwa [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype] at this
    have h1 : S ⊔ A = ⊤ := by
      rw [← hB, ← hBeq, ← sup_assoc, sup_of_le_left (inf_le_left : S ⊓ B ≤ S)]
    have h2 : (S ⊓ A : Subgroup G) = (S.subgroupOf B ⊓ A₁).map B.subtype := by
      rw [Subgroup.map_inf_eq _ _ _ B.subtype_injective, Subgroup.subgroupOf_map_subtype, inf_assoc,
        inf_of_le_right (Subgroup.map_subtype_le A₁ : A ≤ B)]
    have := hcon A h1
    rw [h2, Subgroup.card_map_of_injective B.subtype_injective] at this
    omega
  -- Step 1': `G` is perfect
  have hperf : commutator G = ⊤ := by
    have hcns : ¬ Group.IsSolvable (commutator G) := fun h => hns (isSolvable_of_commutator h)
    apply step1
    apply sup_eq_top_of_map_eq_top
    rcases ((inferInstance : (commutator G).Normal).map _ (QuotientGroup.mk'_surjective S)).eq_bot_or_eq_top
      with h | h
    · exfalso
      have hle : commutator G ≤ S := by
        intro x hx
        have : QuotientGroup.mk' S x ∈ (commutator G).map (QuotientGroup.mk' S) := ⟨x, hx, rfl⟩
        rw [h, Subgroup.mem_bot] at this
        exact (QuotientGroup.eq_one_iff x).mp this
      exact hcns (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle))
    · exact h
  -- Step 2: `S` is not central
  have hSnc : ¬ S ≤ Subgroup.center G := by
    intro hSZ
    have hX15 : Lemma15Conclusion (G ⧸ S) := lemma_1_5 hXnab (hG.quotient S)
    have h2 := card_le_two_of_central hG hperf S hSZ (MulEquiv.refl _) hX15
    have := hcon ⊤ (by simp)
    rw [inf_top_eq] at this
    omega
  -- Step 3: `|S : R| ≤ 2` for every nontrivial normal `R ≤ S`
  have step3 : ∀ R : Subgroup G, R.Normal → R ≠ ⊥ → R ≤ S → Nat.card S ≤ 2 * Nat.card R := by
    intro R hRn hR1 hRS
    have := hRn
    have hR1' : 1 < Nat.card R := by
      rcases Nat.lt_or_ge 1 (Nat.card R) with h | h
      · exact h
      · exact absurd (Subgroup.eq_bot_of_card_le R h) hR1
    have hlt : Nat.card (G ⧸ R) < n := by
      have := Subgroup.card_eq_card_quotient_mul_card_subgroup R
      rw [hn] at this
      have hpos : 0 < Nat.card (G ⧸ R) := Nat.card_pos
      nlinarith
    set Sb : Subgroup (G ⧸ R) := S.map (QuotientGroup.mk' R)
    have hSbn : Sb.Normal := (solvableRadical_normal).map _ (QuotientGroup.mk'_surjective R)
    have hSbs : Group.IsSolvable Sb :=
      Group.isSolvable_of_surjective (f := (QuotientGroup.mk' R).subgroupMap S)
        (MonoidHom.subgroupMap_surjective _ _)
    let eb : (G ⧸ R) ⧸ Sb ≃* G ⧸ S := QuotientGroup.quotientQuotientEquivQuotient R S hRS
    have : IsSimpleGroup ((G ⧸ R) ⧸ Sb) := eb.isSimpleGroup
    have hnab' : ∃ a b : (G ⧸ R) ⧸ Sb, a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := hXnab
      exact ⟨eb.symm a, eb.symm b, fun h => hab (by simpa using congrArg eb h)⟩
    have hrad : solvableRadical (G ⧸ R) = Sb := solvableRadical_eq_of Sb hSbs hnab'
    have hGbns : ¬ Group.IsSolvable (G ⧸ R) := by
      intro h
      have : Group.IsSolvable R :=
        Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hRS)
      exact hns (Group.isSolvable_of_ker_le_range R.subtype (QuotientGroup.mk' R)
        (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype]))
    obtain ⟨Ub, hUb, hUbc⟩ := ih _ hlt (G ⧸ R) rfl (hG.quotient R) hGbns
      (QuotientGroup.quotientMulEquivOfEq hrad).isSimpleGroup
    rw [hrad] at hUb hUbc
    have hU : S ⊔ Ub.comap (QuotientGroup.mk' R) = ⊤ := by
      have hker : (QuotientGroup.mk' R).ker ≤ S ⊔ Ub.comap (QuotientGroup.mk' R) := by
        rw [QuotientGroup.ker_mk']; exact hRS.trans le_sup_left
      rw [← Subgroup.comap_map_eq_self hker, Subgroup.map_sup,
        Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective R), hUb, Subgroup.comap_top]
    have hUbtop : Ub = ⊤ := by
      have := step1 _ hU
      rw [eq_top_iff]
      intro x _
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective R x
      exact (this ▸ Subgroup.mem_top g : g ∈ Ub.comap (QuotientGroup.mk' R))
    rw [hUbtop, inf_top_eq] at hUbc
    have hcardSb : Nat.card S = Nat.card Sb * Nat.card R := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (R.subgroupOf S)
      have h2 : Nat.card (R.subgroupOf S) = Nat.card R :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRS).toEquiv
      have h3 : Nat.card (S ⧸ R.subgroupOf S) = Nat.card Sb := by
        have hker : ((QuotientGroup.mk' R).subgroupMap S).ker = R.subgroupOf S := by
          ext x
          rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
          constructor
          · intro h
            exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val h)
          · intro h
            exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr h)
        rw [← hker]
        exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
          (MonoidHom.subgroupMap_surjective _ _)).toEquiv
      rw [h1, h2, h3]
    rw [hcardSb]
    exact Nat.mul_le_mul_right _ hUbc
  -- Step 4: every Sylow subgroup of `S` is normal in `G`
  have hSylNormal : ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p S), ((P : Subgroup S).map S.subtype).Normal := by
    intro p _ P
    have h := step1 _ (by rw [sup_comm]; exact Sylow.normalizer_sup_eq_top P)
    exact Subgroup.normalizer_eq_top_iff.mp h
  have hS1 : S ≠ ⊥ := fun h => hSnc (h ▸ bot_le)
  -- `|S|` is odd
  have hodd : Odd (Nat.card S) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    obtain ⟨P⟩ : Nonempty (Sylow 2 S) := inferInstance
    set T : Subgroup G := (P : Subgroup S).map S.subtype
    have hTn : T.Normal := hSylNormal 2 P
    have hT2 : IsPGroup 2 T := (P.isPGroup').map S.subtype
    have hT1 : T ≠ ⊥ := by
      intro h
      have hP1 : Nat.card (P : Subgroup S) = 1 := by
        rw [← Subgroup.card_map_of_injective S.subtype_injective]
        change Nat.card T = 1
        rw [h, Subgroup.card_bot]
      rw [Sylow.card_eq_multiplicity] at hP1
      have := Nat.Prime.factorization_pos_of_dvd Nat.prime_two (Nat.card_pos (α := S)).ne'
        (even_iff_two_dvd.mp hev)
      have : 2 ≤ 2 ^ (Nat.card S).factorization 2 := by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ _ := Nat.pow_le_pow_right (by norm_num) this
      omega
    obtain ⟨R, hRT, hRn, hR1, -⟩ := exists_minimalNormal_le hTn hT1
    have hRS : R ≤ S := hRT.trans (Subgroup.map_subtype_le _)
    have h3 := step3 R hRn hR1 hRS
    have hR2 : IsPGroup 2 R := hT2.to_le hRT
    obtain ⟨k, hk⟩ := hR2.exists_card_eq
    obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hRS
    have hm2 : m = 1 ∨ m = 2 := by
      have hpos : 0 < Nat.card R := Nat.card_pos
      rcases Nat.lt_or_ge m 3 with h | h
      · rcases m with _ | _ | _ | m
        · simp at hm; exact absurd hm (Nat.card_pos (α := S)).ne'
        · exact Or.inl rfl
        · exact Or.inr rfl
        · omega
      · nlinarith
    have hS2 : IsPGroup 2 S := by
      apply IsPGroup.of_card (n := k + (m - 1))
      rcases hm2 with rfl | rfl <;> simp [hm, hk, pow_succ]
    exact hSnc (le_center_of_perfect hperf S hS2 (hG.isMetacyclic_of_isPGroup S hS2))
  -- `S` is a minimal normal subgroup, abelian of prime exponent `r`, of order `r` or `r²`
  obtain ⟨R, hRS, hRn, hR1, hRmin⟩ := exists_minimalNormal_le (solvableRadical_normal) hS1
  have hRSeq : R = S := by
    have h3 := step3 R hRn hR1 hRS
    obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hRS
    have hm1 : m = 1 := by
      have hpos : 0 < Nat.card R := Nat.card_pos
      rcases m with _ | _ | _ | m
      · simp at hm; exact absurd hm (Nat.card_pos (α := S)).ne'
      · rfl
      · exfalso; rw [hm] at hodd; exact Nat.not_odd_iff_even.mpr ⟨Nat.card R, by ring⟩ hodd
      · nlinarith
    exact Subgroup.eq_of_le_of_card_ge hRS (by rw [hm, hm1, mul_one])
  subst hRSeq
  -- `S` is abelian
  have hSab : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
    rcases hRmin _ inferInstance (Subgroup.commutator_le_left S S) with h | h
    · intro a ha b hb
      have := Subgroup.commutator_mem_commutator ha hb
      rwa [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    · exfalso
      have hc : commutator S = ⊤ := by
        apply Subgroup.map_injective S.subtype_injective
        rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, h]
      have hD : ∀ k, derivedSeries S k = ⊤ := by
        intro k
        induction k with
        | zero => rfl
        | succ k ih => rw [derivedSeries_succ, ih, ← commutator_def, hc]
      obtain ⟨k, hk⟩ := (isSolvable_def S).mp hSs
      rw [hD k] at hk
      apply hR1
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hx⟩ : S) ∈ (⊤ : Subgroup S) := Subgroup.mem_top _
      rw [hk, Subgroup.mem_bot] at this
      exact (Subgroup.mem_bot).mpr (congrArg Subtype.val this)
  -- `S` has prime exponent `r`
  have hR1' : Nat.card S ≠ 1 := fun h => hR1 (Subgroup.eq_bot_of_card_eq S h)
  obtain ⟨r, hr, hrR⟩ := Nat.exists_prime_and_dvd hR1'
  have : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr hrR)
  have hexp : ∀ x ∈ S, x ^ r = 1 := by
    let Ω : Subgroup G :=
      { carrier := {x | x ∈ S ∧ x ^ r = 1}
        one_mem' := ⟨one_mem _, one_pow r⟩
        mul_mem' := fun {a b} ha hb =>
          ⟨mul_mem ha.1 hb.1, by rw [(Commute.mul_pow (hSab a ha.1 b hb.1) r), ha.2, hb.2, one_mul]⟩
        inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
    have hΩn : Ω.Normal := ⟨fun x hx g => ⟨hRn.conj_mem x hx.1 g, by
      rw [conj_pow, hx.2, mul_one, mul_inv_cancel]⟩⟩
    have hΩ1 : Ω ≠ ⊥ := by
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := S) r hrR
      intro h
      have hyΩ : (y : G) ∈ Ω := ⟨y.2, by rw [← Subgroup.coe_pow, ← hy, pow_orderOf_eq_one]; rfl⟩
      rw [h, Subgroup.mem_bot] at hyΩ
      have : y = 1 := Subtype.ext hyΩ
      rw [this, orderOf_one] at hy
      exact hr.one_lt.ne' hy.symm
    rcases hRmin Ω hΩn (fun x hx => hx.1) with h | h
    · exact absurd h hΩ1
    · intro x hx
      rw [← h] at hx
      exact hx.2
  have hRr : IsPGroup r S := fun x => ⟨1, Subtype.ext (by simpa using hexp x x.2)⟩
  have hRdvd : Nat.card S ∣ r ^ 2 := hG.card_dvd_sq S hRr hexp
  -- `C_G(S) = S`
  have hC : Subgroup.centralizer (S : Set G) = S := by
    have hRC : S ≤ Subgroup.centralizer (S : Set G) := fun a ha =>
      Subgroup.mem_centralizer_iff.mpr fun b hb => hSab b hb a ha
    rcases ((inferInstance : (Subgroup.centralizer (S : Set G)).Normal).map _
        (QuotientGroup.mk'_surjective S)).eq_bot_or_eq_top with h | h
    · refine le_antisymm (fun x hx => ?_) hRC
      have : QuotientGroup.mk' S x ∈ (Subgroup.centralizer (S : Set G)).map (QuotientGroup.mk' S) :=
        ⟨x, hx, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact (QuotientGroup.eq_one_iff x).mp this
    · exfalso
      have htop := sup_eq_top_of_map_eq_top h
      rw [sup_of_le_right hRC] at htop
      apply hSnc
      intro x hx
      rw [Subgroup.mem_center_iff]
      intro g
      exact ((Subgroup.mem_centralizer_iff.mp (htop ▸ Subgroup.mem_top g)) x hx).symm
  -- `G/S` acts faithfully on `S`
  set φ : G →* MulAut S := MulAut.conjNormal
  have hker : φ.ker = S := by
    ext g
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      rw [← hC, Subgroup.mem_centralizer_iff]
      intro x hx
      have := congrArg (fun σ : MulAut S => ((σ ⟨x, hx⟩ : S) : G)) h
      simp only [φ, MulAut.conjNormal_apply, MulAut.one_apply] at this
      calc x * g = (g * x * g⁻¹) * g := by rw [this]
        _ = g * x := by group
    · intro hg
      ext ⟨x, hx⟩
      simp only [φ, MulAut.conjNormal_apply, MulAut.one_apply]
      rw [hSab g hg x hx, mul_inv_cancel_right]
  let ψ : G ⧸ S →* MulAut S :=
    (QuotientGroup.kerLift φ).comp (QuotientGroup.quotientMulEquivOfEq hker.symm).toMonoidHom
  have hψ : Function.Injective ψ := (QuotientGroup.kerLift_injective φ).comp (MulEquiv.injective _)
  have hcentral : ∀ w : G ⧸ S, (∀ x, ψ w x = x⁻¹) → w = 1 := by
    intro w hw
    have hwc : w ∈ Subgroup.center (G ⧸ S) := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply hψ
      rw [map_mul, map_mul]
      exact commute_of_inversion hw
    rw [center_eq_bot_of_simple hXnab, Subgroup.mem_bot] at hwc
    exact hwc
  obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow hr).mp hRdvd
  interval_cases k
  · exact hR1' (by simpa using hk)
  · -- `|S| = r`: `Aut(S)` is abelian
    obtain ⟨a, b, hab⟩ := hXnab
    exact hab (hψ (by rw [map_mul, map_mul]; exact mulAut_comm_of_card_prime (by simpa using hk) _ _))
  · -- `|S| = r²`: a Klein four-subgroup of `G/S` would contain the inversion map
    obtain ⟨E, hEc, hEs, hE4⟩ := exists_elem4 (G ⧸ S) hXnab
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
      have hsub : (E : Set (G ⧸ S)) ⊆ {1, t} := fun u hu => by
        by_cases hu1 : u = 1
        · exact Or.inl hu1
        · exact Or.inr (h u hu hu1).symm
      have := Set.ncard_le_ncard hsub
      rw [← Nat.card_coe_set_eq] at this
      have h2 : ({1, t} : Set (G ⧸ S)).ncard ≤ 2 := by
        have := Set.ncard_insert_le (1 : G ⧸ S) {t}
        rwa [Set.ncard_singleton] at this
      change Nat.card E ≤ _ at this
      omega
    obtain ⟨u, hu, hu1, htu⟩ := hEu
    have hsq : ∀ x ∈ E, (ψ x) ^ 2 = 1 := fun x hx => by rw [← map_pow, hEs x hx, map_one]
    have hne1 : ∀ x, x ≠ 1 → ψ x ≠ 1 := fun x hx h => hx (hψ (by rw [h, map_one]))
    have htu1 : t * u ≠ 1 := by
      intro h
      have ht2 := hEs t ht
      rw [pow_two] at ht2
      exact htu (by calc t = t * (t * u) := by rw [h, mul_one]
        _ = (t * t) * u := by group
        _ = u := by rw [ht2, one_mul])
    rcases exists_inversion_of_klein hr2 (fun a b => Subtype.ext (hSab a a.2 b b.2))
        (fun x => Subtype.ext (by simpa using hexp x x.2)) (by simpa using hk) (hsq t ht) (hsq u hu)
        (by rw [← map_mul, ← map_mul, hEc t ht u hu]) (hne1 t ht1) (hne1 u hu1)
        (fun h => htu (hψ h)) with h | h | h
    · exact ht1 (hcentral t h)
    · exact hu1 (hcentral u h)
    · exact htu1 (hcentral (t * u) (by simpa [map_mul] using h))

/-- **Chillag–Sonn, Lemma (1.8).** If `G` is a nonsolvable Sylow-metacyclic group with `G/S(G)` simple, then
`G = S(G) A` for a subgroup `A` with `|S(G) ∩ A| ≤ 2`. -/
theorem lemma_1_8 {G : Type} [Group G] [Finite G] (hG : SylowMetacyclic G) (hns : ¬ Group.IsSolvable G)
    (hsimp : IsSimpleGroup (G ⧸ solvableRadical G)) :
    ∃ A : Subgroup G, solvableRadical G ⊔ A = ⊤ ∧ Nat.card (solvableRadical G ⊓ A : Subgroup G) ≤ 2 :=
  lemma_1_8_aux _ G rfl hG hns hsimp

end CFSGOutside.ChillagSonn
