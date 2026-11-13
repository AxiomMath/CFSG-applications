import CFSGOutside.ChillagSonn.Case1
import CFSGOutside.Corpus.Gaschutz

/-!
# Lemma (1.10) of Chillag–Sonn: `O(G)` has a complement

If `G` is a nonsolvable Sylow-metacyclic group such that `G/S(G)` has a nonabelian simple normal subgroup `Y` of
index 2 (in the paper `G/S(G) ≅ PGL(2, pⁿ)` or `PGL*(2, p²)`), then `O(G)` has a complement in `G`.

Minimal counterexample, as in the paper: for a minimal normal `R ≤ O(G)`, a complement of `O(G)/R = O(G/R)` in
`G/R` lifts to `E` with `G = O(G) E`, `O(G) ∩ E = R`. If `E < G`, then `O(E) = R` (the join `O(G) O(E)` is normal of
odd order) and a complement of `R` in `E` is one of `O(G)` in `G`; so `E = G` and `O(G) = R` is an abelian
`r`-group. The preimage `G₁` of `Y` splits over `O(G)` by Case 1, and Gaschütz's theorem, through a Sylow
`r`-subgroup of `G₁` (one of `G`, as `r` is odd), gives a complement in `G`.
-/

namespace CFSGOutside.ChillagSonn

open CFSGOutside.Corpus CFSGOutside.Corpus.Open CFSGOutside.Corpus.RankThree.PerfectCover
  CFSGOutside.Corpus.GorensteinWalter CFSGOutside.Corpus.GroupTheory Subgroup
open scoped commutatorElement

/-- `X` has a nonabelian simple normal subgroup of index 2. -/
def HasSimpleIndexTwo (X : Type) [Group X] : Prop :=
  ∃ Y : Subgroup X, Y.Normal ∧ Y.index = 2 ∧ IsSimpleGroup Y ∧ ∃ a b : Y, a * b ≠ b * a

/-- `HasSimpleIndexTwo` is invariant under isomorphism. -/
theorem HasSimpleIndexTwo.of_mulEquiv {X X' : Type} [Group X] [Group X'] (e : X ≃* X')
    (h : HasSimpleIndexTwo X) : HasSimpleIndexTwo X' := by
  obtain ⟨Y, hn, hi, hs, a, b, hab⟩ := h
  set f := Y.equivMapOfInjective (e : X →* X') e.injective
  have := hs
  exact ⟨Y.map (e : X →* X'), hn.map _ e.surjective, by rw [index_map_equiv, hi], f.symm.isSimpleGroup,
    f a, f b, fun h => hab (f.injective (by rw [map_mul, map_mul]; exact h))⟩

section Helpers

variable {G : Type} [Group G] [Finite G]

/-- The odd core is characteristic. -/
instance characteristic_oddCore (Y : Type) [Group Y] [Finite Y] : (oddCore Y).Characteristic :=
  characteristic_iff_comap_le.2 fun φ => le_oddCore ((oddCore_normal Y).comap _)
    (Odd.of_dvd_nat odd_card_oddCore (card_comap_dvd_of_injective _ _ φ.injective))

omit [Finite G] in
/-- `S ∩ B` is solvable if `S` is. -/
theorem isSolvable_subgroupOf {S : Subgroup G} (hS : Group.IsSolvable S) (B : Subgroup G) :
    Group.IsSolvable (S.subgroupOf B) :=
  Group.isSolvable_of_isSolvable_injective (f := B.subtype.subgroupComap S)
    (fun _ _ hxy => Subtype.ext (Subtype.ext (congrArg (fun z : S => (z : G)) hxy)))

/-- If `M ⊴ H` is solvable and `H/M ≅ G/S(G)`, then `S(H) = M`, and `H` inherits the hypotheses of `G`. -/
theorem hypotheses_of_equiv {H : Type} [Group H] [Finite H] (M : Subgroup H) [M.Normal]
    (hM : Group.IsSolvable M) (e : H ⧸ M ≃* G ⧸ solvableRadical G) (hns : ¬ Group.IsSolvable G)
    (hY : HasSimpleIndexTwo (G ⧸ solvableRadical G)) :
    solvableRadical H = M ∧ ¬ Group.IsSolvable H ∧ HasSimpleIndexTwo (H ⧸ solvableRadical H) := by
  set φ : H →* G ⧸ solvableRadical G := (e : H ⧸ M →* G ⧸ solvableRadical G).comp (QuotientGroup.mk' M)
  have hφ : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective M)
  have : Group.IsSolvable (solvableRadical H) := isSolvable_solvableRadical
  have hrad : solvableRadical H = M := by
    refine le_antisymm (fun x hx => ?_) (le_solvableRadical inferInstance hM)
    have h := eq_bot_of_normal_solvable_quotient _ ((inferInstance : (solvableRadical H).Normal).map φ hφ)
      (Group.isSolvable_of_surjective (φ.subgroupMap_surjective (solvableRadical H)))
    have h1 : e (x : H ⧸ M) = 1 := by
      rw [← mem_bot, ← h]; exact mem_map_of_mem φ hx
    rwa [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at h1
  refine ⟨hrad, fun h => hns ?_, hY.of_mulEquiv ((QuotientGroup.quotientMulEquivOfEq hrad).trans e).symm⟩
  have := h
  have : Group.IsSolvable (G ⧸ solvableRadical G) := Group.isSolvable_of_surjective hφ
  have : Group.IsSolvable (solvableRadical G) := isSolvable_solvableRadical
  exact Group.isSolvable_of_subgroup_quotient (solvableRadical G)

/-- `O(G/R) = O(G)/R` for a normal `R ≤ O(G)`. -/
theorem oddCore_quotient (R : Subgroup G) [R.Normal] (hR : R ≤ oddCore G) :
    oddCore (G ⧸ R) = (oddCore G).map (QuotientGroup.mk' R) := by
  refine le_antisymm (fun x hx => ?_) (le_oddCore ((oddCore_normal G).map _ (QuotientGroup.mk'_surjective R))
    (Odd.of_dvd_nat odd_card_oddCore
      (card_dvd_of_surjective ((QuotientGroup.mk' R).subgroupMap_surjective _))))
  set P := (oddCore (G ⧸ R)).comap (QuotientGroup.mk' R)
  set f := (QuotientGroup.mk' R).subgroupComap (oddCore (G ⧸ R))
  have hf : Function.Surjective f := MonoidHom.subgroupComap_surjective _ _ (QuotientGroup.mk'_surjective R)
  have hRP : R ≤ P := fun y hy => by
    rw [mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff y).2 hy]; exact one_mem _
  have hker : f.ker = R.subgroupOf P := by
    ext y
    rw [MonoidHom.mem_ker, mem_subgroupOf, ← QuotientGroup.eq_one_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hP : Odd (Nat.card P) := by
    rw [← card_ker_mul_card_of_surjective hf, hker, Nat.card_congr (subgroupOfEquivOfLe hRP).toEquiv]
    exact (Odd.of_dvd_nat odd_card_oddCore (card_dvd_of_le hR)).mul odd_card_oddCore
  have hPO : P ≤ oddCore G := le_oddCore ((oddCore_normal _).comap _) hP
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective R x
  exact mem_map_of_mem _ (hPO hx)

omit [Finite G] in
/-- If `N ⊴ G` has odd order, `N ≤ H` and `O(H) ≤ N`, then `O(H) = N ∩ H`. -/
theorem oddCore_eq_subgroupOf {H N : Subgroup G} [N.Normal] (hodd : Odd (Nat.card N)) (hNH : N ≤ H)
    (hle : (oddCore H).map H.subtype ≤ N) : oddCore H = N.subgroupOf H :=
  le_antisymm (fun x hx => mem_subgroupOf.2 (hle (mem_map_of_mem _ hx)))
    (le_oddCore inferInstance (by rwa [Nat.card_congr (subgroupOfEquivOfLe hNH).toEquiv]))

omit [Finite G] in
/-- If `N ⊴ G`, `G = N E` and `E` normalizes `K`, then `N ⊔ K ⊴ G`. -/
theorem normal_sup_of_le_normalizer {N K E : Subgroup G} [hN : N.Normal] (hE : E ≤ normalizer (K : Set G))
    (h : N ⊔ E = ⊤) : (N ⊔ K).Normal := by
  have key : ∀ e ∈ E, ∀ x ∈ N ⊔ K, e * x * e⁻¹ ∈ N ⊔ K := by
    intro e he x hx
    obtain ⟨n, hn, k, hk, rfl⟩ := mem_sup_of_normal_left.mp hx
    rw [show e * (n * k) * e⁻¹ = (e * n * e⁻¹) * (e * k * e⁻¹) by group]
    exact mul_mem (mem_sup_left (hN.conj_mem n hn e)) (mem_sup_right ((mem_normalizer_iff.1 (hE he) k).1 hk))
  rw [← normalizer_eq_top_iff, eq_top_iff, ← h]
  refine sup_le (le_sup_left.trans le_normalizer) fun e he => mem_normalizer_iff.2 fun x =>
    ⟨key e he x, fun hx => ?_⟩
  simpa [mul_assoc] using key e⁻¹ (inv_mem he) _ hx

/-- A solvable minimal normal subgroup is abelian of prime exponent. -/
theorem minimalNormal_elem {R : Subgroup G} [hRn : R.Normal] (hR1 : R ≠ ⊥)
    (hRmin : ∀ M : Subgroup G, M.Normal → M ≤ R → M = ⊥ ∨ M = R) (hRs : Group.IsSolvable R) :
    (∀ a ∈ R, ∀ b ∈ R, a * b = b * a) ∧ ∃ r : ℕ, r.Prime ∧ r ∣ Nat.card R ∧ IsPGroup r R := by
  have hab : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := by
    rcases hRmin _ inferInstance (commutator_le_left R R) with h | h
    · intro a ha b hb
      have := commutator_mem_commutator ha hb
      rwa [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    · exfalso
      have hc : commutator R = ⊤ := by
        apply map_injective R.subtype_injective
        rw [commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype, h]
      have hD : ∀ k, derivedSeries R k = ⊤ := by
        intro k
        induction k with
        | zero => rfl
        | succ k ih => rw [derivedSeries_succ, ih, ← commutator_def, hc]
      obtain ⟨k, hk⟩ := (Group.isSolvable_def R).mp hRs
      rw [hD k] at hk
      apply hR1
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hx⟩ : R) ∈ (⊤ : Subgroup R) := mem_top _
      rw [hk, mem_bot] at this
      exact mem_bot.mpr (congrArg Subtype.val this)
  refine ⟨hab, ?_⟩
  have hR1' : Nat.card R ≠ 1 := fun h => hR1 (eq_bot_of_card_eq R h)
  obtain ⟨r, hr, hrR⟩ := Nat.exists_prime_and_dvd hR1'
  have : Fact r.Prime := ⟨hr⟩
  have hexp : ∀ x ∈ R, x ^ r = 1 := by
    let Ω : Subgroup G :=
      { carrier := {x | x ∈ R ∧ x ^ r = 1}
        one_mem' := ⟨one_mem _, one_pow r⟩
        mul_mem' := fun {a b} ha hb =>
          ⟨mul_mem ha.1 hb.1, by rw [(Commute.mul_pow (hab a ha.1 b hb.1) r), ha.2, hb.2, one_mul]⟩
        inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
    have hΩn : Ω.Normal := ⟨fun x hx g => ⟨hRn.conj_mem x hx.1 g, by
      rw [conj_pow, hx.2, mul_one, mul_inv_cancel]⟩⟩
    have hΩ1 : Ω ≠ ⊥ := by
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := R) r hrR
      intro h
      have hyΩ : (y : G) ∈ Ω := ⟨y.2, by rw [← Subgroup.coe_pow, ← hy, pow_orderOf_eq_one]; rfl⟩
      rw [h, mem_bot] at hyΩ
      have : y = 1 := Subtype.ext hyΩ
      rw [this, orderOf_one] at hy
      exact hr.one_lt.ne' hy.symm
    rcases hRmin Ω hΩn (fun x hx => hx.1) with h | h
    · exact absurd h hΩ1
    · intro x hx
      rw [← h] at hx
      exact hx.2
  exact ⟨r, hr, hrR, fun x => ⟨1, Subtype.ext (by simpa using hexp x x.2)⟩⟩

/-- Step 4: an abelian normal `r`-subgroup `V`, `r` odd, lying in a subgroup `G₁` of index 2 and with a complement
in `G₁`, has a complement in `G` (Gaschütz's theorem, twice). -/
theorem exists_compl_of_index_two [Gaschutz.{0}] {r : ℕ} [Fact r.Prime] (hr : r ≠ 2) {V G₁ : Subgroup G}
    [V.Normal] (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hVp : IsPGroup r V) (hVG : V ≤ G₁)
    (hi : G₁.index = 2) {A₁ : Subgroup G₁} (h1 : V.subgroupOf G₁ ⊓ A₁ = ⊥) (h2 : V.subgroupOf G₁ ⊔ A₁ = ⊤) :
    ∃ K : Subgroup G, V ⊓ K = ⊥ ∧ V ⊔ K = ⊤ := by
  have : IsMulCommutative (V.subgroupOf G₁) :=
    ⟨⟨fun a b => Subtype.ext (Subtype.ext (hVc _ (mem_subgroupOf.1 a.2) _ (mem_subgroupOf.1 b.2)))⟩⟩
  have : IsMulCommutative V := ⟨⟨fun a b => Subtype.ext (hVc _ a.2 _ b.2)⟩⟩
  obtain ⟨P₁⟩ : Nonempty (Sylow r G₁) := inferInstance
  have hVp₁ : IsPGroup r (V.subgroupOf G₁) := hVp.comap_of_injective G₁.subtype G₁.subtype_injective
  obtain ⟨K, hKP, hK1, hK2⟩ := (Gaschutz.gaschutz hVp₁ P₁).1 ⟨A₁, h1, h2⟩
  have hidx : ¬ r ∣ ((P₁ : Subgroup G₁).map G₁.subtype).index := by
    rw [index_map_subtype, hi]
    intro h
    rcases (Nat.Prime.dvd_mul Fact.out).1 h with h | h
    · exact P₁.not_dvd_index h
    · exact hr ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h)
  refine (Gaschutz.gaschutz hVp ((P₁.2.map G₁.subtype).toSylow hidx)).2 ⟨K.map G₁.subtype, ?_, ?_, ?_⟩
  · rw [IsPGroup.toSylow_coe]; exact map_mono hKP
  · have := congrArg (map G₁.subtype) hK1
    rwa [map_inf_eq _ _ _ G₁.subtype_injective, subgroupOf_map_subtype, inf_of_le_left hVG, Subgroup.map_bot] at this
  · have := congrArg (map G₁.subtype) hK2
    rw [Subgroup.map_sup, subgroupOf_map_subtype, inf_of_le_left hVG] at this
    rw [IsPGroup.toSylow_coe]; exact this

end Helpers

section Main

variable [CardKerDvdHopfMultiplier] [PslTwoHopfMultiplier] [HopfMultiplierAlternating]
  [CardHopfMultiplierEqCardGriess] [FieldNineAlternatingSix.{0}] [HopfMultiplierM11]
  [MinimalNormalSimpleFactors.{0}] [TwoLePRankOfIsSimpleGroup.{0}] [LrRankTwoIsomorphismTypes]
  [CardStatedProjStatedSL] [CardPsuThreeMulGcd] [FrattiniElementaryQuotient.{0}]
  [FrattiniAutomorphismKernel.{0}] [HopfCentralCoverConsequences] [FrobeniusNormalPComplement.{0}]
  [Gaschutz.{0}]

/-- Lemma (1.10), by strong induction on the order. -/
theorem lemma_1_10_aux (n : ℕ) : ∀ (G : Type) [Group G] [Finite G], Nat.card G = n → SylowMetacyclic G →
    ¬ Group.IsSolvable G → HasSimpleIndexTwo (G ⧸ solvableRadical G) →
    ∃ A : Subgroup G, oddCore G ⊓ A = ⊥ ∧ oddCore G ⊔ A = ⊤ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ _ hn hG hns hY
  set S := solvableRadical G with hSdef
  set O := oddCore G with hOdef
  have hSs : Group.IsSolvable S := isSolvable_solvableRadical
  have hOS : O ≤ S := le_solvableRadical inferInstance
    (isSolvable_of_odd_of_sylowMetacyclic (hG.subgroup _) odd_card_oddCore)
  by_cases hO : O = ⊥
  · exact ⟨⊤, by rw [hO, bot_inf_eq], by rw [sup_top_eq]⟩
  by_contra hcon
  -- Step 1: a minimal normal subgroup `R ≤ O(G)`
  obtain ⟨R, hRO, hRn, hR1, hRmin⟩ := exists_minimalNormal_le (oddCore_normal G) hO
  have := hRn
  have hRS : R ≤ S := hRO.trans hOS
  have hRodd : Odd (Nat.card R) := Odd.of_dvd_nat odd_card_oddCore (card_dvd_of_le hRO)
  -- Step 2: induction in `G/R` gives `E` with `G = O(G) E` and `O(G) ∩ E = R`
  have hlt : Nat.card (G ⧸ R) < n := by
    have hR1' : 1 < Nat.card R := (one_lt_card_iff_ne_bot _).2 hR1
    have := card_eq_card_quotient_mul_card_subgroup R
    rw [hn] at this
    have hpos : 0 < Nat.card (G ⧸ R) := Nat.card_pos
    nlinarith
  have : (S.map (QuotientGroup.mk' R)).Normal := (solvableRadical_normal).map _ (QuotientGroup.mk'_surjective R)
  obtain ⟨-, hnsb, hYb⟩ := hypotheses_of_equiv (S.map (QuotientGroup.mk' R))
    (Group.isSolvable_of_surjective ((QuotientGroup.mk' R).subgroupMap_surjective S))
    (QuotientGroup.quotientQuotientEquivQuotient R S hRS) hns hY
  obtain ⟨Eb, hEb1, hEb2⟩ := ih _ hlt (G ⧸ R) rfl (hG.quotient R) hnsb hYb
  rw [oddCore_quotient R hRO] at hEb1 hEb2
  set E := Eb.comap (QuotientGroup.mk' R) with hEdef
  have hRE : R ≤ E := fun x hx => by
    rw [mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx]; exact one_mem _
  have hOE : O ⊔ E = ⊤ := by
    have h := sup_eq_top_of_map_eq_top (S := R) (N := O ⊔ E)
      (by rw [Subgroup.map_sup, map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective R), hEb2])
    rwa [sup_of_le_right (hRO.trans le_sup_left)] at h
  have hOEinf : O ⊓ E = R := by
    refine le_antisymm (fun x hx => ?_) (le_inf hRO hRE)
    have : QuotientGroup.mk' R x ∈ O.map (QuotientGroup.mk' R) ⊓ Eb :=
      mem_inf.2 ⟨mem_map_of_mem _ (mem_inf.1 hx).1, (mem_inf.1 hx).2⟩
    rw [hEb1, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    exact this
  -- Step 3: `E = G`, so `O(G) = R`
  have hEtop : E = ⊤ := by
    by_contra hEt
    have hElt : Nat.card E < n := by
      have := card_lt_of_lt (lt_top_iff_ne_top.mpr hEt); rwa [card_top, hn] at this
    have hSE : S ⊔ E = ⊤ := eq_top_iff.2 (hOE ▸ sup_le_sup_right hOS E)
    obtain ⟨eE⟩ := nonempty_quotient_subgroupOf_equiv hSE
    obtain ⟨-, hnsE, hYE⟩ := hypotheses_of_equiv _ (isSolvable_subgroupOf hSs E) eE hns hY
    obtain ⟨E₁, hE₁1, hE₁2⟩ := ih _ hElt E rfl (hG.subgroup E) hnsE hYE
    have hOE' : oddCore E = R.subgroupOf E := by
      refine oddCore_eq_subgroupOf hRodd hRE ?_
      rw [← hOEinf]
      refine le_inf ?_ (map_subtype_le _)
      have hEK : E ≤ normalizer (((oddCore E).map E.subtype : Subgroup G) : Set G) := by
        have := le_normalizer_map (H := oddCore E) E.subtype
        rwa [normalizer_eq_top_iff.2 inferInstance, ← MonoidHom.range_eq_map, range_subtype] at this
      have := normal_sup_of_le_normalizer hEK hOE
      exact le_sup_right.trans (le_oddCore inferInstance (odd_card_sup _ _ odd_card_oddCore
        (by rw [card_map_of_injective E.subtype_injective]; exact odd_card_oddCore)))
    rw [hOE'] at hE₁1 hE₁2
    apply hcon
    refine ⟨E₁.map E.subtype, eq_bot_iff.2 fun x hx => ?_, ?_⟩
    · obtain ⟨hxO, ⟨y, hy, rfl⟩⟩ := mem_inf.1 hx
      have : y ∈ R.subgroupOf E ⊓ E₁ :=
        mem_inf.2 ⟨mem_subgroupOf.2 (hOEinf ▸ mem_inf.2 ⟨hxO, y.2⟩), hy⟩
      rw [hE₁1, mem_bot] at this
      rw [this, map_one]; exact one_mem _
    · rw [eq_top_iff, ← hOE]
      refine sup_le le_sup_left ?_
      have := congrArg (map E.subtype) hE₁2
      rw [Subgroup.map_sup, subgroupOf_map_subtype, ← MonoidHom.range_eq_map, range_subtype] at this
      exact this.symm.le.trans (sup_le_sup (inf_le_left.trans hRO) le_rfl)
  have hOR : O = R := by rw [hEtop, inf_top_eq] at hOEinf; exact hOEinf
  have hRs : Group.IsSolvable R := Group.isSolvable_of_isSolvable_injective (inclusion_injective hRS)
  obtain ⟨hab, r, hr, hrR, hRp⟩ := minimalNormal_elem hR1 hRmin hRs
  have : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact Nat.not_even_iff_odd.mpr hRodd (even_iff_two_dvd.mpr hrR)
  -- Step 4: the preimage `G₁` of `Y` splits over `O(G)` (Case 1), and Gaschütz's theorem
  obtain ⟨Y, hYn, hYi, hYs, hYnab⟩ := hY
  set G₁ := Y.comap (QuotientGroup.mk' S) with hG₁def
  have : G₁.Normal := hYn.comap _
  have hG₁i : G₁.index = 2 := by
    rw [hG₁def, index_comap_of_surjective (H := Y) (hf := QuotientGroup.mk'_surjective S), hYi]
  have hSG₁ : S ≤ G₁ := fun x hx => by
    rw [mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx]; exact one_mem _
  set f := (QuotientGroup.mk' S).subgroupComap Y
  have hf : Function.Surjective f := MonoidHom.subgroupComap_surjective _ _ (QuotientGroup.mk'_surjective S)
  have hker : f.ker = S.subgroupOf G₁ := by
    ext y
    rw [MonoidHom.mem_ker, mem_subgroupOf, ← QuotientGroup.eq_one_iff]
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
  obtain ⟨A₁, h1, h2, -⟩ := case1_split (hG.subgroup G₁) hns₁
    (QuotientGroup.quotientMulEquivOfEq hrad₁).isSimpleGroup
  have hO₁ : oddCore G₁ = R.subgroupOf G₁ := oddCore_eq_subgroupOf hRodd (hRS.trans hSG₁) (by
    rw [← hOR]
    exact le_oddCore (normal_map_subtype_of_characteristic _)
      (by rw [card_map_of_injective G₁.subtype_injective]; exact odd_card_oddCore))
  rw [hO₁] at h1 h2
  apply hcon
  rw [hOR]
  exact exists_compl_of_index_two hr2 hab hRp (hRS.trans hSG₁) hG₁i h1 h2

end Main

/-- **Chillag–Sonn, Lemma (1.10).** -/
theorem lemma_1_10 [Gaschutz.{0}] [CardKerDvdHopfMultiplier] [PslTwoHopfMultiplier] [HopfMultiplierAlternating]
    [CardHopfMultiplierEqCardGriess] [FieldNineAlternatingSix.{0}] [HopfMultiplierM11]
    [MinimalNormalSimpleFactors.{0}] [TwoLePRankOfIsSimpleGroup.{0}] [LrRankTwoIsomorphismTypes]
    [CardStatedProjStatedSL] [CardPsuThreeMulGcd] [FrattiniElementaryQuotient.{0}]
    [FrattiniAutomorphismKernel.{0}] [HopfCentralCoverConsequences] [FrobeniusNormalPComplement.{0}]
    {G : Type} [Group G] [Finite G] (hG : SylowMetacyclic G) (hns : ¬ Group.IsSolvable G)
    (hY : ∃ Y : Subgroup (G ⧸ solvableRadical G), Y.Normal ∧ Y.index = 2 ∧ IsSimpleGroup Y ∧
      ∃ a b : Y, a * b ≠ b * a) :
    ∃ A : Subgroup G, oddCore G ⊓ A = ⊥ ∧ oddCore G ⊔ A = ⊤ :=
  lemma_1_10_aux _ G rfl hG hns hY

end CFSGOutside.ChillagSonn
