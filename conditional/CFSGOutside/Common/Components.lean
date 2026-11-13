import CFSGOutside.Corpus.Defs.Components
import CFSGOutside.Corpus.Defs.Fitting

/-!
# Components of a group with trivial Fitting subgroup

For a finite group `K` with `F(K) = 1`: every soluble subnormal subgroup is trivial, so the components of `K` are
nonabelian simple groups with pairwise trivial intersections, and `C_K(E(K)) = 1`. These are the corpus facts
`CFSG.EvenSporadicStandard.SolomonRed.{component_center_eq_bot, component_isSimple, component_nonab,
component_inf_eq_bot, centralizer_layer_eq_bot}` (`CFSG/LocalAnalysis/EvenSporadicStandard/SolomonRed/Layer.lean`
at AxiomMath/CFSG commit 69cb972f587a3ecc035e092253167ff2e303c962), proved here from Mathlib. The proof of
`centralizer_layer_eq_bot` differs from the corpus one: a minimal nonsoluble subnormal subgroup of the
centralizer of the layer would be a component.
-/

universe u

namespace CFSGOutside.Corpus.LocalCores

open Subgroup

section Radical

variable {G : Type*} [Group G] [Finite G]

instance solvableRadical_characteristic : (solvableRadical G).Characteristic := by
  rw [characteristic_iff_map_le]
  intro φ
  haveI := isSolvable_solvableRadical (G := G)
  exact le_solvableRadical ((solvableRadical_normal).map _ φ.surjective)
    (Group.isSolvable_of_surjective (φ.toMonoidHom.subgroupMap_surjective _))

/-- A finite product of soluble groups is soluble. Copy of the corpus proof of
`CFSG.LocalAnalysis.RankFourTheoremC.Lemma213.isSolvable_pi_of_finite`. -/
theorem isSolvable_pi_of_finite {ι : Type*} [Finite ι] {H : ι → Type*} [∀ i, Group (H i)]
    [∀ i, Group.IsSolvable (H i)] : Group.IsSolvable (∀ i, H i) := by
  cases nonempty_fintype ι
  have hle : ∀ k : ℕ, derivedSeries (∀ i, H i) k ≤
      Subgroup.pi Set.univ (fun i => derivedSeries (H i) k) := by
    intro k
    induction k with
    | zero =>
      simp only [derivedSeries_zero]
      rw [Subgroup.pi_top]
    | succ k ih =>
      rw [derivedSeries_succ]
      calc ⁅derivedSeries (∀ i, H i) k, derivedSeries (∀ i, H i) k⁆
          ≤ ⁅Subgroup.pi Set.univ (fun i => derivedSeries (H i) k),
              Subgroup.pi Set.univ (fun i => derivedSeries (H i) k)⁆ :=
            Subgroup.commutator_mono ih ih
        _ ≤ Subgroup.pi Set.univ (fun i => ⁅derivedSeries (H i) k, derivedSeries (H i) k⁆) :=
            Subgroup.commutator_pi_pi_le _ _
        _ = Subgroup.pi Set.univ (fun i => derivedSeries (H i) (k + 1)) := by
            simp_rw [derivedSeries_succ]
  choose n hn using fun i => (inferInstance : Group.IsSolvable (H i)).solvable
  refine ⟨⟨Finset.univ.sup n, ?_⟩⟩
  rw [eq_bot_iff]
  refine (hle _).trans ?_
  rw [le_bot_iff, Subgroup.pi_eq_bot_iff]
  intro i
  rw [eq_bot_iff, ← hn i]
  exact derivedSeries_antitone (H i) (Finset.le_sup (f := n) (Finset.mem_univ i))

/-- `F(G) = 1` forces `R(G) = 1`: the last nontrivial derived subgroup of `R(G)` is abelian and normal. -/
theorem solvableRadical_eq_bot_of_fittingSubgroup_eq_bot (hF : fittingSubgroup G = ⊥) :
    solvableRadical G = ⊥ := by
  classical
  set R := solvableRadical G
  haveI hRs := isSolvable_solvableRadical (G := G)
  have hex : ∃ k, derivedSeries R k = ⊥ := (isSolvable_def R).1 hRs
  by_contra hne
  have hm0 : Nat.find hex ≠ 0 := by
    intro h0
    have h := Nat.find_spec hex
    rw [h0, derivedSeries_zero] at h
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hx⟩ : R) ∈ (⊤ : Subgroup R) := mem_top _
    rw [h, mem_bot] at this
    exact mem_bot.2 (congrArg Subtype.val this)
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  set A := derivedSeries R k
  have hA : A ≠ ⊥ := Nat.find_min hex (by omega)
  have hA' : ⁅A, A⁆ = ⊥ := by
    have h := Nat.find_spec hex
    rwa [hk, Nat.succ_eq_add_one, derivedSeries_succ] at h
  set B := A.map R.subtype
  have hBn : B.Normal := ConjAct.normal_of_characteristic_of_normal
  have hcomm : ∀ a b : B, a * b = b * a := by
    rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
    have h : a * b = b * a := by
      have := commutator_mem_commutator ha hb
      rwa [hA', mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact Subtype.ext (by simpa using congrArg Subtype.val h)
  letI : CommGroup B := { (inferInstance : Group B) with mul_comm := hcomm }
  have hBF : B ≤ fittingSubgroup G := le_sSup ⟨hBn, CommGroup.isNilpotent⟩
  rw [hF, le_bot_iff, map_eq_bot_iff_of_injective _ R.subtype_injective] at hBF
  exact hA hBF

theorem eq_bot_of_isSubnormal_aux (n : ℕ) :
    ∀ (K : Type u) [Group K] [Finite K], Nat.card K = n → solvableRadical K = ⊥ →
      ∀ S : Subgroup K, S.IsSubnormal → Group.IsSolvable S → S = ⊥ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro K _ _ hcard hR S hS hs
  rcases hS.lt_normal with rfl | ⟨M, hMn, hSM, hMlt⟩
  · rw [← le_bot_iff, ← hR]
    exact le_solvableRadical normal_top hs
  · have hMcard : Nat.card M < n := by
      rw [← hcard, ← Subgroup.card_top (G := K)]
      exact Subgroup.card_lt_of_lt hMlt
    have hRM : solvableRadical M = ⊥ := by
      haveI := hMn
      haveI := isSolvable_solvableRadical (G := M)
      have h1 : (solvableRadical M).map M.subtype ≤ solvableRadical K :=
        le_solvableRadical ConjAct.normal_of_characteristic_of_normal
          (Group.isSolvable_of_surjective (M.subtype.subgroupMap_surjective _))
      rwa [hR, le_bot_iff, map_eq_bot_iff_of_injective _ M.subtype_injective] at h1
    have hs' : Group.IsSolvable (S.subgroupOf M) :=
      Group.isSolvable_of_isSolvable_injective (f := (subgroupOfEquivOfLe hSM).toMonoidHom)
        (subgroupOfEquivOfLe hSM).injective
    have h := ih _ hMcard M rfl hRM (S.subgroupOf M) hS.subgroupOf hs'
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hSM hx⟩ : M) ∈ S.subgroupOf M := hx
    rw [h, mem_bot] at hx'
    exact mem_bot.2 (congrArg Subtype.val hx')

/-- In a group with trivial soluble radical, every soluble subnormal subgroup is trivial. -/
theorem eq_bot_of_isSubnormal_of_isSolvable {K : Type u} [Group K] [Finite K]
    (hR : solvableRadical K = ⊥) {S : Subgroup K} (hS : S.IsSubnormal) (hs : Group.IsSolvable S) :
    S = ⊥ :=
  eq_bot_of_isSubnormal_aux _ K rfl hR S hS hs

end Radical

section Fitting

variable {K : Type u} [Group K] [Finite K]

theorem component_center_eq_bot (hF : fittingSubgroup K = ⊥) {L : Subgroup K}
    (hL : IsComponent L) : Subgroup.center ↥L = ⊥ := by
  have hR := solvableRadical_eq_bot_of_fittingSubgroup_eq_bot hF
  set Z := (center L).map L.subtype
  have hZL : Z ≤ L := map_subtype_le _
  have hZsub : Z.IsSubnormal := by
    refine Subgroup.IsSubnormal.trans hZL ?_ hL.2
    have : Z.subgroupOf L = center L := comap_map_eq_self_of_injective L.subtype_injective _
    rw [this]
    exact (inferInstance : (center L).Normal).isSubnormal
  have hZs : Group.IsSolvable Z := by
    refine isSolvable_of_comm fun a b => ?_
    obtain ⟨_, a, ha, rfl⟩ := a
    obtain ⟨_, b, hb, rfl⟩ := b
    exact Subtype.ext (by simpa using congrArg Subtype.val (mem_center_iff.mp hb a))
  have h := eq_bot_of_isSubnormal_of_isSolvable hR hZsub hZs
  exact (map_eq_bot_iff_of_injective _ L.subtype_injective).1 h

theorem component_isSimple (hF : fittingSubgroup K = ⊥) {L : Subgroup K} (hL : IsComponent L) :
    IsSimpleGroup ↥L := by
  have hc := component_center_eq_bot hF hL
  have := hL.1.2.1
  let e : ↥L ⧸ Subgroup.center ↥L ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  exact e.symm.isSimpleGroup

theorem component_nonab (hF : fittingSubgroup K = ⊥) {L : Subgroup K} (hL : IsComponent L) :
    ∃ a ∈ L, ∃ b ∈ L, a * b ≠ b * a := by
  have hc := component_center_eq_bot hF hL
  let e : ↥L ⧸ Subgroup.center ↥L ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  obtain ⟨a, b, hab⟩ := hL.1.2.2
  refine ⟨(e a : K), (e a).2, (e b : K), (e b).2, fun h => hab (e.injective ?_)⟩
  rw [map_mul, map_mul]
  exact Subtype.ext h

theorem component_inf_eq_bot (hF : fittingSubgroup K = ⊥) {L₁ L₂ : Subgroup K}
    (h₁ : IsComponent L₁) (h₂ : IsComponent L₂) (hne : L₁ ≠ L₂) : L₁ ⊓ L₂ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hc := component_commute h₁ h₂ hne
  have hxZ : (⟨x, hx.1⟩ : L₁) ∈ center L₁ := by
    rw [mem_center_iff]
    intro b
    exact Subtype.ext (hc b b.2 x hx.2)
  rw [component_center_eq_bot hF h₁, mem_bot] at hxZ
  exact mem_bot.2 (congrArg Subtype.val hxZ)

/-- `C_K(E(K)) = 1` when `F(K) = 1`. -/
theorem centralizer_layer_eq_bot (hF : fittingSubgroup K = ⊥) :
    centralizer (layer K : Set K) = ⊥ := by
  have hR := solvableRadical_eq_bot_of_fittingSubgroup_eq_bot hF
  set C : Subgroup K := centralizer (layer K : Set K)
  have hCn : C.Normal := Subgroup.normal_centralizer
  by_contra hC
  have hCns : ¬ Group.IsSolvable C := fun hs =>
    hC (eq_bot_of_isSubnormal_of_isSolvable hR hCn.isSubnormal hs)
  obtain ⟨L, ⟨hLC, hLsub, hLns⟩, hmin⟩ :=
    (Set.toFinite {M : Subgroup K | M ≤ C ∧ M.IsSubnormal ∧ ¬ Group.IsSolvable M}).exists_minimal
      ⟨C, le_rfl, hCn.isSubnormal, hCns⟩
  have key : ∀ N : Subgroup L, N.Normal → N = ⊥ ∨ N = ⊤ := by
    intro N hN
    set N' := N.map L.subtype
    have hN'L : N' ≤ L := map_subtype_le N
    have hsub : N'.IsSubnormal := by
      refine Subgroup.IsSubnormal.trans hN'L ?_ hLsub
      have : N'.subgroupOf L = N := comap_map_eq_self_of_injective L.subtype_injective N
      rw [this]
      exact hN.isSubnormal
    by_cases hs : Group.IsSolvable N'
    · left
      exact (map_eq_bot_iff_of_injective _ L.subtype_injective).1
        (eq_bot_of_isSubnormal_of_isSolvable hR hsub hs)
    · right
      have hLN := hmin ⟨hN'L.trans hLC, hsub, hs⟩ hN'L
      rw [eq_top_iff]
      intro x _
      obtain ⟨y, hy, hyx⟩ := hLN x.2
      rwa [show y = x from Subtype.ext hyx] at hy
  have hnt : Nontrivial L := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hLns inferInstance
  haveI : IsSimpleGroup L := { eq_bot_or_eq_top_of_normal := key }
  have hnab : ∃ a b : L, a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact hLns (isSolvable_of_comm h)
  have hcomp : IsComponent L := ⟨(isQuasisimple_of_isSimpleGroup hnab).1, hLsub⟩
  obtain ⟨a, b, hab⟩ := hnab
  exact hab (Subtype.ext (mem_centralizer_iff.1 (hLC a.2) b (component_le_layer hcomp b.2)).symm)

end Fitting

end CFSGOutside.Corpus.LocalCores
