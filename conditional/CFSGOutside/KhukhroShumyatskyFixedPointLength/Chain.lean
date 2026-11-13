import CFSGOutside.Corpus.OddOrder
import CFSGOutside.Corpus.Schreier
import CFSGOutside.KhukhroShumyatskyFixedPointLength.Lemma35

/-!
# Khukhro–Shumyatsky, fixed points: Proposition 3.2

E. I. Khukhro and P. Shumyatsky, *On the length of finite groups and of fixed points*, Proc. Amer. Math. Soc.
**143** (2015), 3781–3790. The chain of the proof of Proposition 3.2 (`ChainProp`, `chainProp_zero`,
`chainProp_succ`) and Proposition 3.2 itself (`nonsolubleLengthLE_of_commSub_eq_top`).
-/

namespace CFSGOutside.KhukhroShumyatskyFixedPointLength

open Subgroup CFSGOutside.Corpus CFSGOutside.Corpus.LocalCores
open CFSGOutside.NonsolubleLength CFSGOutside.UpperNonsolubleSeries
open scoped commutatorElement

section Aux2

variable {X : Type} [Group X] [Finite X]

/-- The layer normalizes every subnormal subgroup. -/
lemma layer_le_normalizer_of_subnormal {U : Subgroup X} (hU : U.IsSubnormal) :
    layer X ≤ normalizer (U : Set X) := by
  refine sSup_le fun K hK => ?_
  rcases component_subnormal_subgroup hK hU with h | h
  · exact h.trans le_normalizer
  · exact (commutator_eq_bot_iff_le_centralizer.mp h).trans (Subgroup.centralizer_le_normalizer _)

/-- A perfect subgroup of `A ⊔ P` lies in `A ⊔ P'` once some derived term of `P` lies in `P'`. -/
lemma perfect_le_sup {D A P P' : Subgroup X} [A.Normal] (hD : ⁅D, D⁆ = D) {b : ℕ}
    (hb : dA b P ≤ P') (h : D ≤ A ⊔ P) : D ≤ A ⊔ P' := by
  rw [← dA_eq_self_of_perfect hD b]
  exact (dA_mono b h).trans ((dA_sup_le A P b).trans (sup_le_sup_left hb A))

lemma dA_subgroupOf_le (H K : Subgroup X) (b : ℕ) :
    dA b (H.subgroupOf K) ≤ (dA b H).subgroupOf K := by
  intro x hx
  rw [mem_subgroupOf]
  have : (dA b (H.subgroupOf K)).map K.subtype ≤ dA b H := by
    rw [map_dA, subgroupOf_map_subtype]; exact dA_mono b inf_le_left
  exact this ⟨x, hx, rfl⟩

lemma mem_normalizer_comap {A B : Type*} [Group A] [Group B] {f : A →* B} {E : Subgroup B} {c : A}
    (h : f c ∈ normalizer (E : Set B)) : c ∈ normalizer ((E.comap f : Subgroup A) : Set A) := by
  rw [mem_normalizer_iff] at h ⊢
  intro n
  simp only [SetLike.mem_coe, mem_comap, map_mul, map_inv]
  exact h (f n)

lemma mem_normalizer_map {A B : Type*} [Group A] [Group B] {f : A →* B} {U : Subgroup A} {c : A}
    (h : c ∈ normalizer (U : Set A)) : f c ∈ normalizer ((U.map f : Subgroup B) : Set B) := by
  exact Subgroup.le_normalizer_map f ⟨c, h, rfl⟩

end Aux2

section Chain

variable {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime] {φ : MulAut G}
  (hφ : φ ^ p = 1) (hpG : ¬ p ∣ Nat.card G)

/-- The chain property at level `t`: the diagonal of a nontrivial `φ`-orbit of components of
`G/M_{t+1}` is not covered by the image of `μ_{t+1}(C_G(φ))`. -/
def ChainProp (t : ℕ) : Prop :=
  ∀ (R : Subgroup (G ⧸ lvN G t)) (hR : IsComponent R) (hRnt : orb (lvAut φ t) R 1 ≠ R),
    ¬ diag (lvAut_pow hφ t) hR hRnt ≤ (upperSeries (fixedSub φ) (2 * t + 1)).map (rho φ t)

include hpG in
lemma exists_lift_diag {t : ℕ} {R : Subgroup (G ⧸ lvN G t)} (hR : IsComponent R)
    (hRnt : orb (lvAut φ t) R 1 ≠ R) :
    ∃ Dh : Subgroup (fixedSub φ), ⁅Dh, Dh⁆ = Dh ∧
      Dh.map (rho φ t) = diag (lvAut_pow hφ t) hR hRnt := by
  obtain ⟨Dh, h1, h2, -⟩ := exists_perfect_lift hφ hpG (F := ⊤)
    (by show (⊤ : Subgroup G).map φ.toMonoidHom = ⊤; exact map_top_of_surjective _ φ.surjective)
    (diag_le_fixedSub (lvAut_pow hφ t) hR hRnt)
    (by rw [map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]; exact le_top)
    (diag_perfect (lvAut_pow hφ t) hR hRnt)
  exact ⟨Dh, h1, h2⟩

include hpG in
lemma chainProp_zero : ChainProp hφ 0 := by
  intro R hR hRnt h
  obtain ⟨Dh, hDp, hDD⟩ := exists_lift_diag hφ hpG hR hRnt
  rw [← hDD, Subgroup.map_le_map_iff] at h
  obtain ⟨b, hb⟩ := exists_dA_upperSeries_odd_le (X := fixedSub φ) 0
  have h2 := perfect_le_sup (A := (rho φ 0).ker) hDp hb (by rwa [sup_comm] at h)
  rw [show upperSeries (fixedSub φ) (2 * 0) = ⊥ from upperSeries_zero _, sup_bot_eq] at h2
  have h3 := (Subgroup.map_eq_bot_iff _).2 h2
  rw [hDD] at h3
  exact diag_ne_bot (lvAut_pow hφ 0) hR hRnt (lvF (G := G) 0) h3

include hpG in
/-- **The chain step** (the induction in the proof of Proposition 3.2). -/
lemma chainProp_succ [Schreier] (hCFSG : TauCeti.ClassificationStatement.{0}) (hp3 : 3 ≤ p) {t : ℕ}
    (ih : ChainProp hφ t) : ChainProp hφ (t + 1) := by
  intro S hS hnt hcon
  obtain ⟨Dh, hDhp, hDhD, x, hx, R, hR, hRnt, hRx⟩ := lemma35 hCFSG hφ hpG hp3 hS hnt
  have hχ : lvAut φ t ^ p = 1 := lvAut_pow hφ t
  obtain ⟨Dh', hDp', hDD'⟩ := exists_lift_diag hφ hpG hR hRnt
  set E := diag hχ hR hRnt with hE
  set ρ := rho φ t with hρ
  have hEtop : ∃ i, E ≤ (upperSeries (fixedSub φ) i).map ρ := by
    obtain ⟨l, hl⟩ := exists_upperSeries_eq_top (X := fixedSub φ)
    refine ⟨2 * l + 1, ?_⟩
    rw [hl, ← MonoidHom.range_eq_map, hρ, range_rho hφ hpG]
    exact diag_le_fixedSub hχ hR hRnt
  classical
  have hi0 : E ≤ (upperSeries (fixedSub φ) (Nat.find hEtop)).map ρ := Nat.find_spec hEtop
  have hmin : ∀ i < Nat.find hEtop, ¬ E ≤ (upperSeries (fixedSub φ) i).map ρ :=
    fun i hi => Nat.find_min hEtop hi
  have hgt : 2 * t + 1 < Nat.find hEtop := by
    by_contra hle
    push Not at hle
    exact ih R hR hRnt (hi0.trans (map_mono (upperSeries_mono hle)))
  have hodd : ∀ k, Nat.find hEtop ≠ 2 * k + 1 := by
    intro k hk
    have h1 : Dh' ≤ upperSeries (fixedSub φ) (2 * k + 1) ⊔ ρ.ker := by
      rw [← Subgroup.map_le_map_iff, hDD', ← hk]; exact hi0
    obtain ⟨b, hb⟩ := exists_dA_upperSeries_odd_le (X := fixedSub φ) k
    have h2 := perfect_le_sup (A := ρ.ker) hDp' hb (by rwa [sup_comm] at h1)
    rw [sup_comm, ← Subgroup.map_le_map_iff, hDD'] at h2
    exact hmin (2 * k) (by omega) h2
  obtain ⟨k, hk, htk⟩ : ∃ k, Nat.find hEtop = 2 * k + 2 ∧ t ≤ k := by
    have := hodd (Nat.find hEtop / 2)
    exact ⟨Nat.find hEtop / 2 - 1, by omega, by omega⟩
  have hnotM : ¬ E ≤ (upperSeries (fixedSub φ) (2 * k + 1)).map ρ := hmin _ (by omega)
  have hMn : (upperSeries (fixedSub φ) (2 * k + 1) ⊔ ρ.ker).Normal := inferInstance
  set M := upperSeries (fixedSub φ) (2 * k + 1) ⊔ ρ.ker with hM
  set πZ := QuotientGroup.mk' M with hπZ
  obtain ⟨T, hT⟩ : ∃ T, T = Dh'.map πZ := ⟨_, rfl⟩
  have hA1 : E.comap ρ = Dh' ⊔ ρ.ker := by rw [← hDD', comap_map_eq]
  have hTA1 : T = (E.comap ρ).map πZ := by
    rw [hT, hA1, Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).2 (show ρ.ker ≤ πZ.ker by
      rw [hπZ, QuotientGroup.ker_mk']; exact le_sup_right), sup_bot_eq]
  have hlayN : ∀ c : fixedSub φ, ρ c ∈ layer (G ⧸ lvN G t) →
      c ∈ normalizer ((E.comap ρ : Subgroup _) : Set (fixedSub φ)) := fun c hc =>
    mem_normalizer_comap (mem_normalizer_diag hχ hR hRnt (rho_mem_fixed φ t c)
      (layer_le_normalizer hR hc))
  -- `T` is subnormal in `Z`
  have hsub : (E.comap ρ).IsSubnormal := by
    haveI := layer_normal' (Y := G ⧸ lvN G t)
    have hle : E.comap ρ ≤ (layer (G ⧸ lvN G t)).comap ρ := fun c hc =>
      diag_le_layer hχ hR hRnt hc
    have hA2 : ((layer (G ⧸ lvN G t)).comap ρ).IsSubnormal :=
      IsSubnormal.step _ ⊤ le_top IsSubnormal.top inferInstance
    refine IsSubnormal.step _ _ hle hA2 ?_
    exact (Subgroup.normal_subgroupOf_iff hle).2 fun z c hz hc =>
      Subgroup.le_normalizer_iff.1 (fun c hc => hlayN c hc) c hc z hz
  have hTsub : T.IsSubnormal := by
    rw [hTA1]; exact hsub.map (QuotientGroup.mk'_surjective M)
  have hlayT := layer_le_normalizer_of_subnormal hTsub
  -- `μ`-level `2k+2` of `C` normalizes `T`
  have hU : upperSeries (fixedSub φ) (2 * k + 2) ≤ (normalizer (T : Set _)).comap πZ := by
    intro c hc
    rw [upperSeries_even] at hc
    let f := QuotientGroup.map (upperSeries (fixedSub φ) (2 * k + 1)) M (MonoidHom.id _)
      (fun y hy => le_sup_left (b := ρ.ker) hy)
    have hf : Function.Surjective f := by
      intro z
      obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective M z
      exact ⟨c, rfl⟩
    have := map_layer_le f hf ⟨_, hc, rfl⟩
    exact hlayT this
  -- `C ∩ L_{t+1}` normalizes `T`
  have hQ : (upperSeries G (2 * t + 2)).subgroupOf (fixedSub φ) ≤
      (normalizer (T : Set _)).comap πZ := by
    intro c hc
    rw [mem_subgroupOf, upperSeries_even] at hc
    have := hlayN c hc
    rw [mem_comap, hTA1]
    exact mem_normalizer_map this
  -- `D̂ ≤ μ_{2k+2} (C ∩ L_{t+1})`
  have hDh1 : Dh ≤ upperSeries (fixedSub φ) (2 * (t + 1) + 1) ⊔ (rho φ (t + 1)).ker := by
    rw [← Subgroup.map_le_map_iff, hDhD]; exact hcon
  have hDh2 : Dh ≤ (rho φ (t + 1)).ker ⊔ upperSeries (fixedSub φ) (2 * (k + 1) + 1) := by
    rw [sup_comm]
    exact hDh1.trans (sup_le_sup_right (upperSeries_mono (by omega)) _)
  obtain ⟨b, hb⟩ := exists_dA_upperSeries_odd_le (X := fixedSub φ) (k + 1)
  have hDh3 := perfect_le_sup (A := (rho φ (t + 1)).ker) hDhp hb hDh2
  obtain ⟨b', hb'⟩ := exists_dA_upperSeries_odd_le (X := G) (t + 1)
  have hb'' : dA b' (rho φ (t + 1)).ker ≤ (upperSeries G (2 * t + 2)).subgroupOf (fixedSub φ) := by
    rw [ker_rho]
    refine (dA_subgroupOf_le _ _ b').trans fun c hc => ?_
    rw [mem_subgroupOf] at hc ⊢
    have := hb' hc
    rwa [show 2 * (t + 1) = 2 * t + 2 by ring] at this
  have hDh4 := perfect_le_sup (A := upperSeries (fixedSub φ) (2 * (k + 1))) hDhp hb''
    (by rwa [sup_comm] at hDh3)
  have hxN : πZ x ∈ normalizer (T : Set _) := by
    have : upperSeries (fixedSub φ) (2 * (k + 1)) ⊔
        (upperSeries G (2 * t + 2)).subgroupOf (fixedSub φ) ≤ (normalizer (T : Set _)).comap πZ :=
      sup_le (by rw [show 2 * (k + 1) = 2 * k + 2 by ring]; exact hU) hQ
    exact this (hDh4 hx)
  -- the commutator relation `[D̂', D̂'^x] ≤ N`
  have hcomm : ∀ d1 ∈ Dh', ∀ d2 ∈ Dh', ⁅d1, x * d2 * x⁻¹⁆ ∈ ρ.ker := by
    intro d1 hd1 d2 hd2
    have he1 : ρ d1 ∈ E := by rw [← hDD']; exact ⟨d1, hd1, rfl⟩
    have he2 : ρ d2 ∈ E := by rw [← hDD']; exact ⟨d2, hd2, rfl⟩
    have he2' := conj_mem_diag hχ hR hRnt (rho_mem_fixed φ t x) he2
    have hc := diag_commute hχ hR hRnt (isComponent_map_mulEquiv _ hR)
      (orb_ne_conj_of_fixed hχ hR hRnt (rho_mem_fixed φ t x)) hRx _ he1 _ he2'
    rw [MonoidHom.mem_ker, map_commutatorElement, map_mul, map_mul, map_inv,
      commutatorElement_eq_one_iff_commute]
    exact hc
  -- hence `T` is abelian and perfect, so trivial
  have hTbot : T = ⊥ := by
    have hTp : ⁅T, T⁆ = T := by rw [hT, ← Subgroup.map_commutator, hDp']
    rw [← hTp, eq_bot_iff, Subgroup.commutator_le]
    intro w1 hw1 w hw
    rw [hT] at hw1
    obtain ⟨d1, hd1, rfl⟩ := hw1
    have hw' : (πZ x)⁻¹ * w * (πZ x)⁻¹⁻¹ ∈ T :=
      (mem_normalizer_iff.1 (inv_mem hxN) w).1 hw
    rw [hT] at hw'
    obtain ⟨d2, hd2, hd2w⟩ := hw'
    have hw2 : w = πZ (x * d2 * x⁻¹) := by
      rw [map_mul, map_mul, map_inv, hd2w]; group
    rw [hw2, mem_bot, ← map_commutatorElement, ← MonoidHom.mem_ker, hπZ, QuotientGroup.ker_mk']
    exact le_sup_right (a := upperSeries (fixedSub φ) (2 * k + 1)) (hcomm d1 hd1 d2 hd2)
  apply hnotM
  have hDM : Dh' ≤ M := by
    rw [← QuotientGroup.ker_mk' M, ← Subgroup.map_eq_bot_iff, ← hπZ, ← hT]; exact hTbot
  rw [← hDD', Subgroup.map_le_map_iff]; exact hDM

end Chain

section Prop32

variable {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime] {φ : MulAut G}

/-- **Proposition 3.2 (Khukhro–Shumyatsky)**.  If `φ` is an automorphism of prime order `p`
coprime to `|G|` and `G = [G, φ]`, then `λ(G) ≤ λ(C_G(φ)) + 1`. -/
theorem nonsolubleLengthLE_of_commSub_eq_top [OddOrder.{0}] [Schreier] (hCFSG : TauCeti.ClassificationStatement.{0})
    (hφ : φ ^ p = 1) (hpG : ¬ p ∣ Nat.card G) (hcomm : commSub φ = ⊤) {l : ℕ}
    (hl : NonsolubleLengthLE (fixedSub φ) l) : NonsolubleLengthLE G (l + 1) := by
  rw [nonsolubleLengthLE_iff_upperSeries] at hl ⊢
  by_contra h
  have hp3 : 3 ≤ p := by
    have := hp.out.two_le
    suffices p ≠ 2 by omega
    rintro rfl
    apply h
    haveI : Group.IsSolvable G :=
      OddOrder.isSolvable_of_odd_natCard _ (Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hpG))
    have h0 := nonsolubleLengthLE_iff_upperSeries.1 (nonsolubleLengthLE_zero_of_isSolvable (X := G))
    rw [eq_top_iff, ← h0]
    exact upperSeries_mono (by omega)
  have hchain : ∀ t, ChainProp hφ t := fun t =>
    Nat.rec (chainProp_zero hφ hpG) (fun _ ih => chainProp_succ hφ hpG hCFSG hp3 ih) t
  obtain ⟨S, hS, hnt⟩ := exists_nontrivial_orbit hCFSG hcomm (t := l)
    (by rwa [show 2 * l + 3 = 2 * (l + 1) + 1 by ring])
  apply hchain l S hS hnt
  rw [hl, ← MonoidHom.range_eq_map, range_rho hφ hpG]
  exact diag_le_fixedSub _ hS hnt

end Prop32

end CFSGOutside.KhukhroShumyatskyFixedPointLength
