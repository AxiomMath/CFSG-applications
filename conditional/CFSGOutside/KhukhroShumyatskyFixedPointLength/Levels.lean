import CFSGOutside.Corpus.Schreier
import CFSGOutside.KhukhroShumyatskyFixedPointLength.Diagonal
import CFSGOutside.KhukhroShumyatskyFixedPointLength.SeriesLength

/-!
# Khukhro–Shumyatsky, fixed points: the levels `G / M_{t+1}` and Lemma 3.3

E. I. Khukhro and P. Shumyatsky, *On the length of finite groups and of fixed points*, Proc. Amer. Math. Soc.
**143** (2015), 3781–3790. The levels `G / M_{t+1}` of the upper nonsoluble series with the induced automorphism and
the map `rho : C_G(φ) → G / M_{t+1}`, Lemma 2.1 at level `t` (`kernel_le_upperSeries`, from Schreier's
conjecture) and Lemma 3.3 (`exists_nontrivial_orbit`).
-/

namespace CFSGOutside.KhukhroShumyatskyFixedPointLength

open Subgroup CFSGOutside.Corpus CFSGOutside.Corpus.LocalCores
open CFSGOutside.NonsolubleLength CFSGOutside.UpperNonsolubleSeries
open scoped commutatorElement

section General

variable {X : Type} [Group X] [Finite X]

/-- A nontrivial finite group with trivial Fitting subgroup has a component. -/
lemma exists_component {K : Type} [Group K] [Finite K] (hF : fittingSubgroup K = ⊥)
    (h : ∃ x : K, x ≠ 1) : ∃ L : Subgroup K, IsComponent L := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hx⟩ := h
  have hl : layer K = ⊥ := layer_eq_bot_of_forall hcon
  have hx' : x ∈ centralizer (layer K : Set K) := by
    rw [hl, mem_centralizer_iff]
    intro y hy
    obtain rfl : y = 1 := by simpa using hy
    simp
  rw [centralizer_layer_eq_bot hF] at hx'
  exact hx (mem_bot.1 hx')

lemma upperSeries_lt_succ_even {k : ℕ} (h : upperSeries X (2 * k + 1) ≠ ⊤) :
    upperSeries X (2 * k + 1) < upperSeries X (2 * k + 2) := by
  refine lt_of_le_of_ne (upperSeries_le_succ _) fun heq => ?_
  set N := upperSeries X (2 * k + 1)
  haveI : Nontrivial (X ⧸ N) := QuotientGroup.nontrivial_iff.2 h
  obtain ⟨L, hL⟩ := exists_component (fittingSubgroup_quotient_upperSeries_odd k)
    (exists_ne (1 : X ⧸ N))
  haveI := component_isSimple (fittingSubgroup_quotient_upperSeries_odd k) hL
  obtain ⟨⟨y, hyL⟩, hy1⟩ := exists_ne (1 : L)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  have hx : x ∈ upperSeries X (2 * k + 2) := by
    rw [upperSeries_even]; exact component_le_layer hL hyL
  rw [← heq] at hx
  exact hy1 (Subtype.ext ((QuotientGroup.eq_one_iff x).2 hx))

/-- Every finite group has finite nonsoluble length. -/
lemma exists_upperSeries_eq_top : ∃ l, upperSeries X (2 * l + 1) = ⊤ := by
  by_contra hcon
  push Not at hcon
  have key : ∀ n, n ≤ Nat.card (upperSeries X (2 * n + 1)) := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih =>
      have h1 := Subgroup.card_lt_of_lt (upperSeries_lt_succ_even (hcon n))
      have h2 := Subgroup.card_le_of_le (upperSeries_le_succ (X := X) (2 * n + 2))
      rw [show 2 * (n + 1) + 1 = 2 * n + 2 + 1 by ring]
      omega
  have h1 := key (Nat.card X + 1)
  have h2 := Subgroup.card_le_card_group (upperSeries X (2 * (Nat.card X + 1) + 1))
  omega

/-- `dA b (A ⊔ P) ≤ A ⊔ dA b P` for normal `A`. -/
lemma dA_sup_le (A P : Subgroup X) [A.Normal] (b : ℕ) : dA b (A ⊔ P) ≤ A ⊔ dA b P := by
  have h1 : (dA b (A ⊔ P)).map (QuotientGroup.mk' A) ≤ (dA b P).map (QuotientGroup.mk' A) := by
    rw [map_dA, map_dA, Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).2 (by
      rw [QuotientGroup.ker_mk']), bot_sup_eq]
  intro x hx
  obtain ⟨y, hy, hyx⟩ := h1 ⟨x, hx, rfl⟩
  have : y⁻¹ * x ∈ A := QuotientGroup.eq.1 hyx
  rw [show x = y * (y⁻¹ * x) by group]
  rw [sup_comm]
  exact mul_mem (mem_sup_left hy) (mem_sup_right this)

lemma dA_eq_self_of_perfect {D : Subgroup X} (hD : ⁅D, D⁆ = D) (n : ℕ) : dA n D = D := by
  induction n with
  | zero => rfl
  | succ n ih => rw [dA, ih, hD]

/-- Every subgroup has a perfect derived term. -/
lemma exists_perfect_dA (Z : Subgroup X) : ∃ n, ⁅dA n Z, dA n Z⁆ = dA n Z := by
  by_contra hcon
  push Not at hcon
  have hlt : ∀ n, dA (n + 1) Z < dA n Z := fun n =>
    lt_of_le_of_ne (show dA (n + 1) Z ≤ dA n Z from dA_le 1 (dA n Z)) (hcon n)
  have key : ∀ n, n + Nat.card (dA n Z) ≤ Nat.card Z := by
    intro n
    induction n with
    | zero => simp; rfl
    | succ n ih => have := Subgroup.card_lt_of_lt (hlt n); omega
  have := key (Nat.card Z + 1)
  omega

end General

section Levels

variable {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime] {φ : MulAut G}

lemma isInv_upperSeries (φ : MulAut G) (j : ℕ) : IsInv φ (upperSeries G j) :=
  map_upperSeries φ j

/-- The `t`-th level `M_{t+1} = upperSeries G (2t+1)`. -/
noncomputable abbrev lvN (G : Type) [Group G] [Finite G] (t : ℕ) : Subgroup G :=
  upperSeries G (2 * t + 1)

/-- The automorphism induced by `φ` on `G/M_{t+1}`. -/
noncomputable def lvAut (φ : MulAut G) (t : ℕ) : MulAut (G ⧸ lvN G t) :=
  quotAut φ (lvN G t) (isInv_upperSeries φ _)

lemma lvAut_mk (φ : MulAut G) (t : ℕ) (x : G) :
    lvAut φ t (x : G ⧸ lvN G t) = (φ x : G ⧸ lvN G t) := rfl

lemma lvAut_pow (hφ : φ ^ p = 1) (t : ℕ) : lvAut φ t ^ p = 1 :=
  quotAut_pow_eq_one hφ _ _

lemma not_dvd_card_quotient (hpG : ¬ p ∣ Nat.card G) (N : Subgroup G) [N.Normal] :
    ¬ p ∣ Nat.card (G ⧸ N) := fun h => hpG (h.trans (Subgroup.card_quotient_dvd_card N))

lemma lvF (t : ℕ) : fittingSubgroup (G ⧸ lvN G t) = ⊥ :=
  fittingSubgroup_quotient_upperSeries_odd t

/-- The map `C_G(φ) → G/M_{t+1}`. -/
noncomputable def rho (φ : MulAut G) (t : ℕ) : fixedSub φ →* G ⧸ lvN G t :=
  (QuotientGroup.mk' _).comp (fixedSub φ).subtype

lemma rho_apply (φ : MulAut G) (t : ℕ) (c : fixedSub φ) :
    rho φ t c = ((c : G) : G ⧸ lvN G t) := rfl

lemma ker_rho (φ : MulAut G) (t : ℕ) : (rho φ t).ker = (lvN G t).subgroupOf (fixedSub φ) := by
  ext c
  simp [rho, mem_subgroupOf, QuotientGroup.eq_one_iff]

lemma rho_mem_fixed (φ : MulAut G) (t : ℕ) (c : fixedSub φ) :
    rho φ t c ∈ fixedSub (lvAut φ t) := by
  rw [mem_fixedSub, rho_apply, lvAut_mk, c.2]

variable (hφ : φ ^ p = 1) (hpG : ¬ p ∣ Nat.card G)
include hφ hpG

/-- Coprime action: every fixed point of `φ` on `G/M_{t+1}` (inside the image of an invariant
subgroup `F`) lifts to a fixed point of `φ` in `F`. -/
lemma exists_fixed_lift {t : ℕ} {F : Subgroup G} (hF : IsInv φ F) {d : G ⧸ lvN G t}
    (hd : d ∈ fixedSub (lvAut φ t)) (hdF : d ∈ F.map (QuotientGroup.mk' _)) :
    ∃ c : fixedSub φ, (c : G) ∈ F ∧ rho φ t c = d := by
  obtain ⟨y, hyF, rfl⟩ := hdF
  have hy : y⁻¹ * φ y ∈ F ⊓ lvN G t := by
    refine ⟨F.mul_mem (F.inv_mem hyF) (hF.mem hyF), ?_⟩
    have : ((y : G) : G ⧸ lvN G t) = ((φ y : G) : G ⧸ lvN G t) := by
      rw [← lvAut_mk]; exact hd.symm
    exact QuotientGroup.eq.1 this
  have hinv : ∀ n ∈ F ⊓ lvN G t, φ n ∈ F ⊓ lvN G t := fun n hn =>
    ⟨hF.mem hn.1, (isInv_upperSeries φ _).mem hn.2⟩
  obtain ⟨n, hn, hfix⟩ := exists_fixed_mul hφ hpG hinv hy
  refine ⟨⟨y * n, hfix⟩, mul_mem hyF hn.1, ?_⟩
  rw [rho_apply]
  simp only [QuotientGroup.mk'_apply]
  rw [QuotientGroup.eq]
  simpa using (lvN G t).inv_mem hn.2

lemma range_rho (t : ℕ) : (rho φ t).range = fixedSub (lvAut φ t) := by
  refine le_antisymm (by rintro _ ⟨c, rfl⟩; exact rho_mem_fixed φ t c) fun d hd => ?_
  obtain ⟨c, -, hc⟩ := exists_fixed_lift hφ hpG (F := ⊤) (by
    show (⊤ : Subgroup G).map φ.toMonoidHom = ⊤; exact map_top_of_surjective _ φ.surjective) hd
    (by rw [map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]; trivial)
  exact ⟨c, hc⟩

/-- A perfect lift of a perfect `φ`-fixed subgroup inside an invariant subgroup. -/
lemma exists_perfect_lift {t : ℕ} {F : Subgroup G} (hF : IsInv φ F)
    {D : Subgroup (G ⧸ lvN G t)} (hDfix : D ≤ fixedSub (lvAut φ t))
    (hDF : D ≤ F.map (QuotientGroup.mk' _)) (hDp : ⁅D, D⁆ = D) :
    ∃ Dh : Subgroup (fixedSub φ), ⁅Dh, Dh⁆ = Dh ∧ Dh.map (rho φ t) = D ∧
      Dh ≤ F.subgroupOf (fixedSub φ) := by
  set Y0 := D.comap (rho φ t) ⊓ F.subgroupOf (fixedSub φ)
  have hY0 : Y0.map (rho φ t) = D := by
    refine le_antisymm ((map_mono inf_le_left).trans (map_comap_le _ _)) fun d hd => ?_
    obtain ⟨c, hcF, hc⟩ := exists_fixed_lift hφ hpG hF (hDfix hd) (hDF hd)
    exact ⟨c, ⟨show rho φ t c ∈ D by rw [hc]; exact hd, hcF⟩, hc⟩
  obtain ⟨n, hn⟩ := exists_perfect_dA Y0
  refine ⟨dA n Y0, hn, ?_, (dA_le n Y0).trans inf_le_right⟩
  rw [map_dA, hY0, dA_eq_self_of_perfect hDp]

end Levels

section Kernel

variable {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime] {φ : MulAut G}

/-- **Lemma 2.1 at level `t`** (Schreier): the kernel of the action of `G` on the components of
`G/M_{t+1}` lies in `M_{t+2}`. -/
lemma kernel_le_upperSeries [Schreier] (hCFSG : TauCeti.ClassificationStatement.{0}) (t : ℕ) :
    (kernelOf (components (G ⧸ lvN G t))).comap (QuotientGroup.mk' _) ≤
      upperSeries G (2 * t + 3) := by
  set Kt := (kernelOf (components (G ⧸ lvN G t))).comap (QuotientGroup.mk' (lvN G t))
  obtain ⟨a, ha⟩ := dA_kernel_le_layer (lvF (G := G) t) hCFSG
  have h1 : dA a Kt ≤ upperSeries G (2 * t + 2) := by
    rw [upperSeries_even]
    intro x hx
    have : (dA a Kt).map (QuotientGroup.mk' (lvN G t)) ≤ layer (G ⧸ lvN G t) := by
      rw [map_dA, map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]; exact ha
    exact this ⟨x, hx, rfl⟩
  haveI : Kt.Normal := Normal.comap inferInstance _
  set L := upperSeries G (2 * t + 2)
  have hle : Kt.map (QuotientGroup.mk' L) ≤ solvableRadical (G ⧸ L) := by
    refine le_solvableRadical
      (Normal.map inferInstance _ (QuotientGroup.mk'_surjective L)) ?_
    rw [isSolvable_subgroup_iff]
    refine ⟨a, ?_⟩
    rw [← map_dA, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact h1
  intro x hx
  rw [show 2 * t + 3 = 2 * (t + 1) + 1 by ring, upperSeries_odd]
  exact hle ⟨x, hx, rfl⟩

/-- **Lemma 3.3**: if `G = [G, φ]` and `G/L_{t+1}` is nonsoluble, then `φ` has a nontrivial orbit
on the components of `G/M_{t+1}`. -/
lemma exists_nontrivial_orbit [Schreier] (hCFSG : TauCeti.ClassificationStatement.{0})
    (hcomm : commSub φ = ⊤) {t : ℕ} (h : upperSeries G (2 * t + 3) ≠ ⊤) :
    ∃ S : Subgroup (G ⧸ lvN G t), IsComponent S ∧ orb (lvAut φ t) S 1 ≠ S := by
  by_contra hall
  push Not at hall
  apply h
  rw [eq_top_iff, ← hcomm]
  refine (closure_le _).2 ?_
  rintro _ ⟨g, rfl⟩
  apply kernel_le_upperSeries hCFSG t
  rw [mem_comap, QuotientGroup.mk'_apply]
  refine mem_kernelOf.2 fun S hS => ?_
  set ψ := lvAut φ t
  set gb : G ⧸ lvN G t := (g : G ⧸ lvN G t)
  have hψg : ((φ g : G) : G ⧸ lvN G t) = ψ gb := rfl
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hψg]
  have hfix : ∀ T : Subgroup (G ⧸ lvN G t), IsComponent T → T.map ψ.toMonoidHom = T := by
    intro T hT
    have := hall T hT
    rwa [orb, pow_one] at this
  apply mem_normalizer_of_conj_mem
  intro s hs
  -- `s = ψ s'` with `s' ∈ S`
  have hsS : s ∈ S.map ψ.toMonoidHom := by rw [hfix S hS]; exact hs
  obtain ⟨s', hs', rfl⟩ := hsS
  set T := S.map (MulAut.conj gb).toMonoidHom
  have hT : IsComponent T := isComponent_map_mulEquiv _ hS
  have hmem : ψ (gb * s' * gb⁻¹) ∈ T := by
    rw [← hfix T hT]; exact ⟨_, ⟨s', hs', rfl⟩, rfl⟩
  obtain ⟨s'', hs'', he⟩ := hmem
  have he' : gb * s'' * gb⁻¹ = ψ (gb * s' * gb⁻¹) := he
  have : gb⁻¹ * ψ gb * ψ s' * (gb⁻¹ * ψ gb)⁻¹ = s'' := by
    have h2 : ψ (gb * s' * gb⁻¹) = ψ gb * ψ s' * (ψ gb)⁻¹ := by simp [map_mul, map_inv]
    rw [h2] at he'
    calc gb⁻¹ * ψ gb * ψ s' * (gb⁻¹ * ψ gb)⁻¹ = gb⁻¹ * (ψ gb * ψ s' * (ψ gb)⁻¹) * gb := by group
      _ = gb⁻¹ * (gb * s'' * gb⁻¹) * gb := by rw [he']
      _ = s'' := by group
  show gb⁻¹ * ψ gb * ψ.toMonoidHom s' * (gb⁻¹ * ψ gb)⁻¹ ∈ S
  rw [MulEquiv.coe_toMonoidHom, this]
  exact hs''

end Kernel

end CFSGOutside.KhukhroShumyatskyFixedPointLength
