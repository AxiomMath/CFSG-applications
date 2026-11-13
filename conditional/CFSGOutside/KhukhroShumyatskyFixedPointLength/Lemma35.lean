import CFSGOutside.KhukhroShumyatskyFixedPointLength.Levels

/-!
# Khukhro–Shumyatsky, fixed points: Lemma 3.5

E. I. Khukhro and P. Shumyatsky, *On the length of finite groups and of fixed points*, Proc. Amer. Math. Soc.
**143** (2015), 3781–3790. Lemma 3.5 (`lemma35`): a nontrivial orbit at level `t+1` gives a perfect lift of its
diagonal and a nontrivial orbit at level `t` whose diagonal the lift moves to a different orbit.
-/

namespace CFSGOutside.KhukhroShumyatskyFixedPointLength

open Subgroup CFSGOutside.Corpus CFSGOutside.Corpus.LocalCores
open CFSGOutside.NonsolubleLength CFSGOutside.UpperNonsolubleSeries
open scoped commutatorElement

section Aux

variable {Q : Type} [Group Q] [Finite Q]

lemma conj_map_map (R : Subgroup Q) (a b : Q) :
    (R.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      R.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [map_map, conj_comp_conj]

/-- If `χ` fixes the component `R`, `x` normalizes `R`, then `χ x` normalizes `R`. -/
lemma aut_mem_normalizer {χ : MulAut Q} {R : Subgroup Q} (hR : R.map χ.toMonoidHom = R)
    {x : Q} (hx : x ∈ normalizer (R : Set Q)) : χ x ∈ normalizer (R : Set Q) := by
  apply mem_normalizer_of_conj_mem
  intro r hr
  have : r ∈ R.map χ.toMonoidHom := by rw [hR]; exact hr
  obtain ⟨r', hr', rfl⟩ := this
  have h1 : x * r' * x⁻¹ ∈ R := (mem_normalizer_iff.1 hx r').1 hr'
  have : χ x * χ.toMonoidHom r' * (χ x)⁻¹ = χ.toMonoidHom (x * r' * x⁻¹) := by
    simp [map_mul, map_inv]
  rw [this, ← hR]
  exact ⟨_, h1, rfl⟩

/-- If `χ` fixes `R` and `y R y⁻¹`, then `y⁻¹ χ(y)` normalizes `R`. -/
lemma inv_mul_aut_mem_normalizer {χ : MulAut Q} {R : Subgroup Q} (hR : R.map χ.toMonoidHom = R)
    {y : Q} (hT : (R.map (MulAut.conj y).toMonoidHom).map χ.toMonoidHom =
      R.map (MulAut.conj y).toMonoidHom) : y⁻¹ * χ y ∈ normalizer (R : Set Q) := by
  apply mem_normalizer_of_conj_mem
  intro r hr
  have : r ∈ R.map χ.toMonoidHom := by rw [hR]; exact hr
  obtain ⟨r', hr', rfl⟩ := this
  have hmem : χ.toMonoidHom (y * r' * y⁻¹) ∈ R.map (MulAut.conj y).toMonoidHom := by
    rw [← hT]; exact ⟨_, ⟨r', hr', rfl⟩, rfl⟩
  obtain ⟨r'', hr'', he⟩ := hmem
  have he' : y * r'' * y⁻¹ = χ (y * r' * y⁻¹) := he
  have h2 : χ (y * r' * y⁻¹) = χ y * χ r' * (χ y)⁻¹ := by simp [map_mul, map_inv]
  rw [h2] at he'
  have : y⁻¹ * χ y * χ.toMonoidHom r' * (y⁻¹ * χ y)⁻¹ = r'' := by
    calc y⁻¹ * χ y * χ.toMonoidHom r' * (y⁻¹ * χ y)⁻¹ = y⁻¹ * (χ y * χ r' * (χ y)⁻¹) * y := by
          simp only [MulEquiv.coe_toMonoidHom]; group
      _ = y⁻¹ * (y * r'' * y⁻¹) * y := by rw [he']
      _ = r'' := by group
  rw [this]; exact hr''

lemma coprime_orderOf_of_not_dvd {p : ℕ} [hp : Fact p.Prime] (hpQ : ¬ p ∣ Nat.card Q) (x : Q) :
    (orderOf x).Coprime p :=
  Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).2 fun h =>
    hpQ (h.trans (orderOf_dvd_natCard x)))

end Aux

section Lemma35

variable {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime] {φ : MulAut G}
  [hsch : Schreier] (hCFSG : TauCeti.ClassificationStatement.{0}) (hφ : φ ^ p = 1) (hpG : ¬ p ∣ Nat.card G)
include hsch hCFSG hφ hpG

/-- **Lemma 3.5 (Khukhro–Shumyatsky)**.  For a nontrivial `φ`-orbit at level `t+1` there is a
perfect subgroup `D̂ ≤ C_G(φ)` covering its diagonal, an element `x ∈ D̂` and a nontrivial
`φ`-orbit at level `t` that `x` does not stabilize. -/
theorem lemma35 (hp3 : 3 ≤ p) {t : ℕ} {S : Subgroup (G ⧸ lvN G (t + 1))} (hS : IsComponent S)
    (hnt : orb (lvAut φ (t + 1)) S 1 ≠ S) :
    ∃ Dh : Subgroup (fixedSub φ), ⁅Dh, Dh⁆ = Dh ∧
      Dh.map (rho φ (t + 1)) = diag (lvAut_pow hφ (t + 1)) hS hnt ∧
      ∃ x ∈ Dh, ∃ R : Subgroup (G ⧸ lvN G t), ∃ hR : IsComponent R,
        ∃ hRnt : orb (lvAut φ t) R 1 ≠ R,
          ∀ k < p, orb (lvAut φ t) R k ≠ R.map (MulAut.conj (rho φ t x)).toMonoidHom := by
  set ψ := lvAut φ (t + 1)
  set χ := lvAut φ t
  have hψ : ψ ^ p = 1 := lvAut_pow hφ (t + 1)
  have hχ : χ ^ p = 1 := lvAut_pow hφ t
  set π1 := QuotientGroup.mk' (lvN G (t + 1))
  set π0 := QuotientGroup.mk' (lvN G t)
  set D := diag hψ hS hnt
  -- the orbit product
  set Sp : Subgroup (G ⧸ lvN G (t + 1)) := ⨆ k : Fin p, orb ψ S k
  have horb_le : ∀ k < p, orb ψ S k ≤ Sp := fun k hk => le_iSup (fun k : Fin p => orb ψ S k) ⟨k, hk⟩
  have hSp_inv : ∀ x ∈ Sp, ψ x ∈ Sp := by
    have : Sp ≤ Sp.comap ψ.toMonoidHom := by
      refine iSup_le fun k => ?_
      rw [← map_le_iff_le_comap]
      have : (orb ψ S k).map ψ.toMonoidHom = orb ψ S (1 + k) := by rw [orb_add, pow_one]
      rw [this, orb_mod hψ]
      exact horb_le _ (Nat.mod_lt _ hp.out.pos)
    exact fun x hx => this hx
  have hDSp : D ≤ Sp := by
    rintro _ ⟨a, rfl⟩
    rw [deltaHom_apply]
    refine Sp.list_prod_mem fun y hy => ?_
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hy
    exact horb_le i (List.mem_range.1 hi) (mem_orb_of_mem ψ a.2 i)
  -- a minimal invariant subgroup covering the orbit product
  have hcand : ∃ n, ∃ F : Subgroup G, IsInv φ F ∧ F.map π1 = Sp ∧ Nat.card F = n := by
    refine ⟨_, Sp.comap π1, isInv_of_forall fun x hx => ?_,
      map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _, rfl⟩
    exact hSp_inv _ hx
  classical
  obtain ⟨Sh, hShinv, hShSp, hShcard⟩ := Nat.find_spec hcand
  have hmin : ∀ F : Subgroup G, IsInv φ F → F.map π1 = Sp → ¬ F < Sh := by
    intro F hF hFS hlt
    have := Nat.find_min' hcand ⟨F, hF, hFS, rfl⟩
    have h2 := Subgroup.card_lt_of_lt hlt
    omega
  -- the perfect lift
  obtain ⟨Dh, hDhp, hDhD, hDhSh⟩ := exists_perfect_lift hφ hpG hShinv
    (diag_le_fixedSub hψ hS hnt) (by rw [hShSp]; exact hDSp) (diag_perfect hψ hS hnt)
  refine ⟨Dh, hDhp, hDhD, ?_⟩
  by_contra hcon
  push Not at hcon
  -- every element of `Dh` fixes every component in a nontrivial orbit at level `t`
  have hfix : ∀ x ∈ Dh, ∀ R : Subgroup (G ⧸ lvN G t), IsComponent R → orb χ R 1 ≠ R →
      R.map (MulAut.conj (rho φ t x)).toMonoidHom = R := by
    intro x hx R hR hRnt
    obtain ⟨k, hk, hkR⟩ := hcon x hx R hR hRnt
    exact conj_eq_of_mem_orb hχ hR hRnt (rho_mem_fixed φ t x)
      (coprime_orderOf_of_not_dvd (not_dvd_card_quotient hpG _) _) hk hkR.symm
  -- some element of `Dh` moves a component at level `t`
  obtain ⟨d, hd, hdK⟩ : ∃ d ∈ Dh, rho φ t d ∉ kernelOf (components (G ⧸ lvN G t)) := by
    by_contra hall
    push Not at hall
    apply diag_ne_bot hψ hS hnt (lvF (G := G) (t + 1))
    rw [← hDhD, eq_bot_iff]
    rintro _ ⟨e, he, rfl⟩
    rw [mem_bot, ← MonoidHom.mem_ker, ker_rho, mem_subgroupOf]
    have h1 := kernel_le_upperSeries hCFSG t (show (e : G) ∈ _ from hall e he)
    rwa [show 2 * t + 3 = 2 * (t + 1) + 1 by ring] at h1
  obtain ⟨R0, hR0, hdR0⟩ : ∃ R0 ∈ components (G ⧸ lvN G t), rho φ t d ∉ normalizer (R0 : Set _) := by
    by_contra hall
    push Not at hall
    exact hdK (mem_kernelOf.2 hall)
  have hR0fix : R0.map χ.toMonoidHom = R0 := by
    by_contra hne
    have hRnt : orb χ R0 1 ≠ R0 := by rwa [orb, pow_one]
    exact hdR0 (mem_normalizer_of_map_conj_eq (hfix d hd R0 hR0 hRnt))
  -- the stabilizer of `R0` in `Sh`
  set HS : Subgroup G := Sh ⊓ (normalizer (R0 : Set _)).comap π0
  have hHSinv : IsInv φ HS := isInv_of_forall fun y hy =>
    ⟨hShinv.mem hy.1, aut_mem_normalizer hR0fix hy.2⟩
  have hHSlt : HS < Sh := by
    refine lt_of_le_of_ne inf_le_left fun heq => hdR0 ?_
    have hdSh : (d : G) ∈ Sh := hDhSh hd
    rw [← heq] at hdSh
    exact hdSh.2
  apply hmin HS hHSinv ?_ hHSlt
  -- `HS` still covers the orbit product
  set Hb := HS.map π1
  have hHbinv : ∀ h ∈ Hb, ψ h ∈ Hb := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨φ y, hHSinv.mem hy, rfl⟩
  have hSHb : S ≤ Hb := by
    refine le_of_star hψ hS hnt (lvF (G := G) (t + 1)) hp3 hHbinv fun c hcS hcH a ha => ?_
    obtain ⟨y, hySh, rfl⟩ : c ∈ Sh.map π1 := by rw [hShSp]; exact horb_le 0 hp.out.pos (by rwa [orb_zero])
    have hyφ : y⁻¹ * φ y ∉ HS := by
      intro hmem
      apply hcH
      exact ⟨_, hmem, by simp [π1, ψ, lvAut_mk]⟩
    have hyφ' : π0 (y⁻¹ * φ y) ∉ normalizer (R0 : Set _) := fun h =>
      hyφ ⟨Sh.mul_mem (Sh.inv_mem hySh) (hShinv.mem hySh), h⟩
    set yb := π0 y
    have hTnt : orb χ (R0.map (MulAut.conj yb).toMonoidHom) 1 ≠ R0.map (MulAut.conj yb).toMonoidHom := by
      intro h
      apply hyφ'
      rw [orb, pow_one] at h
      have := inv_mul_aut_mem_normalizer hR0fix h
      simpa [π0, yb, χ, lvAut_mk] using this
    have hTcomp : IsComponent (R0.map (MulAut.conj yb).toMonoidHom) :=
      isComponent_map_mulEquiv _ hR0
    -- `δ(a) = π1 e` with `e ∈ Dh`
    have hda : deltaFun ψ p a ∈ Dh.map (rho φ (t + 1)) := by
      rw [hDhD]; exact ⟨⟨a, ha⟩, rfl⟩
    obtain ⟨e, he, hea⟩ := hda
    have heT := hfix e he _ hTcomp hTnt
    have hen : yb⁻¹ * rho φ t e * yb ∈ normalizer (R0 : Set _) := by
      apply mem_normalizer_of_map_conj_eq
      have := congrArg (fun H => H.map (MulAut.conj yb⁻¹).toMonoidHom) heT
      simp only [conj_map_map] at this
      rw [show yb⁻¹ * (rho φ t e * yb) = yb⁻¹ * rho φ t e * yb by group, inv_mul_cancel,
        show (MulAut.conj (1 : G ⧸ lvN G t)).toMonoidHom = MonoidHom.id _ by ext; simp,
        map_id] at this
      exact this
    have hyey : y⁻¹ * (e : G) * y ∈ HS := by
      refine ⟨Sh.mul_mem (Sh.mul_mem (Sh.inv_mem hySh) (hDhSh he)) hySh, ?_⟩
      show π0 (y⁻¹ * (e : G) * y) ∈ normalizer (R0 : Set _)
      simpa [π0, yb, rho_apply] using hen
    refine ⟨_, hyey, ?_⟩
    rw [← hea]
    simp [π1, rho_apply]
  refine le_antisymm ?_ ?_
  · rw [← hShSp]; exact map_mono inf_le_left
  · refine iSup_le fun k => ?_
    have := map_mono (f := (ψ ^ (k : ℕ)).toMonoidHom) hSHb
    refine this.trans ?_
    rintro _ ⟨h, hh, rfl⟩
    induction (k : ℕ) generalizing h with
    | zero => simpa using hh
    | succ n ih =>
      rw [pow_succ', MulEquiv.coe_toMonoidHom, MulAut.mul_apply]
      exact hHbinv _ (by simpa using ih h hh)

end Lemma35

end CFSGOutside.KhukhroShumyatskyFixedPointLength
