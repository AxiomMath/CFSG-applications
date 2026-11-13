import CFSGOutside.KhukhroShumyatskyFactorizedLength.Statement
import CFSGOutside.Common.Components

/-!
# The generalized Fitting height

E. I. Khukhro and P. Shumyatsky, *On the length of finite factorized groups*, Ann. Mat. Pura Appl. (4) **194**
(2015), 1775–1780.

Basic properties of the upper generalized Fitting series `fstarSeries` and of the height `genFittingHeight`
defined in `Statement`: `F*` maps into `F*` under surjections, so the height does not increase in a
quotient (`GenFittingHeightLE.of_surjective`) and drops by one when the kernel contains `F*`
(`GenFittingHeightLE.of_surjective_of_le_ker`); the height of a finite group is finite
(`exists_genFittingHeightLE`).
-/

namespace CFSGOutside.KhukhroShumyatskyFactorizedLength

open Subgroup CFSGOutside.Corpus CFSGOutside.Corpus.LocalCores

section Fitting

/-- A normal nilpotent subgroup of a finite group lies in the product of the `p`-cores. -/
lemma le_iSup_pCore_of_nilpotent {A : Type*} [Group A] [Finite A] (N : Subgroup A) [N.Normal]
    [Group.IsNilpotent N] : N ≤ ⨆ (p : ℕ) (_ : p.Prime), pCore p A := by
  classical
  set Z : Subgroup A := ⨆ (p : ℕ) (_ : p.Prime), pCore p A
  have hSylow : ∀ p : ℕ, p.Prime → ∀ P : Sylow p N, (P : Subgroup N).map N.subtype ≤ Z := by
    intro p hp P
    haveI : Fact p.Prime := ⟨hp⟩
    have hchar : (P : Subgroup N).Characteristic := Sylow.characteristic_of_normal P inferInstance
    haveI : ((P : Subgroup N).map N.subtype).Normal := by
      refine ⟨fun x hx g => ?_⟩
      obtain ⟨y, hy, rfl⟩ := hx
      have hmem : MulAut.conjNormal (H := N) g y ∈ (P : Subgroup N) :=
        (characteristic_iff_map_le.1 hchar) (MulAut.conjNormal (H := N) g)
          ⟨y, hy, rfl⟩
      exact ⟨_, hmem, by simp [MulAut.conjNormal_val]⟩
    have hpg : IsPGroup p ((P : Subgroup N).map N.subtype) :=
      P.isPGroup'.of_equiv ((P : Subgroup N).equivMapOfInjective N.subtype N.subtype_injective)
    exact (le_sSup ⟨inferInstance, hpg⟩ :
        (P : Subgroup N).map N.subtype ≤ pCore p A).trans
      (le_iSup_of_le p (le_iSup_of_le hp le_rfl))
  have hidx : (Z.subgroupOf N).index = 1 := by
    rw [Nat.eq_one_iff_not_exists_prime_dvd]
    intro p hp hdvd
    haveI : Fact p.Prime := ⟨hp⟩
    let P : Sylow p N := default
    have hle : (P : Subgroup N) ≤ Z.subgroupOf N := fun y hy =>
      hSylow p hp P ⟨y, hy, rfl⟩
    exact P.not_dvd_index (hdvd.trans (Subgroup.index_dvd_of_le hle))
  rw [Subgroup.index_eq_one] at hidx
  intro x hx
  have : (⟨x, hx⟩ : N) ∈ Z.subgroupOf N := by rw [hidx]; exact mem_top _
  exact this

/-- The Fitting subgroup of a finite group lies in the product of the `p`-cores. -/
lemma fittingSubgroup_le_iSup_pCore (A : Type*) [Group A] [Finite A] :
    fittingSubgroup A ≤ ⨆ (p : ℕ) (_ : p.Prime), pCore p A :=
  sSup_le fun N hN => by
    haveI := hN.1
    haveI := hN.2
    exact le_iSup_pCore_of_nilpotent N

/-- `F(X)` maps into `F(Y)` under a surjective homomorphism. -/
lemma map_fittingSubgroup_le {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    (hf : Function.Surjective f) : (fittingSubgroup X).map f ≤ fittingSubgroup Y := by
  rw [map_le_iff_le_comap]
  refine sSup_le fun N hN => ?_
  rw [← map_le_iff_le_comap]
  haveI := hN.1
  haveI := hN.2
  exact le_sSup ⟨hN.1.map f hf, Group.nilpotent_of_surjective (f.subgroupMap N)
    (f.subgroupMap_surjective N)⟩

end Fitting

section FStar

variable {X : Type*} [Group X] [Finite X]

/-- `F*(X)` maps into `F*(Y)` under a surjective homomorphism. -/
lemma map_generalizedFitting_le {Y : Type*} [Group Y] [Finite Y] (f : X →* Y)
    (hf : Function.Surjective f) : (generalizedFitting X).map f ≤ generalizedFitting Y := by
  rw [generalizedFitting.eq_sup, generalizedFitting.eq_sup, Subgroup.map_sup]
  refine sup_le ((map_fittingSubgroup_le f hf).trans le_sup_left) (le_trans ?_ le_sup_right)
  rw [map_le_iff_le_comap]
  refine sSup_le fun L hL => ?_
  rw [← map_le_iff_le_comap]
  by_cases hker : L ≤ f.ker
  · rw [(Subgroup.map_eq_bot_iff L).mpr hker]; exact bot_le
  · exact le_sSup (show IsComponent (L.map f) from
      ⟨isQuasisimple_map hL.1 f hker, hL.2.map hf⟩)

instance fstarSeries_normal (n : ℕ) : (fstarSeries X n).Normal := (fstarSeriesN X n).2

lemma fstarSeries_zero : fstarSeries X 0 = ⊥ := rfl

lemma mem_fstarSeries_succ {n : ℕ} {x : X} :
    x ∈ fstarSeries X (n + 1) ↔
      (x : X ⧸ fstarSeries X n) ∈ generalizedFitting (X ⧸ fstarSeries X n) := Iff.rfl

lemma fstarSeries_le_succ (n : ℕ) : fstarSeries X n ≤ fstarSeries X (n + 1) := by
  intro x hx
  rw [mem_fstarSeries_succ, (QuotientGroup.eq_one_iff x).2 hx]
  exact one_mem _

/-- The basic step: a surjection carrying `F*_a(X)` into `F*_b(Y)` carries `F*_{a+1}(X)` into
`F*_{b+1}(Y)`. -/
lemma map_fstarSeries_succ_le {Y : Type*} [Group Y] [Finite Y] (f : X →* Y)
    (hf : Function.Surjective f) {a b : ℕ} (h : (fstarSeries X a).map f ≤ fstarSeries Y b) :
    (fstarSeries X (a + 1)).map f ≤ fstarSeries Y (b + 1) := by
  let φ : X ⧸ fstarSeries X a →* Y ⧸ fstarSeries Y b :=
    QuotientGroup.map _ _ f (map_le_iff_le_comap.1 h)
  have hφ : Function.Surjective φ := by
    intro z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨x, rfl⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_fstarSeries_succ]
  exact map_generalizedFitting_le φ hφ ⟨_, hx, rfl⟩

lemma map_fstarSeries_le {Y : Type*} [Group Y] [Finite Y] (f : X →* Y)
    (hf : Function.Surjective f) (n : ℕ) : (fstarSeries X n).map f ≤ fstarSeries Y n := by
  induction n with
  | zero => rw [fstarSeries_zero, fstarSeries_zero, Subgroup.map_bot]
  | succ n ih => exact map_fstarSeries_succ_le f hf ih

lemma fstarSeries_one_le : fstarSeries X 1 ≤ generalizedFitting X := by
  intro x hx
  have := map_generalizedFitting_le (QuotientGroup.quotientBot (G := X)).toMonoidHom
    (MulEquiv.surjective _) ⟨_, hx, rfl⟩
  exact this

lemma map_fstarSeries_succ_le_of_le_ker {Y : Type*} [Group Y] [Finite Y] (f : X →* Y)
    (hf : Function.Surjective f) (hker : generalizedFitting X ≤ f.ker) (n : ℕ) :
    (fstarSeries X (n + 1)).map f ≤ fstarSeries Y n := by
  induction n with
  | zero =>
    rw [fstarSeries_zero, le_bot_iff, Subgroup.map_eq_bot_iff]
    exact fstarSeries_one_le.trans hker
  | succ n ih => exact map_fstarSeries_succ_le f hf ih

lemma GenFittingHeightLE.of_surjective {Y : Type*} [Group Y] [Finite Y] {f : X →* Y}
    (hf : Function.Surjective f) {h : ℕ} (H : GenFittingHeightLE X h) : GenFittingHeightLE Y h := by
  have := map_fstarSeries_le f hf h
  rw [H, map_top_of_surjective f hf, top_le_iff] at this
  exact this

lemma GenFittingHeightLE.of_surjective_of_le_ker {Y : Type*} [Group Y] [Finite Y] {f : X →* Y}
    (hf : Function.Surjective f) (hker : generalizedFitting X ≤ f.ker) {h : ℕ}
    (H : GenFittingHeightLE X (h + 1)) : GenFittingHeightLE Y h := by
  have := map_fstarSeries_succ_le_of_le_ker f hf hker h
  rw [H, map_top_of_surjective f hf, top_le_iff] at this
  exact this

lemma subsingleton_of_genFittingHeightLE_zero (H : GenFittingHeightLE X 0) : Subsingleton X := by
  refine ⟨fun a b => ?_⟩
  have ha : a ∈ fstarSeries X 0 := H ▸ mem_top a
  have hb : b ∈ fstarSeries X 0 := H ▸ mem_top b
  rw [fstarSeries_zero, mem_bot] at ha hb
  rw [ha, hb]

/-- A nontrivial finite group has a nontrivial generalized Fitting subgroup. -/
lemma generalizedFitting_ne_bot [Nontrivial X] : generalizedFitting X ≠ ⊥ := by
  intro h
  rw [generalizedFitting.eq_sup, sup_eq_bot_iff] at h
  have hlayer := centralizer_layer_eq_bot h.1
  rw [h.2] at hlayer
  obtain ⟨x, hx⟩ := exists_ne (1 : X)
  apply hx
  refine mem_bot.1 (hlayer.le ?_)
  rw [mem_centralizer_iff]
  intro g hg
  rw [SetLike.mem_coe, mem_bot] at hg
  simp [hg]

lemma fstarSeries_lt_succ {n : ℕ} (hn : fstarSeries X n ≠ ⊤) :
    fstarSeries X n < fstarSeries X (n + 1) := by
  refine lt_of_le_of_ne (fstarSeries_le_succ n) fun heq => ?_
  haveI : Nontrivial (X ⧸ fstarSeries X n) := QuotientGroup.nontrivial_iff.2 hn
  obtain ⟨⟨y, hy⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one.1
    (generalizedFitting_ne_bot (X := X ⧸ fstarSeries X n)))
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  have hx : x ∈ fstarSeries X (n + 1) := hy
  rw [← heq] at hx
  exact hy1 (Subtype.ext ((QuotientGroup.eq_one_iff x).2 hx))

/-- The generalized Fitting height of a finite group is finite. -/
lemma exists_genFittingHeightLE : ∃ h, GenFittingHeightLE X h := by
  by_contra hcon
  push Not at hcon
  have key : ∀ n, n ≤ Nat.card (fstarSeries X n) := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih =>
      exact Nat.succ_le_of_lt (ih.trans_lt (Subgroup.card_lt_of_lt (fstarSeries_lt_succ (hcon n))))
  have h1 := key (Nat.card X + 1)
  have h2 := Subgroup.card_le_card_group (fstarSeries X (Nat.card X + 1))
  omega

lemma genFittingHeightLE_genFittingHeight : GenFittingHeightLE X (genFittingHeight X) :=
  Nat.sInf_mem exists_genFittingHeightLE

end FStar

end CFSGOutside.KhukhroShumyatskyFactorizedLength
