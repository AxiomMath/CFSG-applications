import CFSGOutside.HallPaige.Statements
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Double coset criteria for complete mappings

Wilcox's double coset criteria (Wilcox 2009, Corollaries 15 and 16; Evans 2009, Lemmas 3, 4),
derived from the coset criterion `CosetStatement` (Wilcox, Proposition 14), which is taken as a
hypothesis `hcos` throughout.

## Main results

* `CFSGOutside.HallPaige.exists_equiv_quotient_common_rep`: subgroups of equal order have a common left
  transversal (via Hall's marriage theorem).
* `CFSGOutside.HallPaige.hasCompleteMapping_of_doubleCoset_perms`: Wilcox, Corollary 15.
* `CFSGOutside.HallPaige.hasCompleteMapping_of_wilcoxCriterion`: `WilcoxCriterion` plus admissibility of
  proper good subgroups gives a complete mapping.
* `CFSGOutside.HallPaige.hasCompleteMapping_of_forall_sq_mem`, `CFSGOutside.HallPaige.hasCompleteMapping_of_forall_mul_mem`:
  Wilcox, Corollary 16.
* `CFSGOutside.HallPaige.hasCompleteMapping_of_triangle`, `CFSGOutside.HallPaige.wilcoxCriterion_of_triangle`: the form
  `ψ D ∈ {D, D⁻¹}`.
* `CFSGOutside.HallPaige.wilcoxCriterion_of_labelling`, `CFSGOutside.HallPaige.wilcoxCriterion_of_labelling_sq`,
  `CFSGOutside.HallPaige.wilcoxCriterion_of_permLabelling`: forms for transitive actions with labelled
  suborbits, suitable for certificates.
* `CFSGOutside.HallPaige.hasCompleteMapping_of_two_doubleCosets`,
  `CFSGOutside.HallPaige.hasCompleteMapping_of_card_doubleCoset_le_two`,
  `CFSGOutside.HallPaige.hasCompleteMapping_of_two_transitive`: Evans, Lemma 4 and the 2-transitive case.

## Implementation notes

Instead of the formula `|HxH| = |H|² / |H ∩ xHx⁻¹|`, the left cosets inside `HxH` are identified
with the `H`-orbit of `xH` in `G ⧸ H` (`CFSGOutside.HallPaige.cosetsInEquivOrbit`), so that
`|HxH| = |H| · #(left cosets in HxH)` and the stabilizer of `xH` in `H` is `H ∩ xHx⁻¹`.
-/

namespace CFSGOutside.HallPaige

universe u

open DoubleCoset

section Transversal

variable {K : Type*} [Group K]

/-- The preimage of a set of left cosets has `|A|` times as many elements. -/
theorem card_preimage_mk_eq (A : Subgroup K) (t : Set (K ⧸ A)) :
    Nat.card (QuotientGroup.mk ⁻¹' t : Set K) = Nat.card A * Nat.card t := by
  rw [Nat.card_congr (QuotientGroup.preimageMkEquivSubgroupProdSet A t), Nat.card_prod]

/-- **Common left transversals.** Two subgroups `A`, `B` of a finite group `K` of the same order
have a common left transversal; phrased as a bijection `K ⧸ A ≃ K ⧸ B` in which each coset and
its image share a representative. -/
theorem exists_equiv_quotient_common_rep [Finite K] (A B : Subgroup K)
    (hAB : Nat.card A = Nat.card B) :
    ∃ f : K ⧸ A ≃ K ⧸ B, ∀ c, ∃ h : K, (h : K ⧸ A) = c ∧ (h : K ⧸ B) = f c := by
  classical
  have := Fintype.ofFinite K
  let t : K ⧸ A → Finset (K ⧸ B) := fun c =>
    (Finset.univ.filter fun h : K => (QuotientGroup.mk h : K ⧸ A) = c).image
      fun h => (QuotientGroup.mk h : K ⧸ B)
  have hpos : 0 < Nat.card B := Nat.card_pos
  obtain ⟨f, hf, hft⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).1 <| by
    intro s
    have hsub : (QuotientGroup.mk ⁻¹' (s : Set (K ⧸ A)) : Set K) ⊆
        QuotientGroup.mk ⁻¹' ((s.biUnion t : Finset (K ⧸ B)) : Set (K ⧸ B)) := by
      intro h hh
      simp only [Set.mem_preimage, Finset.mem_coe, Finset.mem_biUnion] at hh ⊢
      exact ⟨_, hh, Finset.mem_image.2 ⟨h, by simp, rfl⟩⟩
    have := Nat.card_mono (Set.toFinite _) hsub
    rw [card_preimage_mk_eq, card_preimage_mk_eq, Nat.card_eq_card_toFinset, Nat.card_eq_card_toFinset,
      hAB] at this
    simpa using Nat.le_of_mul_le_mul_left this hpos
  have hcard : Nat.card (K ⧸ A) = Nat.card (K ⧸ B) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup A
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup B
    rw [hAB] at h1
    exact Nat.eq_of_mul_eq_mul_right hpos (h1.symm.trans h2)
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hf, ?_⟩
    simpa [Nat.card_eq_fintype_card] using hcard
  refine ⟨Equiv.ofBijective f hbij, fun c => ?_⟩
  obtain ⟨h, hh, hfh⟩ := Finset.mem_image.1 (hft c)
  exact ⟨h, (Finset.mem_filter.1 hh).2, hfh⟩

end Transversal

section Main

variable {G : Type u} [Group G] (H : Subgroup G)

/-- The double coset `HgH` containing a left coset `gH`. -/
def cosetToDouble : G ⧸ H → Quotient (H : Set G) H :=
  fun c => Quotient.liftOn' c (mk H H) fun a b hab => by
    have hk : a⁻¹ * b ∈ H := QuotientGroup.leftRel_apply.1 hab
    have : b = a * (a⁻¹ * b) := by group
    rw [this, mk_mul_mem ⟨_, hk⟩ a]

@[simp]
theorem cosetToDouble_mk (g : G) : cosetToDouble H (g : G ⧸ H) = mk H H g := rfl

/-- The left cosets contained in the double coset `q`. -/
abbrev CosetsIn (q : Quotient (H : Set G) H) : Type u := {c : G ⧸ H // cosetToDouble H c = q}

theorem quotToDoubleCoset_eq_preimage (q : Quotient (H : Set G) H) :
    quotToDoubleCoset H H q = QuotientGroup.mk ⁻¹' {c : G ⧸ H | cosetToDouble H c = q} := by
  ext g
  simp [mem_quotToDoubleCoset_iff]

/-- `|HgH| = |H| · #{left cosets in HgH}`. -/
theorem card_quotToDoubleCoset (q : Quotient (H : Set G) H) :
    Nat.card (quotToDoubleCoset H H q) = Nat.card H * Nat.card (CosetsIn H q) := by
  rw [quotToDoubleCoset_eq_preimage, card_preimage_mk_eq]
  rfl

theorem card_cosetsIn_eq_iff [Finite G] {q q' : Quotient (H : Set G) H} :
    Nat.card (CosetsIn H q) = Nat.card (CosetsIn H q') ↔
      Nat.card (quotToDoubleCoset H H q) = Nat.card (quotToDoubleCoset H H q') := by
  rw [card_quotToDoubleCoset, card_quotToDoubleCoset]
  exact (Nat.mul_right_inj (Nat.card_pos (α := H)).ne').symm

theorem mem_orbit_iff_cosetToDouble (a : G) (c : G ⧸ H) :
    c ∈ MulAction.orbit H (a : G ⧸ H) ↔ cosetToDouble H c = mk H H a := by
  induction c using QuotientGroup.induction_on with
  | H g =>
  rw [cosetToDouble_mk, eq_comm, DoubleCoset.eq]
  constructor
  · rintro ⟨h, hh⟩
    change ((h * a : G) : G ⧸ H) = g at hh
    rw [QuotientGroup.eq] at hh
    exact ⟨h, h.2, _, hh, by group⟩
  · rintro ⟨h, hh, k, hk, rfl⟩
    refine ⟨⟨h, hh⟩, ?_⟩
    change ((h * a : G) : G ⧸ H) = _
    rw [QuotientGroup.eq]
    simpa [mul_assoc] using hk

/-- The left cosets in `HaH` form the `H`-orbit of `aH`. -/
def cosetsInEquivOrbit {q : Quotient (H : Set G) H} {a : G} (ha : mk H H a = q) :
    CosetsIn H q ≃ MulAction.orbit H (a : G ⧸ H) :=
  Equiv.subtypeEquivRight fun c => by rw [mem_orbit_iff_cosetToDouble, ha]

theorem card_orbit_mul_card_stabilizer (a : G) [Finite G] :
    Nat.card (MulAction.orbit H (a : G ⧸ H)) * Nat.card (MulAction.stabilizer H (a : G ⧸ H)) =
      Nat.card H := by
  rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer H (a : G ⧸ H)),
    ← Subgroup.card_eq_card_quotient_mul_card_subgroup]

/-- If `HaH` and `HzH` contain equally many left cosets, there is a bijection between these
left cosets of the form `haH ↦ hzH`. -/
theorem exists_cosetsIn_equiv [Finite G] {q₁ q₂ : Quotient (H : Set G) H} {a z : G}
    (ha : mk H H a = q₁) (hz : mk H H z = q₂)
    (hcard : Nat.card (CosetsIn H q₁) = Nat.card (CosetsIn H q₂)) :
    ∃ e : CosetsIn H q₁ ≃ CosetsIn H q₂, ∀ c : CosetsIn H q₁, ∃ h : H,
      (c : G ⧸ H) = ((h * a : G) : G ⧸ H) ∧ (e c : G ⧸ H) = ((h * z : G) : G ⧸ H) := by
  let ea := cosetsInEquivOrbit H ha
  let ez := cosetsInEquivOrbit H hz
  have hO : Nat.card (MulAction.orbit H (a : G ⧸ H)) = Nat.card (MulAction.orbit H (z : G ⧸ H)) := by
    rw [← Nat.card_congr ea, ← Nat.card_congr ez, hcard]
  have hS : Nat.card (MulAction.stabilizer H (a : G ⧸ H)) =
      Nat.card (MulAction.stabilizer H (z : G ⧸ H)) := by
    have h1 := card_orbit_mul_card_stabilizer H a
    have h2 := card_orbit_mul_card_stabilizer H z
    rw [hO] at h1
    have hpos : 0 < Nat.card (MulAction.orbit H (z : G ⧸ H)) := Nat.card_pos_iff.2
      ⟨⟨⟨_, MulAction.mem_orbit_self _⟩⟩, inferInstance⟩
    exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)
  obtain ⟨f, hf⟩ := exists_equiv_quotient_common_rep _ _ hS
  let oa := MulAction.orbitEquivQuotientStabilizer H (a : G ⧸ H)
  let oz := MulAction.orbitEquivQuotientStabilizer H (z : G ⧸ H)
  refine ⟨ea.trans (oa.trans (f.trans (oz.symm.trans ez.symm))), fun c => ?_⟩
  obtain ⟨h, h1, h2⟩ := hf (oa (ea c))
  refine ⟨h, ?_, ?_⟩
  · have : (ea c : G ⧸ H) = ((oa.symm (oa (ea c)) : MulAction.orbit H (a : G ⧸ H)) : G ⧸ H) := by
      rw [Equiv.symm_apply_apply]
    rw [← h1, MulAction.orbitEquivQuotientStabilizer_symm_apply, Subgroup.smul_def,
      MulAction.Quotient.smul_mk] at this
    exact this
  · simp only [Equiv.trans_apply]
    rw [← h2]
    change ((oz.symm h : MulAction.orbit H (z : G ⧸ H)) : G ⧸ H) = _
    rw [MulAction.orbitEquivQuotientStabilizer_symm_apply]
    rfl

end Main

section Criterion

variable {G : Type u} [Group G] [Finite G]

/-- **Wilcox, Corollary 15.** Let `H ≤ G` have a complete mapping, and let `φ`, `ψ` be
size-preserving permutations of the double cosets `H \ G / H` with `ψ D ⊆ D * φ D` for every
double coset `D` (phrased with representatives: some `a ∈ D`, `b ∈ φ D` have `a * b ∈ ψ D`;
since `D * φ D` is a union of double cosets this is equivalent). Then `G` has a complete
mapping. -/
theorem hasCompleteMapping_of_doubleCoset_perms (hcos : CosetStatement.{u}) (H : Subgroup G)
    (hH : HasCompleteMapping H) (φ ψ : Quotient (H : Set G) H ≃ Quotient (H : Set G) H)
    (hφ : ∀ q, Nat.card (quotToDoubleCoset H H (φ q)) = Nat.card (quotToDoubleCoset H H q))
    (hψ : ∀ q, Nat.card (quotToDoubleCoset H H (ψ q)) = Nat.card (quotToDoubleCoset H H q))
    (hmul : ∀ q, ∃ a b : G, mk H H a = q ∧ mk H H b = φ q ∧ mk H H (a * b) = ψ q) :
    HasCompleteMapping G := by
  choose a b ha hb hab using hmul
  have hY : ∀ q, Nonempty (CosetsIn H q ≃ CosetsIn H (φ q)) := fun q =>
    Finite.card_eq.1 ((card_cosetsIn_eq_iff H).2 (hφ q).symm)
  let Y := fun q => (hY q).some
  have hZ : ∀ q, ∃ e : CosetsIn H q ≃ CosetsIn H (ψ q), ∀ c : CosetsIn H q, ∃ h : H,
      (c : G ⧸ H) = ((h * a q : G) : G ⧸ H) ∧ (e c : G ⧸ H) = ((h * (a q * b q) : G) : G ⧸ H) :=
    fun q => exists_cosetsIn_equiv H (ha q) (hab q) ((card_cosetsIn_eq_iff H).2 (hψ q).symm)
  choose Z hZ using hZ
  let x : (Σ q, CosetsIn H q) ≃ G ⧸ H := Equiv.sigmaFiberEquiv (cosetToDouble H)
  let y : (Σ q, CosetsIn H q) ≃ G ⧸ H :=
    (Equiv.sigmaCongrRight Y).trans ((Equiv.sigmaCongrLeft φ).trans x)
  let z : (Σ q, CosetsIn H q) ≃ G ⧸ H :=
    (Equiv.sigmaCongrRight Z).trans ((Equiv.sigmaCongrLeft ψ).trans x)
  refine hcos H hH x y z ?_
  rintro ⟨q, c⟩
  obtain ⟨h, hc, hzc⟩ := hZ q c
  have hxv : x ⟨q, c⟩ = c := rfl
  have hyv : y ⟨q, c⟩ = Y q c := rfl
  have hzv : z ⟨q, c⟩ = Z q c := rfl
  rw [hxv, hyv, hzv]
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (Y q c : G ⧸ H)
  have hgq : mk H H (b q) = mk H H g := by
    rw [hb, ← (Y q c).2, ← hg, cosetToDouble_mk]
  obtain ⟨k, hk, k', hk', rfl⟩ := DoubleCoset.eq.1 hgq
  refine ⟨h * a q * k⁻¹, k * b q * k', ?_, hg, ?_⟩
  · rw [hc, QuotientGroup.eq]
    simpa [mul_assoc] using H.inv_mem hk
  · rw [hzc, QuotientGroup.eq]
    simpa [mul_assoc] using H.inv_mem hk'

/-- **Wilcox–Evans criterion.** A group satisfying `WilcoxCriterion` all of whose proper good
subgroups have complete mappings has a complete mapping. -/
theorem hasCompleteMapping_of_wilcoxCriterion (hcos : CosetStatement.{u})
    (hW : WilcoxCriterion G) (hP : ProperSubgroupsAdmissible G) : HasCompleteMapping G := by
  obtain ⟨H, hne, hgood, ψ, hψ, hmul⟩ := hW
  exact hasCompleteMapping_of_doubleCoset_perms hcos H (hP H hne hgood) (Equiv.refl _) ψ
    (fun _ => rfl) hψ hmul

/-- **Wilcox, Corollary 16** (Evans, Lemma 3). If `H ≤ G` has a complete mapping and every double
coset `D` of `H` contains some `g` with `g * g ∈ D`, then `G` has a complete mapping. -/
theorem hasCompleteMapping_of_forall_sq_mem (hcos : CosetStatement.{u}) (H : Subgroup G)
    (hH : HasCompleteMapping H) (hsq : ∀ q : Quotient (H : Set G) H, ∃ g : G,
      mk H H g = q ∧ mk H H (g * g) = q) : HasCompleteMapping G :=
  hasCompleteMapping_of_doubleCoset_perms hcos H hH (Equiv.refl _) (Equiv.refl _)
    (fun _ => rfl) (fun _ => rfl) fun q => by
      obtain ⟨g, hg, hgg⟩ := hsq q
      exact ⟨g, g, hg, hg, hgg⟩

/-- Corollary 16 in the form `D ⊆ D * D`: some `a, b ∈ D` have `a * b ∈ D`. -/
theorem hasCompleteMapping_of_forall_mul_mem (hcos : CosetStatement.{u}) (H : Subgroup G)
    (hH : HasCompleteMapping H) (hD : ∀ q : Quotient (H : Set G) H, ∃ a b : G,
      mk H H a = q ∧ mk H H b = q ∧ mk H H (a * b) = q) : HasCompleteMapping G :=
  hasCompleteMapping_of_doubleCoset_perms hcos H hH (Equiv.refl _) (Equiv.refl _)
    (fun _ => rfl) (fun _ => rfl) hD

end Criterion

section Inverse

variable {G : Type u} [Group G] (H : Subgroup G)

/-- Inversion of double cosets: `HgH ↦ Hg⁻¹H`. -/
def invDoubleCoset (q : Quotient (H : Set G) H) : Quotient (H : Set G) H :=
  Quotient.liftOn' q (fun g => mk H H g⁻¹) fun x y hxy => by
    obtain ⟨h, hh, k, hk, rfl⟩ := DoubleCoset.rel_iff.1 hxy
    exact DoubleCoset.eq.2 ⟨k⁻¹, H.inv_mem hk, h⁻¹, H.inv_mem hh, by group⟩

@[simp]
theorem invDoubleCoset_mk (g : G) : invDoubleCoset H (mk H H g) = mk H H g⁻¹ := rfl

@[simp]
theorem invDoubleCoset_invDoubleCoset (q : Quotient (H : Set G) H) :
    invDoubleCoset H (invDoubleCoset H q) = q := by
  rw [← out_eq' q, invDoubleCoset_mk, invDoubleCoset_mk, inv_inv]

theorem mk_eq_invDoubleCoset_iff (g : G) (q : Quotient (H : Set G) H) :
    mk H H g = invDoubleCoset H q ↔ mk H H g⁻¹ = q := by
  rw [← invDoubleCoset_mk]
  constructor
  · intro h; rw [h, invDoubleCoset_invDoubleCoset]
  · rintro rfl; rw [invDoubleCoset_invDoubleCoset]

theorem card_quotToDoubleCoset_invDoubleCoset (q : Quotient (H : Set G) H) :
    Nat.card (quotToDoubleCoset H H (invDoubleCoset H q)) = Nat.card (quotToDoubleCoset H H q) :=
  Nat.card_congr <| Equiv.subtypeEquiv (Equiv.inv G) fun g => by
    simp only [mem_quotToDoubleCoset_iff, Equiv.inv_apply]
    exact mk_eq_invDoubleCoset_iff H g q

/-- `D ⊆ D * D`, phrased with representatives. -/
def SelfMul (q : Quotient (H : Set G) H) : Prop :=
  ∃ a b : G, mk H H a = q ∧ mk H H b = q ∧ mk H H (a * b) = q

theorem SelfMul.invDoubleCoset {q : Quotient (H : Set G) H} (hq : SelfMul H q) :
    SelfMul H (invDoubleCoset H q) := by
  obtain ⟨a, b, ha, hb, hab⟩ := hq
  refine ⟨b⁻¹, a⁻¹, ?_, ?_, ?_⟩
  · rw [← hb]; rfl
  · rw [← ha]; rfl
  · rw [← hab, ← mul_inv_rev]; rfl

theorem selfMul_invDoubleCoset_iff (q : Quotient (H : Set G) H) :
    SelfMul H (invDoubleCoset H q) ↔ SelfMul H q :=
  ⟨fun h => by simpa using h.invDoubleCoset, SelfMul.invDoubleCoset H⟩

open Classical in
/-- The permutation fixing the double cosets `D` with `D ⊆ D * D` and inverting the others. -/
noncomputable def triangleFun (q : Quotient (H : Set G) H) : Quotient (H : Set G) H :=
  if SelfMul H q then q else invDoubleCoset H q

theorem triangleFun_involutive : Function.Involutive (triangleFun H) := by
  intro q
  by_cases hq : SelfMul H q
  · simp [triangleFun, hq]
  · have : ¬ SelfMul H (invDoubleCoset H q) := by rwa [selfMul_invDoubleCoset_iff]
    simp [triangleFun, hq, this]

/-- **Triangle form of the double coset criterion.** If every double coset `D` contains
`a, b` with `a * b ∈ D` or `(a * b)⁻¹ ∈ D`, there is a size-preserving permutation `ψ` of the
double cosets (`ψ D = D` or `D⁻¹`) with `ψ D ⊆ D * D`. -/
theorem exists_perm_of_triangle
    (htri : ∀ q : Quotient (H : Set G) H, ∃ a b : G, mk H H a = q ∧ mk H H b = q ∧
      (mk H H (a * b) = q ∨ mk H H (a * b)⁻¹ = q)) :
    ∃ ψ : Quotient (H : Set G) H ≃ Quotient (H : Set G) H,
      (∀ q, Nat.card (quotToDoubleCoset H H (ψ q)) = Nat.card (quotToDoubleCoset H H q)) ∧
      ∀ q, ∃ a b : G, mk H H a = q ∧ mk H H b = q ∧ mk H H (a * b) = ψ q := by
  refine ⟨(triangleFun_involutive H).toPerm, fun q => ?_, fun q => ?_⟩
  · simp only [Function.Involutive.coe_toPerm, triangleFun]
    split_ifs
    · rfl
    · exact card_quotToDoubleCoset_invDoubleCoset H q
  · simp only [Function.Involutive.coe_toPerm, triangleFun]
    split_ifs with hq
    · exact hq
    · obtain ⟨a, b, ha, hb, h | h⟩ := htri q
      · exact absurd ⟨a, b, ha, hb, h⟩ hq
      · exact ⟨a, b, ha, hb, (mk_eq_invDoubleCoset_iff H _ q).2 h⟩

variable [Finite G]

/-- Triangle form of the double coset criterion: if `H` has a complete mapping and every double
coset `D` of `H` contains `a, b` with `a * b ∈ D` or `(a * b)⁻¹ ∈ D`, then `G` has a complete
mapping. -/
theorem hasCompleteMapping_of_triangle (hcos : CosetStatement.{u}) (hH : HasCompleteMapping H)
    (htri : ∀ q : Quotient (H : Set G) H, ∃ a b : G, mk H H a = q ∧ mk H H b = q ∧
      (mk H H (a * b) = q ∨ mk H H (a * b)⁻¹ = q)) : HasCompleteMapping G := by
  obtain ⟨ψ, hψ, hmul⟩ := exists_perm_of_triangle H htri
  exact hasCompleteMapping_of_doubleCoset_perms hcos H hH (Equiv.refl _) ψ (fun _ => rfl) hψ hmul

omit [Finite G] in
/-- Triangle form, concluding `WilcoxCriterion`. -/
theorem wilcoxCriterion_of_triangle (hne : H ≠ ⊤) (hgood : IsGood H)
    (htri : ∀ q : Quotient (H : Set G) H, ∃ a b : G, mk H H a = q ∧ mk H H b = q ∧
      (mk H H (a * b) = q ∨ mk H H (a * b)⁻¹ = q)) : WilcoxCriterion G :=
  ⟨H, hne, hgood, exists_perm_of_triangle H htri⟩

end Inverse

section Action

variable {G : Type u} {α : Type*} [Group G] [MulAction G α]

/-- Double cosets of a point stabilizer `H = G_{x₀}`: `HgH = Hg'H` iff some `h ∈ H` moves
`g • x₀` to `g' • x₀`. -/
theorem mk_stabilizer_eq_mk_iff (x₀ : α) (g g' : G) :
    mk (MulAction.stabilizer G x₀) (MulAction.stabilizer G x₀) g =
        mk (MulAction.stabilizer G x₀) (MulAction.stabilizer G x₀) g' ↔
      ∃ h ∈ MulAction.stabilizer G x₀, h • g • x₀ = g' • x₀ := by
  rw [DoubleCoset.eq]
  constructor
  · rintro ⟨h, hh, k, hk, rfl⟩
    refine ⟨h, hh, ?_⟩
    rw [MulAction.mem_stabilizer_iff] at hk
    rw [mul_smul, mul_smul, hk]
  · rintro ⟨h, hh, hg⟩
    refine ⟨h, hh, g⁻¹ * h⁻¹ * g', ?_, by group⟩
    rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, ← hg, inv_smul_smul, inv_smul_smul]

/-- **Labelling form of the Wilcox criterion.** Let `G` act transitively on `α` with point
stabilizer `H = G_{x₀}` good and proper. Label the points by `lab : α → Fin r` so that labels are
exactly the `H`-orbits, and let `σ` be a permutation of the labels preserving the label class
sizes, such that for each label `k` some `a, b` with `a • x₀`, `b • x₀` labelled `k` have
`(a * b) • x₀` labelled `σ k`. Then `G` satisfies `WilcoxCriterion`. -/
theorem wilcoxCriterion_of_labelling [Finite α] (x₀ : α) (htrans : ∀ y : α, ∃ g : G, g • x₀ = y)
    {r : ℕ} (lab : α → Fin r)
    (hlab : ∀ y y', lab y = lab y' ↔ ∃ h ∈ MulAction.stabilizer G x₀, h • y = y')
    (σ : Equiv.Perm (Fin r))
    (hsize : ∀ k, Nat.card {y // lab y = σ k} = Nat.card {y // lab y = k})
    (hmul : ∀ k, ∃ a b : G, lab (a • x₀) = k ∧ lab (b • x₀) = k ∧ lab ((a * b) • x₀) = σ k)
    (hgood : IsGood (MulAction.stabilizer G x₀)) (hne : ∃ y, y ≠ x₀) : WilcoxCriterion G := by
  set H := MulAction.stabilizer G x₀ with hHdef
  have hmk : ∀ g g' : G, mk H H g = mk H H g' ↔ lab (g • x₀) = lab (g' • x₀) := fun g g' => by
    rw [mk_stabilizer_eq_mk_iff, hlab]
  let ℓ : Quotient (H : Set G) H → Fin r := fun q => lab (q.out • x₀)
  have hℓ : ∀ g, ℓ (mk H H g) = lab (g • x₀) := fun g => (hmk _ _).1 (out_eq' _)
  have hℓinj : Function.Injective ℓ := by
    intro q q' h
    rw [← out_eq' q, ← out_eq' q', hmk]
    exact h
  have hℓsurj : Function.Surjective ℓ := fun k => by
    obtain ⟨a, -, ha, -, -⟩ := hmul k
    exact ⟨mk H H a, by rw [hℓ, ha]⟩
  let e := Equiv.ofBijective ℓ ⟨hℓinj, hℓsurj⟩
  have hℓeq : ∀ g q, mk H H g = q ↔ lab (g • x₀) = ℓ q := fun g q => by
    rw [← hℓ]; exact hℓinj.eq_iff.symm
  -- the left cosets of `H` are the points of `α`
  let E : G ⧸ H ≃ α := (MulAction.orbitEquivQuotientStabilizer G x₀).symm.trans
    (Equiv.subtypeUnivEquiv fun y => htrans y)
  have hE : ∀ g : G, E g = g • x₀ := fun g => rfl
  have hcard : ∀ q, Nat.card (quotToDoubleCoset H H q) = Nat.card H * Nat.card {y // lab y = ℓ q} :=
    fun q => by
      rw [card_quotToDoubleCoset]
      congr 1
      refine Nat.card_congr (Equiv.subtypeEquiv E fun c => ?_)
      induction c using QuotientGroup.induction_on with
      | H g => rw [cosetToDouble_mk, hE, hℓeq]
  refine ⟨H, ?_, hgood, e.trans (σ.trans e.symm), fun q => ?_, fun q => ?_⟩
  · rintro hH
    obtain ⟨y, hy⟩ := hne
    obtain ⟨g, rfl⟩ := htrans y
    have hg : g ∈ H := hH ▸ Subgroup.mem_top g
    exact hy (MulAction.mem_stabilizer_iff.1 hg)
  · have : ℓ (e.symm (σ (e q))) = σ (ℓ q) := e.apply_symm_apply _
    simp only [Equiv.trans_apply]
    rw [hcard, hcard, this, hsize]
  · obtain ⟨a, b, ha, hb, hab⟩ := hmul (ℓ q)
    refine ⟨a, b, (hℓeq _ _).2 ha, (hℓeq _ _).2 hb, (hℓeq _ _).2 ?_⟩
    rw [hab]
    exact (e.apply_symm_apply _).symm

/-- Labelling form with `σ = 1` and a single element: if for every label `k` some `g` has
`g • x₀` and `(g * g) • x₀` both labelled `k`, then `G` satisfies `WilcoxCriterion`. -/
theorem wilcoxCriterion_of_labelling_sq [Finite α] (x₀ : α)
    (htrans : ∀ y : α, ∃ g : G, g • x₀ = y) {r : ℕ} (lab : α → Fin r)
    (hlab : ∀ y y', lab y = lab y' ↔ ∃ h ∈ MulAction.stabilizer G x₀, h • y = y')
    (hsq : ∀ k, ∃ g : G, lab (g • x₀) = k ∧ lab ((g * g) • x₀) = k)
    (hgood : IsGood (MulAction.stabilizer G x₀)) (hne : ∃ y, y ≠ x₀) : WilcoxCriterion G :=
  wilcoxCriterion_of_labelling x₀ htrans lab hlab (Equiv.refl _) (fun _ => rfl)
    (fun k => by
      obtain ⟨g, h1, h2⟩ := hsq k
      exact ⟨g, g, h1, h1, h2⟩) hgood hne

end Action

/-- The permutation-representation form `PermLabelling` implies `WilcoxCriterion`. -/
theorem wilcoxCriterion_of_permLabelling {G : Type u} [Group G] [Finite G]
    (h : PermLabelling G) : WilcoxCriterion G := by
  obtain ⟨n, ρ, x₀, r, lab, σ, htrans, hlab, hsize, hmul, hgood, hne⟩ := h
  let _ : MulAction G (Fin n) := MulAction.compHom (Fin n) ρ
  have hsmul : ∀ (g : G) (y : Fin n), g • y = ρ g y := fun _ _ => rfl
  have hstab : MulAction.stabilizer G x₀ = (MulAction.stabilizer (Equiv.Perm (Fin n)) x₀).comap ρ := by
    ext g
    simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_comap, hsmul, Equiv.Perm.smul_def]
  refine wilcoxCriterion_of_labelling x₀ (by simpa only [hsmul] using htrans) lab ?_ σ hsize
    (by simpa only [hsmul] using hmul) (hstab ▸ hgood) hne
  intro y y'
  rw [hlab]
  simp only [MulAction.mem_stabilizer_iff, hsmul]

section TwoTransitive

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
theorem mk_eq_mk_one_iff (H : Subgroup G) (g : G) : mk H H g = mk H H 1 ↔ g ∈ H := by
  rw [eq_comm, DoubleCoset.eq]
  constructor
  · rintro ⟨h, hh, k, hk, rfl⟩
    simpa using H.mul_mem hh hk
  · intro hg
    exact ⟨g, hg, 1, H.one_mem, by simp⟩

/-- **Two double cosets** (Evans, Lemma 4). If `H` has a complete mapping, `H` and `G ∖ H` are
the only double cosets of `H`, and `[G : H] ≥ 3`, then `G` has a complete mapping. -/
theorem hasCompleteMapping_of_two_doubleCosets (hcos : CosetStatement.{u}) (H : Subgroup G)
    (hH : HasCompleteMapping H)
    (h2 : ∀ g g' : G, g ∉ H → g' ∉ H → mk H H g = mk H H g') (h3 : 3 ≤ H.index) :
    HasCompleteMapping G := by
  refine hasCompleteMapping_of_forall_mul_mem hcos H hH fun q => ?_
  by_cases hq : q.out ∈ H
  · have h1 : mk H H 1 = q := by rw [← out_eq' q, eq_comm, mk_eq_mk_one_iff]; exact hq
    exact ⟨1, 1, h1, h1, by rw [mul_one, h1]⟩
  · set g := q.out
    obtain ⟨b, hb, hgb⟩ : ∃ b, b ∉ H ∧ g * b ∉ H := by
      by_contra! hcon
      classical
      have := Fintype.ofFinite (G ⧸ H)
      have hsub : (Finset.univ : Finset (G ⧸ H)) ⊆ {((1 : G) : G ⧸ H), ((g⁻¹ : G) : G ⧸ H)} := by
        intro c _
        induction c using QuotientGroup.induction_on with
        | H b =>
        by_cases hbH : b ∈ H
        · simp [QuotientGroup.eq, hbH]
        · simp only [Finset.mem_insert, Finset.mem_singleton, QuotientGroup.eq]
          exact Or.inr (by rw [← mul_inv_rev]; exact H.inv_mem (hcon b hbH))
      have := (Finset.card_le_card hsub).trans Finset.card_le_two
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, ← Subgroup.index] at this
      omega
    refine ⟨g, b, out_eq' q, ?_, ?_⟩
    · rw [h2 b g hb hq, out_eq']
    · rw [h2 _ g hgb hq, out_eq']

/-- Two double cosets, phrased by counting: if `H` has a complete mapping, at most two double
cosets, and index at least `3`, then `G` has a complete mapping. -/
theorem hasCompleteMapping_of_card_doubleCoset_le_two (hcos : CosetStatement.{u})
    (H : Subgroup G) (hH : HasCompleteMapping H)
    (h2 : Nat.card (Quotient (H : Set G) H) ≤ 2) (h3 : 3 ≤ H.index) : HasCompleteMapping G := by
  refine hasCompleteMapping_of_two_doubleCosets hcos H hH (fun g g' hg hg' => ?_) h3
  by_contra hne
  classical
  have : Finite (Quotient (H : Set G) H) := Quotient.finite _
  have := Fintype.ofFinite (Quotient (H : Set G) H)
  have h1g : mk H H g ≠ mk H H 1 := by rwa [Ne, mk_eq_mk_one_iff]
  have h1g' : mk H H g' ≠ mk H H 1 := by rwa [Ne, mk_eq_mk_one_iff]
  have hc : ({mk H H 1, mk H H g, mk H H g'} : Finset _).card = 3 :=
    Finset.card_eq_three.2 ⟨_, _, _, h1g.symm, h1g'.symm, hne, rfl⟩
  have := Finset.card_le_univ ({mk H H 1, mk H H g, mk H H g'} : Finset _)
  rw [hc, ← Nat.card_eq_fintype_card] at this
  omega

/-- **Two-transitive actions** (Evans, remark after Lemma 4). If `G` acts 2-transitively on a
finite set `α` with at least three points and a point stabilizer has a complete mapping, then
`G` has a complete mapping. -/
theorem hasCompleteMapping_of_two_transitive (hcos : CosetStatement.{u}) {α : Type*}
    [MulAction G α] (x₀ : α)
    (h2 : ∀ x y x' y' : α, x ≠ y → x' ≠ y' → ∃ g : G, g • x = x' ∧ g • y = y')
    (h3 : 3 ≤ Nat.card α) (hH : HasCompleteMapping (MulAction.stabilizer G x₀)) :
    HasCompleteMapping G := by
  refine hasCompleteMapping_of_two_doubleCosets hcos _ hH (fun g g' hg hg' => ?_) ?_
  · rw [MulAction.mem_stabilizer_iff] at hg hg'
    obtain ⟨h, hh, hgh⟩ := h2 x₀ (g • x₀) x₀ (g' • x₀) (Ne.symm hg) (Ne.symm hg')
    exact (mk_stabilizer_eq_mk_iff x₀ g g').2 ⟨h, hh, hgh⟩
  · have horb : MulAction.orbit G x₀ = Set.univ := by
      refine Set.eq_univ_of_forall fun y => ?_
      by_cases hy : y = x₀
      · subst hy
        exact MulAction.mem_orbit_self _
      · obtain ⟨g, hg, -⟩ := h2 x₀ y y x₀ (Ne.symm hy) hy
        exact ⟨g, hg⟩
    rwa [MulAction.index_stabilizer, horb, Set.ncard_univ]

end TwoTransitive

end CFSGOutside.HallPaige
