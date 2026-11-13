import Mathlib

/-!
# Pullback of a characteristic-subgroup configuration along `K ⊴ G`

Given `K ⊴ G`, characteristic `O ≤ K`, and characteristic `N ≤ K/O` with trivial centralizer in `K/O`,
there is a normal `C ⊴ G` such that `G/C` has a normal subgroup `S ≅ N` with trivial centralizer, and
`S.index * |C| = K.index * N.index * |O|`; in particular `S.index ∣ K.index * N.index`.
(Equality `S.index = K.index * N.index` is false in general: take `G = S₃ × C₂`, `K = N = S₃`, `O = 1`.)
-/

namespace CFSGOutside.Gagola

open Classical

namespace D8Pullback

theorem char_mem {A : Type*} [Group A] (H : Subgroup A) [H.Characteristic] (φ : A ≃* A) {x : A}
    (hx : x ∈ H) : φ x ∈ H := by
  have h : x ∈ H.comap φ.toMonoidHom := by
    rw [(inferInstance : H.Characteristic).fixed φ]; exact hx
  exact h

variable {G : Type} [Group G] [Finite G] (K : Subgroup G) [K.Normal] (O : Subgroup K)
  [O.Characteristic] (N : Subgroup (K ⧸ O)) [N.Characteristic]

instance instNormalO : (O.map K.subtype).Normal := by
  refine ⟨?_⟩
  rintro _ ⟨o, ho, rfl⟩ g
  have := char_mem O (MulAut.conjNormal (H := K) g) ho
  exact ⟨_, this, by simp [MulAut.conjNormal_apply]⟩

/-- the map `K/O → G/O'` -/
noncomputable def iota : K ⧸ O →* G ⧸ O.map K.subtype :=
  QuotientGroup.lift O ((QuotientGroup.mk' (O.map K.subtype)).comp K.subtype) (by
    intro o ho
    simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply, QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨o, ho, rfl⟩)

theorem iota_mk (k : K) : iota K O (k : K ⧸ O) = ((k : G) : G ⧸ O.map K.subtype) := rfl

theorem iota_injective : Function.Injective (iota K O) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
  rw [iota_mk, QuotientGroup.eq_one_iff] at hx
  obtain ⟨o, ho, hok⟩ := hx
  have : o = k := Subtype.ext hok
  subst this
  exact (QuotientGroup.eq_one_iff _).mpr ho

theorem conj_aux (g : G) (y : K ⧸ O) :
    ∃ z : K ⧸ O, iota K O z = (g : G ⧸ O.map K.subtype) * iota K O y * (g : G ⧸ O.map K.subtype)⁻¹ ∧
      (y ∈ N → z ∈ N) := by
  have hmap : O.map ((MulAut.conjNormal (H := K) g : K ≃* K) : K →* K) = O := by
    rw [Subgroup.map_equiv_eq_comap_symm]
    exact (inferInstance : O.Characteristic).fixed _
  let ψ : K ⧸ O ≃* K ⧸ O := QuotientGroup.congr O O (MulAut.conjNormal (H := K) g) hmap
  refine ⟨ψ y, ?_, fun hy => char_mem N ψ hy⟩
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
  have : ψ (k : K ⧸ O) = ((MulAut.conjNormal (H := K) g k : K) : K ⧸ O) := rfl
  rw [this, iota_mk, iota_mk]
  simp [MulAut.conjNormal_apply]

theorem normal_Nbar : (N.map (iota K O)).Normal := by
  refine ⟨?_⟩
  rintro _ ⟨y, hy, rfl⟩ q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨z, hz, hzN⟩ := conj_aux K O N g y
  exact ⟨z, hzN hy, hz⟩

/-- `C̄`, the centralizer of `N̄` in `G/O'`. -/
noncomputable def Cbar : Subgroup (G ⧸ O.map K.subtype) :=
  Subgroup.centralizer ((N.map (iota K O) : Subgroup _) : Set _)

instance normal_Cbar : (Cbar K O N).Normal := by
  haveI := normal_Nbar K O N
  refine ⟨?_⟩
  intro h hh g s hs
  rw [Cbar, Subgroup.mem_centralizer_iff] at hh
  have h1 : g⁻¹ * s * g ∈ N.map (iota K O) := by
    have := (inferInstance : (N.map (iota K O)).Normal).conj_mem s hs g⁻¹
    simpa using this
  have h2 := hh _ h1
  simp only [mul_assoc] at h2 ⊢
  have h3 := congrArg (fun t => g * t * g⁻¹) h2
  simp only [mul_assoc, mul_inv_cancel_left] at h3
  simpa [mul_assoc] using h3

/-- `C`, the preimage of `C̄` in `G`. -/
noncomputable def Csub : Subgroup G := (Cbar K O N).comap (QuotientGroup.mk' (O.map K.subtype))

instance normal_Csub : (Csub K O N).Normal := by
  unfold Csub; infer_instance

theorem le_Csub : O.map K.subtype ≤ Csub K O N := by
  intro x hx
  show QuotientGroup.mk' (O.map K.subtype) x ∈ Cbar K O N
  have : QuotientGroup.mk' (O.map K.subtype) x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
  rw [this]
  exact one_mem _

noncomputable def lam : G ⧸ O.map K.subtype →* G ⧸ Csub K O N :=
  QuotientGroup.lift (O.map K.subtype) (QuotientGroup.mk' (Csub K O N)) (by
    intro x hx
    simp only [MonoidHom.mem_ker, QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff _).mpr (le_Csub K O N hx))

theorem lam_mk (g : G) : lam K O N (g : G ⧸ O.map K.subtype) = (g : G ⧸ Csub K O N) := rfl

theorem lam_surj : Function.Surjective (lam K O N) := by
  intro x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  exact ⟨g, rfl⟩

theorem lam_eq_one {q : G ⧸ O.map K.subtype} : lam K O N q = 1 ↔ q ∈ Cbar K O N := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  rw [lam_mk, QuotientGroup.eq_one_iff]
  rfl

noncomputable def ff : K ⧸ O →* G ⧸ Csub K O N := (lam K O N).comp (iota K O)

theorem ff_injective (hN : Subgroup.centralizer (N : Set (K ⧸ O)) = ⊥) :
    Function.Injective (ff K O N) := by
  rw [injective_iff_map_eq_one]
  intro y hy
  have hy' : iota K O y ∈ Cbar K O N := (lam_eq_one K O N).mp hy
  rw [Cbar, Subgroup.mem_centralizer_iff] at hy'
  have : y ∈ Subgroup.centralizer (N : Set (K ⧸ O)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    apply iota_injective K O
    rw [map_mul, map_mul]
    exact hy' _ ⟨n, hn, rfl⟩
  rw [hN] at this
  exact this

theorem card_eq (hN : Subgroup.centralizer (N : Set (K ⧸ O)) = ⊥) :
    ∃ S : Subgroup (G ⧸ Csub K O N), S.Normal ∧ Subgroup.centralizer (S : Set (G ⧸ Csub K O N)) = ⊥ ∧
      Nonempty (S ≃* N) ∧ S.index * Nat.card (Csub K O N) = K.index * N.index * Nat.card O := by
  have hinj := ff_injective K O N hN
  haveI hNb := normal_Nbar K O N
  have hSeq : N.map (ff K O N) = (N.map (iota K O)).map (lam K O N) := by
    rw [Subgroup.map_map]; rfl
  haveI hSn : (N.map (ff K O N)).Normal := by
    rw [hSeq]; exact Subgroup.Normal.map hNb _ (lam_surj K O N)
  have hSe : N.map (ff K O N) ≃* N := (Subgroup.equivMapOfInjective N (ff K O N) hinj).symm
  refine ⟨N.map (ff K O N), hSn, ?_, ⟨hSe⟩, ?_⟩
  · rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [Subgroup.mem_centralizer_iff] at hx
    obtain ⟨q, rfl⟩ := lam_surj K O N x
    have hq : q ∈ Cbar K O N := by
      rw [Cbar, Subgroup.mem_centralizer_iff]
      intro n hn
      have hm : q * n * q⁻¹ ∈ N.map (iota K O) := hNb.conj_mem n hn q
      have h1 := hx (lam K O N n) (by rw [hSeq]; exact ⟨n, hn, rfl⟩)
      have h2 : lam K O N (q * n * q⁻¹ * n⁻¹) = 1 := by
        simp only [map_mul, map_inv]
        rw [← h1]
        simp [mul_assoc]
      have h3 : q * n * q⁻¹ * n⁻¹ ∈ Cbar K O N := (lam_eq_one K O N).mp h2
      have h4 : q * n * q⁻¹ * n⁻¹ ∈ N.map (iota K O) := Subgroup.mul_mem _ hm (Subgroup.inv_mem _ hn)
      obtain ⟨y, hy, hyeq⟩ := h4
      have h5 : ff K O N y = 1 := by
        show lam K O N (iota K O y) = 1
        rw [hyeq]; exact h2
      have := hinj (h5.trans (map_one _).symm)
      subst this
      rw [map_one] at hyeq
      have h6 : q * n * q⁻¹ = n := by
        have := congrArg (fun t => t * n) hyeq.symm
        simpa using this
      have := congrArg (fun t => t * q) h6
      simp only [mul_assoc, inv_mul_cancel, mul_one] at this
      exact this.symm
    exact (lam_eq_one K O N).mpr hq
  · -- index computation
    have e1 : Nat.card (N.map (ff K O N)) = Nat.card N := Nat.card_congr hSe.toEquiv
    have a1 := Subgroup.card_mul_index (N.map (ff K O N))
    have a2 : Nat.card (G ⧸ Csub K O N) = (Csub K O N).index := rfl
    have a3 := Subgroup.index_mul_card (Csub K O N)
    have a4 := Subgroup.card_mul_index K
    have a5 := Subgroup.card_mul_index O
    have a6 := Subgroup.card_mul_index N
    have a7 : Nat.card (K ⧸ O) = O.index := rfl
    have a8 : Nat.card (K ⧸ O) = N.index * Nat.card N := by rw [← a6]; rw [mul_comm]
    rw [e1, a2] at a1
    have hn : 0 < Nat.card N := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_left hn
    have : Nat.card N * ((N.map (ff K O N)).index * Nat.card (Csub K O N)) = Nat.card G := by
      rw [← a3, ← a1]; ring
    rw [this, ← a4]
    have : Nat.card K = Nat.card (K ⧸ O) * Nat.card O := by rw [← a5, a7]; ring
    rw [this, a8]; ring

end D8Pullback

open D8Pullback in
theorem pullback_characteristic_ex {G : Type} [Group G] [Finite G] (K : Subgroup G) [K.Normal]
    (O : Subgroup K) [O.Characteristic] (N : Subgroup (K ⧸ O)) [N.Characteristic]
    (hN : Subgroup.centralizer (N : Set (K ⧸ O)) = ⊥) :
    ∃ (C : Subgroup G) (_ : C.Normal) (S : Subgroup (G ⧸ C)) (_ : S.Normal),
      Subgroup.centralizer (S : Set (G ⧸ C)) = ⊥ ∧ Nonempty (S ≃* N) ∧
      Nat.card O ∣ Nat.card C ∧ S.index * Nat.card C = K.index * N.index * Nat.card O := by
  obtain ⟨S, hS, h1, h2, h3⟩ := card_eq K O N hN
  refine ⟨Csub K O N, inferInstance, S, hS, h1, h2, ?_, h3⟩
  have : Nat.card (O.map K.subtype) = Nat.card O :=
    Subgroup.card_map_of_injective K.subtype_injective
  rw [← this]
  exact Subgroup.card_dvd_of_le (le_Csub K O N)

/-- Weakened form: the index of `S` divides `K.index * N.index` (equality fails in general). -/
theorem pullback_characteristic {G : Type} [Group G] [Finite G] (K : Subgroup G) [K.Normal]
    (O : Subgroup K) [O.Characteristic] (N : Subgroup (K ⧸ O)) [N.Characteristic]
    (hN : Subgroup.centralizer (N : Set (K ⧸ O)) = ⊥) :
    ∃ (C : Subgroup G) (_ : C.Normal) (S : Subgroup (G ⧸ C)) (_ : S.Normal),
      Subgroup.centralizer (S : Set (G ⧸ C)) = ⊥ ∧ Nonempty (S ≃* N) ∧
      S.index ∣ K.index * N.index := by
  obtain ⟨C, hC, S, hS, h1, h2, ⟨t, ht⟩, h3⟩ := pullback_characteristic_ex K O N hN
  refine ⟨C, hC, S, hS, h1, h2, ⟨t, ?_⟩⟩
  have ho : 0 < Nat.card O := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_left ho
  rw [ht] at h3
  linarith [h3]

end CFSGOutside.Gagola
