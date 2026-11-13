import Mathlib
import CFSGOutside.Corpus.Defs.PGammaL2

/-!
# Basic facts on `PGL(2,K)`, `PSL(2,K)`, `PΓL(2,K)` for finite fields `K`

Orders, centers, and the abelian quotient `PΓL(2,K) / PSL(2,K)`.
The statements about `PSL` that mention `ringChar K ≠ 2` keep that hypothesis;
the center statement `center_PSL2` holds for every field (hypothesis unused).
-/

noncomputable section

namespace CFSGOutside.GiuliettiKorchmaros.LinearTwo

open Matrix CFSGOutside.Corpus.GorensteinWalter

section Orders

variable (K : Type) [Field K] [Finite K]

theorem card_GL2 :
    Nat.card (GL (Fin 2) K) = (Nat.card K ^ 2 - 1) * (Nat.card K ^ 2 - Nat.card K) := by
  have := Fintype.ofFinite K
  rw [Matrix.card_GL_field]
  simp [Fin.prod_univ_two, Nat.card_eq_fintype_card]

theorem card_PGL2 : Nat.card (PGL2 K) = Nat.card K * (Nat.card K ^ 2 - 1) := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center (GL (Fin 2) K))
  have h2 : Nat.card (Subgroup.center (GL (Fin 2) K)) = Nat.card K - 1 := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    rw [← Nat.card_units, ← Nat.card_congr
      (MonoidHom.ofInjective (f := (GeneralLinearGroup.scalar (Fin 2) : Kˣ →* GL (Fin 2) K))
        (fun a b h => by
          have := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h
          simpa [Units.ext_iff] using this)).toEquiv]
  rw [card_GL2, h2] at h1
  have hq : 2 ≤ Nat.card K := by
    have : Nontrivial K := inferInstance
    exact Nat.succ_le_of_lt (Finite.one_lt_card)
  have h3 : Nat.card K ^ 2 - Nat.card K = Nat.card K * (Nat.card K - 1) := by
    rw [Nat.mul_sub_one, pow_two]
  have hpos : 0 < Nat.card K - 1 := by omega
  apply Nat.eq_of_mul_eq_mul_right hpos
  change Nat.card (GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K)) * _ = _
  rw [← h1, h3]
  ring

theorem card_center_SL2 (hK : ringChar K ≠ 2) :
    Nat.card (Subgroup.center (SpecialLinearGroup (Fin 2) K)) = 2 := by
  have hne : (-1 : K) ≠ 1 := by
    intro h
    apply hK
    have h2 : ((2 : ℕ) : K) = 0 := by push_cast; linear_combination -h
    exact CharP.ringChar_of_prime_eq_zero Nat.prime_two h2
  have : (Subgroup.center (SpecialLinearGroup (Fin 2) K) : Set (SpecialLinearGroup (Fin 2) K)) =
      {1, -1} := by
    ext A
    rw [SetLike.mem_coe, Matrix.SpecialLinearGroup.mem_center_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Fintype.card_fin]
    constructor
    · rintro ⟨r, hr, hA⟩
      have : (r - 1) * (r + 1) = 0 := by linear_combination hr
      rcases mul_eq_zero.mp this with h | h
      · left; apply Subtype.ext; rw [← hA, sub_eq_zero.mp h]; simp
      · right
        apply Subtype.ext
        rw [← hA, eq_neg_of_add_eq_zero_left h]
        ext i j; fin_cases i <;> fin_cases j <;> simp
    · rintro (rfl | rfl)
      · exact ⟨1, by simp⟩
      · exact ⟨-1, by simp, by ext i j; fin_cases i <;> fin_cases j <;> simp⟩
  have hn : Nat.card (Subgroup.center (SpecialLinearGroup (Fin 2) K)) =
      (({1, -1} : Set (SpecialLinearGroup (Fin 2) K))).ncard := by
    rw [← this, ← Nat.card_coe_set_eq]; rfl
  rw [hn, Set.ncard_pair]
  intro h
  apply hne
  have := congrArg (fun A : SpecialLinearGroup (Fin 2) K => (A : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simpa using this.symm

theorem card_PSL2_mul_two (hK : ringChar K ≠ 2) :
    Nat.card (PSL2 K) * 2 = Nat.card K * (Nat.card K ^ 2 - 1) := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (SpecialLinearGroup (Fin 2) K))
  rw [card_center_SL2 K hK] at h1
  have h2 := Matrix.card_SL_mul_card_units (n := Fin 2) (R := K)
  rw [card_GL2, Nat.card_units] at h2
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  have h3 : Nat.card K ^ 2 - Nat.card K = Nat.card K * (Nat.card K - 1) := by
    rw [Nat.mul_sub_one, pow_two]
  have hpos : 0 < Nat.card K - 1 := by omega
  apply Nat.eq_of_mul_eq_mul_right hpos
  change Nat.card (SpecialLinearGroup (Fin 2) K ⧸
    Subgroup.center (SpecialLinearGroup (Fin 2) K)) * 2 * _ = _
  rw [← h1]
  rw [h3] at h2
  linarith

/-- If `mk A` commutes with the classes of both elementary matrices, it is trivial. -/
theorem mk_eq_one_of_commute (A B C : GL (Fin 2) K)
    (hB : (B : Matrix (Fin 2) (Fin 2) K) = !![1, 1; 0, 1])
    (hC : (C : Matrix (Fin 2) (Fin 2) K) = !![1, 0; 1, 1])
    (h1 : ProjGenLinGroup.mk A * ProjGenLinGroup.mk B =
      ProjGenLinGroup.mk B * ProjGenLinGroup.mk A)
    (h2 : ProjGenLinGroup.mk A * ProjGenLinGroup.mk C =
      ProjGenLinGroup.mk C * ProjGenLinGroup.mk A) :
    ProjGenLinGroup.mk A = 1 := by
  rw [← map_mul, ← map_mul, ProjGenLinGroup.mk_eq_mk_iff] at h1 h2
  obtain ⟨u, hu⟩ := h1
  obtain ⟨v, hv⟩ := h2
  have hdet : (A : Matrix (Fin 2) (Fin 2) K).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp A.isUnit).ne_zero
  rw [Matrix.det_fin_two] at hdet
  have e : ∀ {g h : GL (Fin 2) K}, g = h → ∀ i j,
      (g : Matrix (Fin 2) (Fin 2) K) i j = (h : Matrix (Fin 2) (Fin 2) K) i j :=
    fun h i j => by rw [h]
  have u00 := e hu 0 0
  have u10 := e hu 1 0
  have u01 := e hu 0 1
  have u11 := e hu 1 1
  have v00 := e hv 0 0
  have v10 := e hv 1 0
  have v01 := e hv 0 1
  have v11 := e hv 1 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, hB, hC] at u00 u10 u01 u11 v00 v10 v01 v11
  have hc : (A : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    by_contra hc
    have hu1 : (u : K) = 1 := mul_left_cancel₀ hc (by linear_combination u10)
    rw [hu1] at u00
    apply hc; linear_combination -u00
  have hb : (A : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by
    by_contra hb
    have hv1 : (v : K) = 1 := mul_left_cancel₀ hb (by linear_combination v01)
    rw [hv1] at v11
    apply hb; linear_combination -v11
  rw [hb, hc] at hdet
  have ha : (A : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := fun h => hdet (by rw [h]; ring)
  have hd : (A : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0 := fun h => hdet (by rw [h]; ring)
  have hu1 : (u : K) = 1 := mul_left_cancel₀ ha (by rw [hc] at u00; linear_combination u00)
  rw [hu1, hb] at u01
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar]
  refine ⟨Units.mk0 _ ha, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hb, hc] <;> linear_combination u01

/-- The elementary matrix `[[1,1],[0,1]]`. -/
def E12 : SpecialLinearGroup (Fin 2) K := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩

/-- The elementary matrix `[[1,0],[1,1]]`. -/
def E21 : SpecialLinearGroup (Fin 2) K := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩

theorem center_PGL2 : Subgroup.center (PGL2 K) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨A, rfl⟩ := ProjGenLinGroup.mk_surjective x
  rw [Subgroup.mem_center_iff] at hx
  rw [Subgroup.mem_bot]
  refine mk_eq_one_of_commute K A (SpecialLinearGroup.toGL (E12 K))
    (SpecialLinearGroup.toGL (E21 K)) rfl rfl ?_ ?_
  · exact (hx _).symm
  · exact (hx _).symm

theorem center_PSL2 (hK : ringChar K ≠ 2) : Subgroup.center (PSL2 K) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  rw [Subgroup.mem_center_iff] at hx
  rw [Subgroup.mem_bot]
  apply ProjectiveSpecialLinearGroup.toPGL_injective
  rw [map_one]
  have key : ∀ E : SpecialLinearGroup (Fin 2) K,
      ProjGenLinGroup.mk (SpecialLinearGroup.toGL g) * ProjGenLinGroup.mk (SpecialLinearGroup.toGL E) =
      ProjGenLinGroup.mk (SpecialLinearGroup.toGL E) * ProjGenLinGroup.mk (SpecialLinearGroup.toGL g) := by
    intro E
    have := congrArg (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K))
      (hx (QuotientGroup.mk E : PSL2 K))
    simp only [map_mul] at this
    exact this.symm
  exact mk_eq_one_of_commute K _ (SpecialLinearGroup.toGL (E12 K))
    (SpecialLinearGroup.toGL (E21 K)) rfl rfl (key _) (key _)

end Orders

section Gamma

variable (K : Type) [Field K] [Finite K]

/-- The subgroup of squares of `Kˣ`. -/
def sqSub : Subgroup Kˣ := (powMonoidHom 2 : Kˣ →* Kˣ).range

theorem mem_sqSub {d : Kˣ} : d ∈ sqSub K ↔ ∃ w : Kˣ, w ^ 2 = d := Iff.rfl

/-- Ring automorphisms of a finite field of odd characteristic change a unit only by a square. -/
theorem exists_sq_map (hK : ringChar K ≠ 2) (σ : K ≃+* K) (d : Kˣ) :
    ∃ w : Kˣ, Units.map (σ : K →* K) d = d * w ^ 2 := by
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic (Units.map (σ : K →* K))
  have hodd : Odd m := by
    by_contra hev
    rw [Int.not_odd_iff_even] at hev
    obtain ⟨k, hk⟩ := hev
    obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare hK
    have ha0 : a ≠ 0 := by
      rintro rfl; exact ha ⟨0, by simp⟩
    obtain ⟨g, hg⟩ : ∃ g : Kˣ, Units.map (σ : K →* K) g = Units.mk0 a ha0 :=
      ⟨Units.map (σ.symm : K →* K) (Units.mk0 a ha0), by
        ext; simp⟩
    rw [hm, hk, _root_.zpow_add] at hg
    exact ha ⟨((g ^ k : Kˣ) : K), by
      have := congrArg Units.val hg
      simpa using this.symm⟩
  obtain ⟨k, hk⟩ := hodd
  refine ⟨d ^ k, ?_⟩
  rw [hm, hk]
  group

theorem ringEquiv_mul_comm (σ τ : K ≃+* K) : σ * τ = τ * σ := by
  obtain ⟨p, hp⟩ := CharP.exists K
  have hp' : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  let e : (K ≃+* K) ≃* (K ≃ₐ[ZMod p] K) := {
    toFun := fun sigma =>
      AlgEquiv.ofRingEquiv (f := sigma) (by
        intro x
        have h :
            (sigma.toRingHom.comp (algebraMap (ZMod p) K) :
              ZMod p →+* K) = algebraMap (ZMod p) K :=
          RingHom.ext_zmod _ _
        exact DFunLike.congr_fun h x)
    invFun := fun sigma => sigma.toRingEquiv
    left_inv := by intro sigma; ext x; rfl
    right_inv := by intro sigma; ext x; rfl
    map_mul' := by intro sigma tau; ext x; rfl }
  have hc : IsCyclic (K ≃+* K) := e.isCyclic.mpr inferInstance
  letI := hc.commGroup
  exact mul_comm σ τ

/-- Determinant modulo squares on `PGL₂(K)`. -/
def detQ : PGL2 K →* Kˣ ⧸ sqSub K :=
  ProjGenLinGroup.lift ((QuotientGroup.mk' (sqSub K)).comp GeneralLinearGroup.det) (by
    ext u
    simp only [MonoidHom.coe_comp, Function.comp_apply, QuotientGroup.mk'_apply,
      MonoidHom.one_apply, QuotientGroup.eq_one_iff]
    exact ⟨u, by ext; simp [pow_two]⟩)

theorem detQ_mk (A : GL (Fin 2) K) :
    detQ K (ProjGenLinGroup.mk A) = (GeneralLinearGroup.det A : Kˣ) := rfl

theorem detQ_fieldAut (hK : ringChar K ≠ 2) (σ : K ≃+* K) (x : PGL2 K) :
    detQ K (pgl2FieldAut K σ x) = detQ K x := by
  induction x using ProjGenLinGroup.induction_on with | mk A =>
  obtain ⟨w, hw⟩ := exists_sq_map K hK σ (GeneralLinearGroup.det A)
  change detQ K (ProjGenLinGroup.mk (GeneralLinearGroup.map (σ : K →+* K) A)) = _
  rw [detQ_mk, detQ_mk, GeneralLinearGroup.map_det,
    show (Units.map ((σ : K →+* K) : K →* K)) (GeneralLinearGroup.det A) = _ from hw]
  rw [QuotientGroup.eq]
  exact (mem_sqSub K).mpr ⟨w⁻¹, by group⟩

/-- The homomorphism `PΓL₂(K) → (Kˣ/squares) × Aut(K)`. -/
def Phi (hK : ringChar K ≠ 2) : PGammaL2 K →* (Kˣ ⧸ sqSub K) × (K ≃+* K) :=
  MonoidHom.mk' (fun x => (detQ K x.left, x.right)) (by
    intro x y
    refine Prod.ext ?_ rfl
    simp only [SemidirectProduct.mul_left, map_mul, Prod.fst_mul]
    rw [detQ_fieldAut K hK])

theorem Phi_ker_le (hK : ringChar K ≠ 2) (x : PGammaL2 K) (hx : Phi K hK x = 1) :
    x ∈ ((ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range).map
      (SemidirectProduct.inl : PGL2 K →* PGammaL2 K) := by
  have h1 : detQ K x.left = 1 := congrArg Prod.fst hx
  have h2 : x.right = 1 := congrArg Prod.snd hx
  have hx : x = SemidirectProduct.inl x.left := by
    ext <;> simp [h2]
  obtain ⟨A, hA⟩ := ProjGenLinGroup.mk_surjective x.left
  rw [← hA, detQ_mk, QuotientGroup.eq_one_iff, mem_sqSub] at h1
  obtain ⟨μ, hμ⟩ := h1
  rw [hx]
  refine Subgroup.mem_map.mpr ⟨x.left, ?_, rfl⟩
  let A' : GL (Fin 2) K := A * GeneralLinearGroup.scalar (Fin 2) μ⁻¹
  have hdet : (A' : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    have h4 : GeneralLinearGroup.det A' = 1 := by
      simp only [A', map_mul, ← hμ]
      ext; simp [pow_two]
    have := congrArg Units.val h4
    simpa using this
  let S : SpecialLinearGroup (Fin 2) K := ⟨(A' : Matrix (Fin 2) (Fin 2) K), hdet⟩
  refine ⟨QuotientGroup.mk S, ?_⟩
  rw [ProjectiveSpecialLinearGroup.toPGL_mk, ← hA, ProjGenLinGroup.mk_eq_mk_iff]
  refine ⟨μ, ?_⟩
  ext1
  change (A' : Matrix (Fin 2) (Fin 2) K) * _ = _
  simp [A', mul_assoc, ← map_mul]

theorem commutator_PGammaL2_le (hK : ringChar K ≠ 2) :
    commutator (PGammaL2 K) ≤
      ((ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range).map SemidirectProduct.inl := by
  rw [commutator_def, Subgroup.commutator_le]
  intro g _ h _
  apply Phi_ker_le K hK
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact Prod.ext (mul_comm (Phi K hK g).1 (Phi K hK h).1)
    (ringEquiv_mul_comm K (Phi K hK g).2 (Phi K hK h).2)

end Gamma

end CFSGOutside.GiuliettiKorchmaros.LinearTwo
