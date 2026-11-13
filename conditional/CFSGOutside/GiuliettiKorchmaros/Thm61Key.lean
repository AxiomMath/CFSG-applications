import Mathlib
import CFSGOutside.Corpus.SemilinearEquivAut
import CFSGOutside.Corpus.AutAlternatingBijectiveConj
import CFSGOutside.GiuliettiKorchmaros.LinearTwo

/-!
# Key group-theoretic lemmas for Theorem 6.1
-/

noncomputable section

namespace CFSGOutside.GiuliettiKorchmaros.Key

open CFSGOutside.Corpus CFSGOutside.Corpus.GorensteinWalter
open scoped MatrixGroups

variable {X : Type} [Group X] [Finite X]

/-- Conjugation of `X` on `Y / Z(Y)` for a normal subgroup `Y`. -/
def conjQuot (Y : Subgroup X) [Y.Normal] : X →* MulAut (Y ⧸ Subgroup.center Y) where
  toFun g := QuotientGroup.congr (Subgroup.center Y) (Subgroup.center Y) (MulAut.conjNormal g)
    (Subgroup.map_center_eq _)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on
    simp [QuotientGroup.congr]
  map_mul' g h := by
    ext x
    induction x using QuotientGroup.induction_on
    simp [QuotientGroup.congr]

theorem conjQuot_mk (Y : Subgroup X) [Y.Normal] (g : X) (y : Y) :
    conjQuot Y g (QuotientGroup.mk y) = QuotientGroup.mk (MulAut.conjNormal g y) := rfl

/-- (1) -/
theorem ker_conjQuot (Y : Subgroup X) [Y.Normal]
    (hY : ∀ φ : Y →* Subgroup.center Y, φ = 1) :
    (conjQuot Y).ker = Subgroup.centralizer (Y : Set X) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
  constructor
  · intro hg y hy
    have hc : ∀ y : Y, (MulAut.conjNormal g y)⁻¹ * y ∈ Subgroup.center Y := by
      intro y
      have := congrArg (fun f => f (QuotientGroup.mk y)) hg
      simp only [conjQuot_mk, MulAut.one_apply] at this
      exact QuotientGroup.eq.mp this
    let c : Y → Subgroup.center Y := fun y => ⟨_, hc y⟩
    have hmul : ∀ a b : Y, c (a * b) = c a * c b := by
      intro a b
      apply Subtype.ext
      show (MulAut.conjNormal g (a * b))⁻¹ * (a * b) =
        ((MulAut.conjNormal g a)⁻¹ * a) * ((MulAut.conjNormal g b)⁻¹ * b)
      have h2 := Subgroup.mem_center_iff.mp (hc a) (MulAut.conjNormal g b)⁻¹
      rw [map_mul, mul_inv_rev]
      calc _ = ((MulAut.conjNormal g b)⁻¹ * (((MulAut.conjNormal g a)⁻¹ * a))) * b := by
            simp only [mul_assoc]
        _ = _ := by rw [h2]; simp only [mul_assoc]
    let φ : Y →* Subgroup.center Y := MonoidHom.mk' c hmul
    have := congrArg (fun f => ((f ⟨y, hy⟩ : Subgroup.center Y) : Y)) (hY φ)
    have h5 : (MulAut.conjNormal g ⟨y, hy⟩)⁻¹ * ⟨y, hy⟩ = (1 : Y) := this
    have h6 := congrArg Subtype.val h5
    simp [MulAut.conjNormal_apply] at h6
    have h7 : g * (y⁻¹ * g⁻¹) = y⁻¹ := eq_inv_of_mul_eq_one_left h6
    have h8 : Commute g y⁻¹ := by
      have := congrArg (· * g) h7
      simpa [mul_assoc, Commute, SemiconjBy] using this
    simpa using (Commute.inv_right h8).symm.eq
  · intro hg
    ext x
    induction x using QuotientGroup.induction_on with | _ y => ?_
    rw [conjQuot_mk]
    congr 1
    apply Subtype.ext
    simp [MulAut.conjNormal_apply]
    rw [mul_inv_eq_iff_eq_mul]; exact (hg _ y.2).symm

theorem transvection_pow {K : Type} [Field K] {i j : Fin 2} (h : i ≠ j) (c : K) (n : ℕ) :
    (Matrix.SpecialLinearGroup.transvection h c) ^ n =
      Matrix.SpecialLinearGroup.transvection h (n * c) := by
  induction n with
  | zero => simp [Matrix.SpecialLinearGroup.transvection_coeff_zero]
  | succ n ih =>
    rw [pow_succ, ih]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul]
    show Matrix.transvection i j (n * c) * Matrix.transvection i j c = Matrix.transvection i j ((n + 1 : ℕ) * c)
    rw [Matrix.transvection_mul_transvection_same _ _ h]
    push_cast
    rw [add_mul, one_mul]

/-- (2) -/
theorem sl2_hom_trivial (K : Type) [Field K] [Finite K] (hK : ringChar K ≠ 2) {A : Type*}
    [CommGroup A] (hA : ∀ a : A, a ^ 2 = 1) (φ : SL(2, K) →* A) : φ = 1 := by
  have hp : (ringChar K).Prime := by
    have := Fintype.ofFinite K
    exact CharP.char_is_prime K _
  have hcop : Nat.Coprime 2 (ringChar K) := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hK)
  ext g
  refine Matrix.SL2.transvection_induction (fun g => φ g = 1) ?_ ?_ g
  · intro i j h c
    have h1 : (φ (Matrix.SpecialLinearGroup.transvection h c)) ^ ringChar K = 1 := by
      rw [← map_pow, transvection_pow]
      have : ((ringChar K : ℕ) : K) = 0 := by simp
      rw [this, zero_mul, Matrix.SpecialLinearGroup.transvection_coeff_zero, map_one]
    have h2 := hA (φ (Matrix.SpecialLinearGroup.transvection h c))
    have := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h1)
    rw [hcop] at this
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp this)
  · intro a b ha hb
    simp [ha, hb]

/-- (3) -/
theorem sl2_center_sq (K : Type) [Field K] (c : SL(2, K)) (hc : c ∈ Subgroup.center SL(2, K)) :
    c ^ 2 = 1 := by
  obtain ⟨r, hr, hrc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  simp only [Fintype.card_fin] at hr
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, pow_two, ← hrc, ← map_mul, ← pow_two, hr, map_one]
  rfl

theorem subsingleton_ringEquiv_of_card_three (K : Type) [Field K] [Finite K]
    (h3 : Nat.card K = 3) : Subsingleton (K ≃+* K) := by
  have := Fintype.ofFinite K
  have hc : Fintype.card K = 3 := by rw [← Nat.card_eq_fintype_card]; exact h3
  have hp : Nat.Prime 3 := by norm_num
  let e : ZMod 3 ≃+* K := ZMod.ringEquivOfPrime K hp hc
  refine ⟨fun σ τ => ?_⟩
  have key : ∀ σ : K ≃+* K, σ = RingEquiv.refl K := by
    intro σ
    ext x
    obtain ⟨y, rfl⟩ := e.surjective x
    have := Subsingleton.elim (σ.toRingHom.comp e.toRingHom) e.toRingHom
    exact congrArg (fun f : ZMod 3 →+* K => f y) this
  rw [key σ, key τ]

/-- (5) -/
theorem card_PGammaL2_of_card_three (K : Type) [Field K] [Finite K] (h3 : Nat.card K = 3) :
    Nat.card (PGammaL2 K) = 24 := by
  have hs := subsingleton_ringEquiv_of_card_three K h3
  have e : PGammaL2 K ≃ PGL2 K × (K ≃+* K) :=
    { toFun := fun x => (x.left, x.right)
      invFun := fun p => ⟨p.1, p.2⟩
      left_inv := fun x => rfl
      right_inv := fun p => rfl }
  rw [Nat.card_congr e, Nat.card_prod, LinearTwo.card_PGL2, h3]
  have : Nat.card (K ≃+* K) = 1 := Nat.card_unique
  rw [this]
  norm_num

instance centerCommGroup {G : Type*} [Group G] : CommGroup (Subgroup.center G) :=
  { (inferInstance : Group (Subgroup.center G)) with
    mul_comm := fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a) }

theorem hom_center_trivial_of_sl2 {K : Type} [Field K] [Finite K] (hK : ringChar K ≠ 2)
    (Y : Subgroup X) (eY : Y ≃* SL(2, K)) (φ : Y →* Subgroup.center Y) : φ = 1 := by
  have hA : ∀ a : Subgroup.center Y, a ^ 2 = 1 := by
    intro a
    have h1 : eY (a : Y) ∈ Subgroup.center SL(2, K) := by
      rw [← Subgroup.map_center_eq eY]
      exact Subgroup.mem_map_of_mem _ a.2
    have h2 := sl2_center_sq K _ h1
    apply Subtype.ext
    apply eY.injective
    simpa [pow_two] using h2
  have := sl2_hom_trivial K hK (A := Subgroup.center Y) hA (φ.comp eY.symm.toMonoidHom)
  ext y
  have := congrArg (fun f => f (eY y)) this
  simpa using this

theorem exists_hom_aux [SemilinearEquivAut.{0}] {K : Type} [Field K] [Finite K]
    (hK : ringChar K ≠ 2) (Y : Subgroup X) [Y.Normal] (eY : Y ≃* SL(2, K)) :
    ∃ Φ : X →* PGammaL2 K, Φ.ker = Subgroup.centralizer (Y : Set X) ∧
      commutator X ≤ Y ⊔ Φ.ker := by
  obtain ⟨e, he⟩ := SemilinearEquivAut.semilinearEquivAut K
  let ψ : Y ⧸ Subgroup.center Y ≃* PSL2 K :=
    QuotientGroup.congr (Subgroup.center Y) (Subgroup.center SL(2, K)) eY
      (Subgroup.map_center_eq _)
  let Φ : X →* PGammaL2 K :=
    (e.symm : MulAut (PSL2 K) →* PGammaL2 K).comp
      ((MulAut.congr ψ : MulAut _ →* MulAut _).comp (conjQuot Y))
  have hker : Φ.ker = Subgroup.centralizer (Y : Set X) := by
    rw [← ker_conjQuot Y (hom_center_trivial_of_sl2 hK Y eY)]
    ext g
    simp only [MonoidHom.mem_ker]
    show e.symm (MulAut.congr ψ (conjQuot Y g)) = 1 ↔ _
    rw [← map_one e.symm, e.symm.injective.eq_iff, ← map_one (MulAut.congr ψ),
      (MulAut.congr ψ).injective.eq_iff]
  have hY : ∀ y : Y, Φ y = SemidirectProduct.inl
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (QuotientGroup.mk (eY y) : PSL2 K)) := by
    intro y
    rw [← he]
    have : MulAut.congr ψ (conjQuot Y y) = MulAut.conj (QuotientGroup.mk (eY y) : PSL2 K) := by
      ext w
      obtain ⟨u, rfl⟩ := ψ.surjective w
      induction u using QuotientGroup.induction_on with | _ z => ?_
      simp [ψ, QuotientGroup.congr, conjQuot_mk, MulAut.congr]
      have hz : (MulAut.conjNormal (y : X) z) = y * z * y⁻¹ := Subtype.ext (by simp [MulAut.conjNormal_apply])
      rw [hz, map_mul, map_mul, map_inv]
      rfl
    show e.symm (MulAut.congr ψ (conjQuot Y y)) = _
    rw [this]
  refine ⟨Φ, hker, ?_⟩
  intro g hg
  have h1 : Φ g ∈ commutator (PGammaL2 K) := by
    have : Subgroup.map Φ (commutator X) ≤ commutator (PGammaL2 K) := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator]
      exact Subgroup.commutator_mono le_top le_top
    exact this (Subgroup.mem_map_of_mem Φ hg)
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := LinearTwo.commutator_PGammaL2_le K hK h1
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective x
  have h2 : Φ (eY.symm s : Y) = Φ g := by
    rw [hY, ← hx]
    simp
  have h3 : ((eY.symm s : Y) : X)⁻¹ * g ∈ Φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h2, inv_mul_cancel]
  have : g = ((eY.symm s : Y) : X) * (((eY.symm s : Y) : X)⁻¹ * g) := by group
  rw [this]
  exact Subgroup.mul_mem_sup (eY.symm s).2 h3

/-- (4a) -/
theorem commutator_le_of_normal_sl2 [SemilinearEquivAut.{0}] {K : Type} [Field K] [Finite K]
    (hK : ringChar K ≠ 2) (Y : Subgroup X) [Y.Normal] (eY : Y ≃* SL(2, K)) :
    commutator X ≤ Y ⊔ Subgroup.centralizer (Y : Set X) := by
  obtain ⟨Φ, h1, h2⟩ := exists_hom_aux hK Y eY
  rwa [h1] at h2

instance finite_PGammaL2 (K : Type) [Field K] [Finite K] : Finite (PGammaL2 K) := by
  have : Finite (K ≃+* K) := Finite.of_injective (fun σ : K ≃+* K => (σ : K → K))
    DFunLike.coe_injective
  have : Finite (GL (Fin 2) K) := Finite.of_injective
    (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K)) Units.val_injective
  have : Finite (PGL2 K) := inferInstanceAs (Finite (GL (Fin 2) K ⧸ Subgroup.center _))
  exact Finite.of_equiv (PGL2 K × (K ≃+* K))
    { toFun := fun p => ⟨p.1, p.2⟩
      invFun := fun x => (x.left, x.right)
      left_inv := fun p => rfl
      right_inv := fun x => rfl }

/-- (4b) -/
theorem card_le_of_normal_sl2 [SemilinearEquivAut.{0}] {K : Type} [Field K] [Finite K]
    (hK : ringChar K ≠ 2) (Y : Subgroup X) [Y.Normal] (eY : Y ≃* SL(2, K)) :
    Nat.card X ≤ Nat.card (Subgroup.centralizer (Y : Set X)) * Nat.card (PGammaL2 K) := by
  obtain ⟨Φ, h1, -⟩ := exists_hom_aux hK Y eY
  rw [← h1, ← Subgroup.card_ker_mul_card_range Φ]
  exact Nat.mul_le_mul_left _ (Subgroup.card_le_card_group _)

theorem hom_trivial_of_perfect {Y : Subgroup X} (hperf : commutator Y = ⊤)
    {A : Type*} [CommGroup A] (φ : Y →* A) : φ = 1 := by
  have : (⊤ : Subgroup Y) ≤ φ.ker := by
    rw [← hperf, commutator_def, Subgroup.commutator_le]
    intro g _ h _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm.mpr
      (mul_comm _ _)]
  ext y
  simpa [MonoidHom.mem_ker] using this (Subgroup.mem_top y)

/-- (6) -/
theorem exists_hom_perm_seven [AutAlternatingBijectiveConj] (Y : Subgroup X) [Y.Normal]
    (hperf : commutator Y = ⊤) (e : Y ⧸ Subgroup.center Y ≃* alternatingGroup (Fin 7)) :
    ∃ ψ : X →* Equiv.Perm (Fin 7), ψ.ker = Subgroup.centralizer (Y : Set X) := by
  have hb := AutAlternatingBijectiveConj.aut_alternatingGroup_bijective_conj 7 (by norm_num)
    (by norm_num)
  let c : Equiv.Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) := MulEquiv.ofBijective _ hb
  refine ⟨(c.symm : MulAut _ →* _).comp (((MulAut.congr e).toMonoidHom : MulAut (Y ⧸ Subgroup.center Y) →* MulAut (alternatingGroup (Fin 7))).comp (conjQuot Y)), ?_⟩
  rw [← ker_conjQuot Y (fun φ => hom_trivial_of_perfect hperf φ)]
  ext g
  simp only [MonoidHom.mem_ker]
  show c.symm (MulAut.congr e (conjQuot Y g)) = 1 ↔ _
  rw [← map_one c.symm, c.symm.injective.eq_iff, ← map_one (MulAut.congr e),
    (MulAut.congr e).injective.eq_iff]

end CFSGOutside.GiuliettiKorchmaros.Key
