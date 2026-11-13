import CFSGOutside.ChillagSonn.Metacyclic
import CFSGOutside.ChillagSonn.Unipotent
import CFSGOutside.Corpus.SchurMultipliers

/-!
# Lemma (1.7) of Chillag–Sonn

If `Y ⊴ X` is cyclic of order 3 or 6 and `X/Y` is `PSL(2,9)`, `PGL(2,9)`, `PGL*(2,9)` or `A₇`, then `X` is not
Sylow-metacyclic.

Instead of Huppert IV.8.6 we use that `PSL(2,9)` (hence each of the four groups) has a subgroup `U` of order 9 and
exponent 3 inverted by conjugation by a square `E²`. After reducing to `|Y| = 3`, the preimage `Q` of `U` is a 3-group
of order 27, so, being metacyclic, it has an element `x` with `x³ ≠ 1`. A lift `w` of `E²` is a square, so it
centralizes `Y` (`|Aut Y| = 2`), and `w x w⁻¹ = x⁻¹ y` with `y ∈ Y` central in `Q`; hence `x³ = w x³ w⁻¹ = x⁻³`,
and `x⁹ = 1` gives `x³ = 1`.
-/

namespace CFSGOutside.ChillagSonn

open CFSGOutside.Corpus CFSGOutside.Corpus.GorensteinWalter Matrix
open scoped MatrixGroups

/-- `G` has a subgroup of order 9 and exponent 3 inverted by conjugation by a square `E²`. -/
def HasInvertedNine (G : Type*) [Group G] : Prop :=
  ∃ (U : Subgroup G) (E : G), Nat.card U = 9 ∧ (∀ g ∈ U, g ^ 3 = 1) ∧ ∀ g ∈ U, E ^ 2 * g * (E ^ 2)⁻¹ = g⁻¹

/-- `HasInvertedNine` passes to overgroups. -/
theorem HasInvertedNine.of_injective {H G : Type*} [Group H] [Group G] (h : HasInvertedNine H) (j : H →* G)
    (hj : Function.Injective j) : HasInvertedNine G := by
  obtain ⟨U, E, hU, h3, hE⟩ := h
  refine ⟨U.map j, j E, by rw [Subgroup.card_map_of_injective hj, hU], ?_, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩; rw [← map_pow, h3 g hg, map_one]
  · rintro _ ⟨g, hg, rfl⟩; rw [← map_pow, ← map_inv, ← map_mul, ← map_mul, hE g hg, map_inv]

/-- `|H| = |ker f| · |f(H)|` when `ker f ≤ H`. -/
theorem card_eq_card_ker_mul {A B : Type*} [Group A] [Group B] (f : A →* B) {H : Subgroup A} (hH : f.ker ≤ H) :
    Nat.card H = Nat.card f.ker * Nat.card (H.map f) := by
  rw [← (f.domRestrict H).ker.card_mul_index, Subgroup.index_ker, MonoidHom.domRestrict_range,
    MonoidHom.ker_domRestrict, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv]

/-- If `|Aut Y| = 2`, an element of odd order centralizes `Y`. -/
theorem conj_eq_of_odd {X : Type*} [Group X] {Y : Subgroup X} [Y.Normal] (hA : Nat.card (MulAut Y) = 2) {x : X}
    {n : ℕ} (hn : x ^ n = 1) (hn2 : Nat.Coprime n 2) {y : X} (hy : y ∈ Y) : x * y * x⁻¹ = y := by
  have h1 : MulAut.conjNormal (H := Y) x = 1 := by
    rw [← orderOf_eq_one_iff, ← Nat.dvd_one, ← hn2.gcd_eq_one]
    refine Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one ?_) (hA ▸ orderOf_dvd_natCard _)
    rw [← map_pow, hn, map_one]
  simpa only [MulAut.conjNormal_apply, MulAut.one_apply] using
    congrArg (fun σ : MulAut Y => ((σ ⟨y, hy⟩ : Y) : X)) h1

/-- If `|Aut Y| = 2`, squares centralize `Y`. -/
theorem sq_conj_eq {X : Type*} [Group X] {Y : Subgroup X} [Y.Normal] (hA : Nat.card (MulAut Y) = 2) (d : X)
    {y : X} (hy : y ∈ Y) : d ^ 2 * y * (d ^ 2)⁻¹ = y := by
  have h1 : MulAut.conjNormal (H := Y) (d ^ 2) = 1 := by rw [map_pow, ← hA, pow_card_eq_one']
  simpa only [MulAut.conjNormal_apply, MulAut.one_apply] using
    congrArg (fun σ : MulAut Y => ((σ ⟨y, hy⟩ : Y) : X)) h1

/-- The core case: a surjection onto a group with an inverted subgroup of order 9, with kernel of order 3. -/
theorem not_sylowMetacyclic_of_ker_three {X G : Type*} [Group X] [Group G] [Finite X] (φ : X →* G)
    (hφ : Function.Surjective φ) (hk : Nat.card φ.ker = 3) (hG : HasInvertedNine G) : ¬ SylowMetacyclic X := by
  intro hX
  obtain ⟨U, E, hU, h3, hE⟩ := hG
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsCyclic φ.ker := isCyclic_of_prime_card hk
  have hA : Nat.card (MulAut φ.ker) = 2 := by rw [IsCyclic.card_mulAut, hk]; rfl
  have hY3 : ∀ y ∈ φ.ker, y ^ 3 = 1 := fun y hy => by
    have h := pow_card_eq_one' (x := (⟨y, hy⟩ : φ.ker))
    rw [hk] at h
    simpa using congrArg Subtype.val h
  set Q := U.comap φ
  have hQ3 : ∀ x ∈ Q, x ^ 3 ∈ φ.ker := fun x hx => by rw [MonoidHom.mem_ker, map_pow]; exact h3 (φ x) hx
  have hQ9 : ∀ x ∈ Q, x ^ 9 = 1 := fun x hx => by
    rw [show 9 = 3 * 3 from rfl, pow_mul]; exact hY3 _ (hQ3 x hx)
  have hQp : IsPGroup 3 Q := fun x => ⟨2, Subtype.ext (by simpa using hQ9 x x.2)⟩
  have hQc : Nat.card Q = 27 := by
    rw [card_eq_card_ker_mul φ (MonoidHom.ker_le_comap φ U), hk, Subgroup.map_comap_eq_self_of_surjective hφ, hU]
  obtain ⟨x, hxQ, hx⟩ : ∃ x ∈ Q, x ^ 3 ≠ 1 := by
    by_contra! h
    have := hX.card_dvd_sq Q hQp h
    rw [hQc] at this; norm_num at this
  obtain ⟨d, rfl⟩ := hφ E
  have hy : x * (d ^ 2 * x * (d ^ 2)⁻¹) ∈ φ.ker := by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv, map_pow]
    rw [hE (φ x) hxQ, mul_inv_cancel]
  have hc : Commute x⁻¹ (x * (d ^ 2 * x * (d ^ 2)⁻¹)) :=
    Commute.inv_left (mul_inv_eq_iff_eq_mul.mp (conj_eq_of_odd hA (hQ9 x hxQ) (by norm_num) hy))
  have h1 : (d ^ 2 * x * (d ^ 2)⁻¹) ^ 3 = x ^ 3 := by rw [conj_pow, sq_conj_eq hA d (hQ3 x hxQ)]
  rw [show d ^ 2 * x * (d ^ 2)⁻¹ = x⁻¹ * (x * (d ^ 2 * x * (d ^ 2)⁻¹)) by group, hc.mul_pow, hY3 _ hy,
    mul_one, inv_pow, inv_eq_iff_mul_eq_one] at h1
  have h9 := hQ9 x hxQ
  rw [show 9 = 3 + 3 + 3 from rfl, pow_add, pow_add, h1, one_mul] at h9
  exact hx h9

/-- The case `|ker φ| = 6`, reduced to `|ker φ| = 3` by factoring out the subgroup of order 2 of `ker φ`. -/
theorem not_sylowMetacyclic_of_ker_six {X G : Type*} [Group X] [Group G] [Finite X] (φ : X →* G)
    (hφ : Function.Surjective φ) (hc : IsCyclic φ.ker) (hk : Nat.card φ.ker = 6) (hG : HasInvertedNine G) :
    ¬ SylowMetacyclic X := by
  intro hX
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := φ.ker)
  have hog : orderOf (g : X) = 6 := by rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hk]
  set N := Subgroup.zpowers ((g : X) ^ 3)
  have hN : N.Normal := ⟨fun n hn h => by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨h * g * h⁻¹, φ.normal_ker.conj_mem _ g.2 h⟩)
    have hm' : (g : X) ^ m = h * g * h⁻¹ := by simpa using congrArg Subtype.val hm
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    refine Subgroup.mem_zpowers_iff.mpr ⟨m * k, ?_⟩
    rw [← conj_zpow, ← conj_pow, ← hm', ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_mul,
      ← _root_.zpow_mul]
    congr 1; push_cast; ring⟩
  have hNk : N ≤ φ.ker := (Subgroup.zpowers_le).mpr (pow_mem g.2 3)
  have hN2 : Nat.card N = 2 := by
    rw [Nat.card_zpowers, orderOf_pow_of_dvd (by norm_num) (by rw [hog]; norm_num), hog]
  have hcard := card_eq_card_ker_mul (QuotientGroup.mk' N) (H := φ.ker) (by rwa [QuotientGroup.ker_mk'])
  rw [QuotientGroup.ker_mk', hk, hN2] at hcard
  refine not_sylowMetacyclic_of_ker_three (QuotientGroup.lift N φ hNk)
    (QuotientGroup.lift_surjective_of_surjective _ _ hφ hNk) ?_ hG (hX.quotient N)
  rw [QuotientGroup.ker_lift]
  omega

/-- Reduction to surjections: `X/Y ≅ G` with `G` as in `HasInvertedNine`. -/
theorem not_sylowMetacyclic_of_quotient {X G : Type*} [Group X] [Finite X] [Group G] (Y : Subgroup X) [Y.Normal]
    (hYc : IsCyclic Y) (hY : Nat.card Y = 3 ∨ Nat.card Y = 6) (e : X ⧸ Y ≃* G) (hG : HasInvertedNine G) :
    ¬ SylowMetacyclic X := by
  set φ := e.toMonoidHom.comp (QuotientGroup.mk' Y)
  have hker : φ.ker = Y := by ext x; simp [φ, QuotientGroup.eq_one_iff]
  have hφ : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective Y)
  rw [← hker] at hY hYc
  rcases hY with h | h
  · exact not_sylowMetacyclic_of_ker_three φ hφ h hG
  · exact not_sylowMetacyclic_of_ker_six φ hφ hYc h hG

/-! ### `PSL(2, 9)` -/

section PSL

variable (F : Type) [Field F]

/-- `b ↦ !![1, b; 0, 1]` as a homomorphism into `SL(2, F)`. -/
def unipSL : Multiplicative F →* SL(2, F) where
  toFun b := ⟨!![1, b.toAdd; 0, 1], by simp [Matrix.det_fin_two]⟩
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> rfl
  map_mul' a b := by
    ext i j
    change (!![1, (a * b).toAdd; 0, 1] : Matrix (Fin 2) (Fin 2) F) i j =
      (!![1, a.toAdd; 0, 1] * !![1, b.toAdd; 0, 1] : Matrix (Fin 2) (Fin 2) F) i j
    rw [Matrix.mul_fin_two]; fin_cases i <;> fin_cases j <;> simp [add_comm]

/-- For `|F| = 9`, `PSL(2, F)` has an inverted subgroup of order 9. -/
theorem hasInvertedNine_PSL2 [Finite F] (hF : Nat.card F = 9) : HasInvertedNine (PSL2 F) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP F 3 := charP_of_card_eq_pow (f := 2) (by norm_num) hF
  set u : Multiplicative F →* PSL2 F := (QuotientGroup.mk' _).comp (unipSL F)
  have hu : Function.Injective u := by
    rw [injective_iff_map_eq_one]
    intro b hb
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hb
    obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hb
    have := congrArg (fun M => M 0 1) hr
    simp [unipSL] at this
    exact Multiplicative.toAdd.injective this.symm
  obtain ⟨ε, hε⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  rw [Nat.card_units, hF] at hε
  set a : F := (ε : F)
  have ha0 : a ≠ 0 := ε.ne_zero
  have ha4 : a ^ 4 = -1 := by
    have h8 : (a ^ 4) ^ 2 = 1 := by
      rw [← pow_mul, ← Units.val_pow_eq_pow_val, show 4 * 2 = 9 - 1 from rfl, ← hε, pow_orderOf_eq_one,
        Units.val_one]
    refine (sq_eq_one_iff.mp h8).resolve_left fun h => ?_
    exact pow_ne_one_of_lt_orderOf (n := 4) (by norm_num) (by rw [hε]; norm_num)
      (Units.ext (by simpa using h))
  let T : SL(2, F) := ⟨!![a, 0; 0, a⁻¹], by simp [Matrix.det_fin_two, ha0]⟩
  refine ⟨u.range, QuotientGroup.mk' (Subgroup.center SL(2, F)) T, ?_, ?_, ?_⟩
  · rw [← Nat.card_congr (MonoidHom.ofInjective hu).toEquiv, Nat.card_congr Multiplicative.toAdd, hF]
  · have h3 : (3 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 3
    rintro _ ⟨b, rfl⟩
    rw [← map_pow, show b ^ 3 = 1 from Multiplicative.toAdd.injective (by simp [nsmul_eq_mul, h3]), map_one]
  · rintro _ ⟨b, rfl⟩
    simp only [u, MonoidHom.comp_apply]
    rw [← map_pow, ← map_inv, ← map_mul, ← map_mul, ← map_inv]
    congr 1
    rw [mul_inv_eq_iff_eq_mul, ← map_inv, pow_two]
    ext i j
    change (!![a, 0; 0, a⁻¹] * !![a, 0; 0, a⁻¹] * !![1, b.toAdd; 0, 1] : Matrix (Fin 2) (Fin 2) F) i j =
      (!![1, (b⁻¹).toAdd; 0, 1] * (!![a, 0; 0, a⁻¹] * !![a, 0; 0, a⁻¹]) : Matrix (Fin 2) (Fin 2) F) i j
    simp only [Matrix.mul_fin_two]
    fin_cases i <;> fin_cases j <;> simp
    field_simp
    linear_combination b.toAdd * ha4

/-- `PSL(2, F)` inside `PGL*(2, F)`. -/
noncomputable def pslToPGLStar : PSL2 F →* PGLStar F :=
  ((SemidirectProduct.inl).comp ProjectiveSpecialLinearGroup.toPGL).codRestrict (PGLStar F) fun a =>
    Subgroup.subset_closure (Or.inl ⟨by simp, a, by simp⟩)

theorem pslToPGLStar_injective : Function.Injective (pslToPGLStar F) := fun a b h =>
  ProjectiveSpecialLinearGroup.toPGL_injective (SemidirectProduct.inl_injective (congrArg Subtype.val h))

/-- `A₆` inside `A₇`. -/
noncomputable def altSixToSeven : alternatingGroup (Fin 6) →* alternatingGroup (Fin 7) :=
  ((Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb).comp (alternatingGroup (Fin 6)).subtype).codRestrict _ fun σ => by
    rw [MonoidHom.comp_apply, Equiv.Perm.mem_alternatingGroup, Equiv.Perm.viaEmbeddingHom_apply,
      Equiv.Perm.viaEmbedding, Equiv.Perm.sign_extendDomain]
    exact σ.2

theorem altSixToSeven_injective : Function.Injective altSixToSeven := fun a b h =>
  Subtype.ext (Equiv.Perm.viaEmbeddingHom_injective _ (congrArg Subtype.val h))

end PSL

open CFSGOutside.Corpus CFSGOutside.Corpus.GorensteinWalter in
/-- **Chillag–Sonn, Lemma (1.7).** -/
theorem lemma_1_7 [FieldNineAlternatingSix.{0}] {X : Type} [Group X] [Finite X] (Y : Subgroup X) [Y.Normal]
    (hYc : IsCyclic Y) (hY : Nat.card Y = 3 ∨ Nat.card Y = 6) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 9)
    (hX : Nonempty (X ⧸ Y ≃* PSL2 F) ∨ Nonempty (X ⧸ Y ≃* PGL2 F) ∨ Nonempty (X ⧸ Y ≃* PGLStar F) ∨
      Nonempty (X ⧸ Y ≃* alternatingGroup (Fin 7))) :
    ¬ SylowMetacyclic X := by
  have h := hasInvertedNine_PSL2 F hF
  rcases hX with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact not_sylowMetacyclic_of_quotient Y hYc hY e h
  · exact not_sylowMetacyclic_of_quotient Y hYc hY e
      (h.of_injective _ ProjectiveSpecialLinearGroup.toPGL_injective)
  · exact not_sylowMetacyclic_of_quotient Y hYc hY e (h.of_injective _ (pslToPGLStar_injective F))
  · have := Fintype.ofFinite F
    obtain ⟨eA⟩ := FieldNineAlternatingSix.unique_field_nine_projective_linear_alternating_six_isomorphism F
      (by rw [← Nat.card_eq_fintype_card, hF])
    exact not_sylowMetacyclic_of_quotient Y hYc hY e
      (h.of_injective (altSixToSeven.comp eA.toMonoidHom) (altSixToSeven_injective.comp eA.injective))

end CFSGOutside.ChillagSonn
