import CFSGOutside.ChillagSonn.Fact5C

/-!
# Fact 5 of Chillag–Sonn: `PGL*(2, p²)` has no stem extension by a group of order 2

Let `D ≤ Z(A) ∩ A'` have order 2 with `A/D ≅ PGL*(2, F)`, `|F| = p²`, `p` odd. The preimage `A₀` of `PSL(2, F)` is
perfect, hence `A₀ ≅ SL(2, F)`, compatibly with `A₀/D ≅ PSL(2, F)`. For `t ∈ A ∖ A₀` mapping to `(ḡ, σ)`, conjugation by
`t` acts on `SL(2, F)` as `x ↦ g σ(x) g⁻¹`; with `s` the image of `t²` this gives `g σ(g) = s λ`, `g σ(s) = s g`, so
`det g` is a square, contradicting `ḡ ∉ PSL(2, F)`.
-/

noncomputable section

namespace CFSGOutside.ChillagSonn

open CFSGOutside.Corpus CFSGOutside.Corpus.GorensteinWalter Matrix SemidirectProduct
open scoped MatrixGroups

/-- The map `PSL(2, F) → PΓL(2, F)` onto `pslInPGammaL F`. -/
def toPslInPGammaL (F : Type) [Field F] : PSL2 F →* pslInPGammaL F :=
  ((inl : PGL2 F →* PGammaL2 F).comp ProjectiveSpecialLinearGroup.toPGL).codRestrict _ fun y =>
    Subgroup.mem_map_of_mem _ ⟨y, rfl⟩

/-- `toPslInPGammaL F` is bijective. -/
theorem toPslInPGammaL_bijective (F : Type) [Field F] : Function.Bijective (toPslInPGammaL F) := by
  refine ⟨fun y z h => ProjectiveSpecialLinearGroup.toPGL_injective (inl_injective (congrArg Subtype.val h)), ?_⟩
  rintro ⟨_, _, ⟨y, rfl⟩, rfl⟩
  exact ⟨y, rfl⟩

/-- `PSL(2, F)` inside `PΓL(2, F)` is isomorphic to `PSL(2, F)`. -/
def pslInPGammaLEquiv (F : Type) [Field F] : pslInPGammaL F ≃* PSL2 F :=
  (MulEquiv.ofBijective _ (toPslInPGammaL_bijective F)).symm

/-- `pslInPGammaLEquiv F` inverts `y ↦ inl (toPGL y)`. -/
theorem inl_toPGL_pslInPGammaLEquiv {F : Type} [Field F] (x : pslInPGammaL F) :
    inl (ProjectiveSpecialLinearGroup.toPGL (pslInPGammaLEquiv F x)) = (x : PGammaL2 F) :=
  congrArg Subtype.val ((MulEquiv.ofBijective _ (toPslInPGammaL_bijective F)).apply_symm_apply x)

open CFSGOutside.Corpus CFSGOutside.Corpus.GorensteinWalter in
/-- **Fact 5 of Chillag–Sonn.** `PGL*(2, p²)` has no stem extension by a group of order 2. -/
theorem not_isDoubleStemCover_pglStar [SemilinearEquivAut.{0}] [PslTwoHopfMultiplier] [HopfMultiplierAlternating]
    [CardHopfMultiplierEqCardGriess] [FieldNineAlternatingSix.{0}] [HopfCentralCoverConsequences]
    {A : Type} [Group A] [Finite A] {F : Type} [Field F] [Finite F] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hF : Nat.card F = p ^ 2) [IsSimpleGroup (PSL2 F)] (hnab : ∃ a b : PSL2 F, a * b ≠ b * a)
    (h : IsDoubleStemCover A (PGLStar F)) : False := by
  obtain ⟨D, hDn, hD, hD2, ⟨e⟩⟩ := h
  have := Fact.mk hp
  have := Fintype.ofFinite F
  have : CharP F p := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hF])
  have hK : ringChar F ≠ 2 := by rw [ringChar.eq F p]; exact hp2
  have haut := card_ringEquiv hF
  have huniq := (Nat.card_eq_two_iff' (1 : F ≃+* F)).mp haut
  have hsq : ∀ τ : F ≃+* F, τ * τ = 1 := fun τ => by
    have := pow_card_eq_one' (x := τ); rwa [haut, sq] at this
  have h5 : 5 ≤ Nat.card F := by
    have := hp.two_le
    have : 3 ≤ p := by omega
    rw [hF]; nlinarith
  -- the map `A → PΓL(2, F)` with kernel `D` and image `PGL*(2, F)`
  let π : A →* PGammaL2 F := (PGLStar F).subtype.comp (e.toMonoidHom.comp (QuotientGroup.mk' D))
  have hπmem : ∀ a, π a ∈ PGLStar F := fun a => (e (QuotientGroup.mk a)).2
  have hπsurj : ∀ y ∈ PGLStar F, ∃ a, π a = y := fun y hy => by
    obtain ⟨q, hq⟩ := e.surjective ⟨y, hy⟩
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨a, congrArg Subtype.val hq⟩
  have hπker : ∀ a, π a = 1 ↔ a ∈ D := fun a => by
    change ((e (a : A ⧸ D) : PGammaL2 F)) = 1 ↔ _
    rw [OneMemClass.coe_eq_one, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  -- the index-2 subgroup `A₀`
  let ρ : A →* (F ≃+* F) := rightHom.comp π
  let A₀ := ρ.ker
  have hA₀mem : ∀ a, a ∈ A₀ ↔ (π a).right = 1 := fun a => Iff.rfl
  obtain ⟨σ, hσ⟩ := huniq.exists
  obtain ⟨x, hx, hxr⟩ := exists_mem_pglStar_right hK hσ
  obtain ⟨t, rfl⟩ := hπsurj x hx
  have hρsurj : Function.Surjective ρ := fun τ => by
    by_cases hτ : τ = 1
    · exact ⟨1, by simp [hτ]⟩
    · exact ⟨t, by rw [huniq.unique hτ hσ]; exact hxr⟩
  have hidx : A₀.index = 2 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hρsurj, Subgroup.card_top, haut]
  have hDA₀ : D ≤ A₀ := fun d hd => by rw [hA₀mem, (hπker d).mpr hd]; rfl
  have hA₀π : ∀ a ∈ A₀, π a ∈ pslInPGammaL F := fun a ha => by
    have hr : (π a).right = 1 := ha
    refine ⟨(π a).left, (right_eq_one_iff_of_mem_pglStar hK haut (hπmem a)).mp hr, ?_⟩
    ext <;> simp [hr]
  -- `A₀ → PSL(2, F)`
  let θ : A₀ →* PSL2 F := (pslInPGammaLEquiv F).toMonoidHom.comp
    ((π.comp A₀.subtype).codRestrict _ fun a => hA₀π a a.2)
  have hθ : ∀ a : A₀, inl (ProjectiveSpecialLinearGroup.toPGL (θ a)) = π a := fun a =>
    inl_toPGL_pslInPGammaLEquiv _
  have hθsurj : Function.Surjective θ := fun y => by
    have hy : inl (ProjectiveSpecialLinearGroup.toPGL y) ∈ PGLStar F :=
      Subgroup.subset_closure (Or.inl ⟨rfl, y, rfl⟩)
    obtain ⟨a, ha⟩ := hπsurj _ hy
    have haA : a ∈ A₀ := by rw [hA₀mem, ha]; rfl
    refine ⟨⟨a, haA⟩, ProjectiveSpecialLinearGroup.toPGL_injective
      (inl_injective (φ := pgl2FieldAut F) (G := F ≃+* F) ?_)⟩
    rw [hθ]; exact ha
  have hθker : θ.ker = D.subgroupOf A₀ := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hπker, ← hθ a, map_eq_one_iff _ inl_injective,
      map_eq_one_iff _ ProjectiveSpecialLinearGroup.toPGL_injective]
  have hperf : commutator A₀ = ⊤ :=
    commutator_eq_top_of_stem hnab D (hD.trans inf_le_right) hD2 A₀ hidx θ hθsurj hθker hDA₀
  have hDc : θ.ker ≤ Subgroup.center A₀ := by
    rw [hθker]
    intro a ha
    rw [Subgroup.mem_subgroupOf] at ha
    rw [Subgroup.mem_center_iff]
    intro b
    exact Subtype.ext (Subgroup.mem_center_iff.mp ((hD.trans inf_le_left) ha) b)
  have hker2 : Nat.card θ.ker = 2 := by
    rw [hθker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDA₀).toEquiv, hD2]
  -- `A₀ ≅ SL(2, F)`, compatibly with `θ`
  obtain ⟨η₀⟩ := nonempty_mulEquiv_sl2 hperf θ.ker hDc hker2 hK h5
    (QuotientGroup.quotientKerEquivOfSurjective θ hθsurj) hnab
  have hZ : Subgroup.center A₀ = θ.ker :=
    center_eq_of_simple_quotient θ.ker hDc (QuotientGroup.quotientKerEquivOfSurjective θ hθsurj) hnab
  have hkerη : ∀ a, θ a = 1 ↔ η₀ a ∈ Subgroup.center SL(2, F) := fun a => by
    rw [← MonoidHom.mem_ker, ← hZ, Subgroup.mem_center_iff, Subgroup.mem_center_iff]
    constructor
    · intro h y
      obtain ⟨b, rfl⟩ := η₀.surjective y
      rw [← map_mul, ← map_mul, h b]
    · intro h b
      apply η₀.injective
      rw [map_mul, map_mul, h]
  obtain ⟨η, hηsurj, hηc⟩ := exists_compatible_sl2 η₀ θ hθsurj hkerη
  have hπη : ∀ a : A₀, π a = inl (SpecialLinearGroup.toPGL (η a)) := fun a => by rw [← hθ, hηc]
  -- conjugation by `t` is `x ↦ g σ(x) g⁻¹`
  obtain ⟨g, hg⟩ := ProjGenLinGroup.mk_surjective (π t).left
  have hgT : ProjGenLinGroup.mk g ∉ pslT F := by
    rw [hg]
    intro h
    exact hσ (hxr ▸ (right_eq_one_iff_of_mem_pglStar hK haut (hπmem t)).mpr h)
  have hconj : ∀ a : A₀, η (MulAut.conjNormal t a) = semiConj g σ (η a) := by
    have := eq_of_toPGL_eq hperf (η.comp (MulAut.conjNormal t).toMonoidHom) ((semiConj g σ).comp η) fun a => by
      apply inl_injective (φ := pgl2FieldAut F) (G := F ≃+* F)
      change inl (SpecialLinearGroup.toPGL (η (MulAut.conjNormal t a))) =
        inl (SpecialLinearGroup.toPGL (semiConj g σ (η a)))
      rw [← hπη, MulAut.conjNormal_apply, map_mul, map_mul, map_inv, hπη a, conj_inl, toPGL_semiConj, hg, hxr]
    exact fun a => DFunLike.congr_fun this a
  -- the image `s` of `t²`
  have ht2 : t * t ∈ A₀ := by rw [hA₀mem, map_mul, mul_right, hxr, hsq]
  set a₀ : A₀ := ⟨t * t, ht2⟩
  set S := SpecialLinearGroup.toGL (η a₀)
  have E1 : g * GeneralLinearGroup.map (σ : F →+* F) S = S * g := by
    have h1 := hconj a₀
    have h2 : MulAut.conjNormal t a₀ = a₀ := Subtype.ext (by
      rw [MulAut.conjNormal_apply]; show t * (t * t) * t⁻¹ = t * t; group)
    rw [h2] at h1
    have h3 := congrArg SpecialLinearGroup.toGL h1
    rw [toGL_semiConj, eq_mul_inv_iff_mul_eq] at h3
    exact h3.symm
  have hcomm : ∀ y : SL(2, F), (S⁻¹ * (g * GeneralLinearGroup.map (σ : F →+* F) g)) * SpecialLinearGroup.toGL y =
      SpecialLinearGroup.toGL y * (S⁻¹ * (g * GeneralLinearGroup.map (σ : F →+* F) g)) := by
    intro y
    obtain ⟨a, rfl⟩ := hηsurj y
    have h1 : η (MulAut.conjNormal (t * t) a) = η a₀ * η a * (η a₀)⁻¹ := by
      rw [← map_mul, ← map_inv, ← map_mul]
      congr 1
    have h2 : η (MulAut.conjNormal (t * t) a) = semiConj g σ (semiConj g σ (η a)) := by
      rw [map_mul, MulAut.mul_apply, hconj, hconj]
    have h3 := congrArg SpecialLinearGroup.toGL (h1.symm.trans h2)
    rw [map_mul, map_mul, map_inv, toGL_semiConj, toGL_semiConj, map_mul, map_mul, map_inv,
      map_map_of_mul_self (hsq σ)] at h3
    have h4 : g * GeneralLinearGroup.map (σ : F →+* F) g * SpecialLinearGroup.toGL (η a) =
        S * SpecialLinearGroup.toGL (η a) * S⁻¹ * (g * GeneralLinearGroup.map (σ : F →+* F) g) := by
      rw [h3]; group
    calc _ = S⁻¹ * (g * GeneralLinearGroup.map (σ : F →+* F) g * SpecialLinearGroup.toGL (η a)) := by group
      _ = _ := by rw [h4]; group
  obtain ⟨u, hu⟩ := exists_scalar_of_comm _ hcomm
  have E2 : g * GeneralLinearGroup.map (σ : F →+* F) g = S * GeneralLinearGroup.scalar (Fin 2) u := by
    rw [← hu]; group
  have hS : GeneralLinearGroup.det S = 1 := Units.ext (by simp [S])
  exact not_isSquare_det hK g hgT (isSquare_det_of_semilinear hp hp2 hF hσ g S hS u E1 E2)

end CFSGOutside.ChillagSonn
