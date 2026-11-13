import CFSGOutside.Common.NonsolubleLength
import CFSGOutside.Corpus.Defs.ElemThompson
import CFSGOutside.Corpus.Schreier
import CFSGOutside.Wilson.Defs
import CFSGOutside.Wilson.Orbit
import CFSGOutside.Wilson.Radical
import CFSGOutside.Wilson.Sections

/-!
# Wilson, compact torsion groups: Lemma 4

**Paper.** J. S. Wilson, *On the structure of compact torsion groups*, Monatsh. Math. **96** (1983), 57–66,
Lemma 4 (p. 63) and its proof (p. 64).

**Lemma 4.** Write `A = ⟨u^{p^{a-1}} : u ∈ tQ⟩` (`a ≥ 1`) and `N` for the normal closure of `A` in `H`.
(i) `N` normalizes the simple direct factors of every perfect chief factor `L/M` of `H` with `L ≤ K` and `p`
dividing `|L/M|`. (ii) There are normal subgroups `K₁ ≤ K₂` of `K ∩ N` such that `K₁` is `p`-soluble, `K₂/K₁` is a
direct product of `𝔖_p`-groups and `(K ∩ N)/K₂` is soluble ("since Schreier's conjecture holds").

`lemma4` proves (ii), with `K₁ = O_{p-sol}(K ∩ N)` and `K₂/K₁ = E(Y)` for `Y = (K ∩ N)/K₁`. Part (i) is proved for the
components of `Y`, the only case (ii) uses (`Orbit.map_pow_eq_of_prod`). The classification enters through the
Schreier conjecture (`CFSGOutside.Corpus.Schreier`) and the classification statement.
-/

namespace CFSGOutside.Wilson

open Subgroup CFSGOutside.Corpus CFSGOutside.Corpus.LocalCores CFSGOutside.NonsolubleLength

section Sylow

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- A Sylow `p`-subgroup of `G` meets a subnormal subgroup `H` in a Sylow `p`-subgroup of `H`. -/
theorem isSylowOf_inf_of_isSubnormal (S : Sylow p G) {H : Subgroup G} (hH : H.IsSubnormal) :
    ABGLocalTools.IsSylowOf p ((S : Subgroup G) ⊓ H) H := by
  induction hH with
  | top =>
    rw [inf_top_eq, ABGLocalTools.isSylowOf_iff]
    exact ⟨le_top, S.isPGroup', by rw [Subgroup.relIndex_top_right]; exact S.not_dvd_index⟩
  | step H K hHK hK hN ih =>
    have h := ih.inf_of_le_normalizer hHK
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hHK).mp hN)
    rwa [inf_assoc, inf_eq_right.mpr hHK] at h

/-- A Sylow `p`-subgroup meets a subnormal subgroup of order divisible by `p` nontrivially. -/
theorem sylow_inf_ne_bot_of_isSubnormal (S : Sylow p G) {H : Subgroup G} (hH : H.IsSubnormal)
    (hp : p ∣ Nat.card H) : (S : Subgroup G) ⊓ H ≠ ⊥ := by
  obtain ⟨Q, hQ⟩ := isSylowOf_inf_of_isSubnormal S hH
  rw [← hQ]
  intro h
  rw [Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective] at h
  exact Q.ne_bot_of_dvd_card hp h

end Sylow

section Quotient

variable {G : Type*} [Group G]

/-- An automorphism of `G` preserving the characteristic subgroup `N` induces an automorphism of `G ⧸ N`. -/
def quotEquiv (N : Subgroup G) [N.Characteristic] (φ : MulAut G) : MulAut (G ⧸ N) :=
  QuotientGroup.congr N N φ (Subgroup.characteristic_iff_map_eq.mp inferInstance φ)

theorem quotEquiv_apply (N : Subgroup G) [N.Characteristic] (φ : MulAut G) (x : G) :
    quotEquiv N φ (QuotientGroup.mk' N x) = QuotientGroup.mk' N (φ x) :=
  QuotientGroup.congr_mk' N N φ (Subgroup.characteristic_iff_map_eq.mp inferInstance φ) x

/-- The action of `Aut G` on `G ⧸ N` for a characteristic subgroup `N`. -/
def quotAut (N : Subgroup G) [N.Characteristic] : MulAut G →* MulAut (G ⧸ N) where
  toFun := quotEquiv N
  map_one' := by
    ext x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
    change quotEquiv N (1 : MulAut G) (QuotientGroup.mk' N y) = QuotientGroup.mk' N y
    rw [quotEquiv_apply]
    rfl
  map_mul' φ ψ := by
    ext x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
    change quotEquiv N (φ * ψ) (QuotientGroup.mk' N y) =
      quotEquiv N φ (quotEquiv N ψ (QuotientGroup.mk' N y))
    rw [quotEquiv_apply, quotEquiv_apply, quotEquiv_apply]
    rfl

theorem quotAut_apply (N : Subgroup G) [N.Characteristic] (φ : MulAut G) (x : G) :
    quotAut N φ (QuotientGroup.mk' N x) = QuotientGroup.mk' N (φ x) :=
  quotEquiv_apply N φ x

end Quotient

theorem normal_map_of_char {Q : Type*} [Group Q] (R : Subgroup Q) [R.Normal]
    (P : Subgroup R) [P.Characteristic] : (P.map R.subtype).Normal := by
  refine ⟨?_⟩
  rintro _ ⟨r, hr, rfl⟩ g
  refine ⟨MulAut.conjNormal g r, ?_, ?_⟩
  · exact (Subgroup.characteristic_iff_le_comap.mp ‹P.Characteristic› (MulAut.conjNormal g)) hr
  · simp [MulAut.conjNormal_apply]

variable {p : ℕ} [hp : Fact p.Prime]

/-- **Lemma 4 of Wilson** (with `a + 1` in place of `a`). Let `K ⊴ H`, `Q ∈ Syl_p(K)` and
`t ∈ H` with `(tq)^(p^(a+1)) = 1` for all `q ∈ Q`; let `N` be the normal closure of the
elements `(tq)^(p^a)`. Then `K ∩ N` has normal subgroups `K₁ ≤ K₂` (normal in `H`) with `K₁`
`p`-soluble, `K₂/K₁` a direct product of `𝔖_p`-groups and `(K ∩ N)/K₂` soluble. -/
theorem lemma4 [Schreier] (hCFSG : TauCeti.ClassificationStatement.{0}) {H : Type} [Group H] [Finite H]
    {K : Subgroup H} [hK : K.Normal] (Q : Sylow p K) (t : H) (a : ℕ)
    (hexp : ∀ q ∈ Q, (t * (q : H)) ^ (p ^ (a + 1)) = 1) :
    ∃ K₁ K₂ : Subgroup H, K₁.Normal ∧ K₂.Normal ∧ K₁ ≤ K₂ ∧
      K₂ ≤ K ⊓ normalClosure {x : H | ∃ q ∈ Q, x = (t * (q : H)) ^ (p ^ a)} ∧
      IsPSolvable p K₁ ∧ SpFactor p K₁ K₂ ∧
      SolFactor K₂ (K ⊓ normalClosure {x : H | ∃ q ∈ Q, x = (t * (q : H)) ^ (p ^ a)}) := by
  classical
  set Aset : Set H := {x : H | ∃ q ∈ Q, x = (t * (q : H)) ^ (p ^ a)}
  set N := normalClosure Aset
  set X := K ⊓ N
  have hXn : X.Normal := Subgroup.normal_inf_normal K N
  obtain ⟨R, hRn, hRp, hRmax⟩ := exists_pSolRad p X
  have hRc : R.Characteristic := pSolRad_characteristic hRp hRmax
  set Y := ↥X ⧸ R
  have hF : fittingSubgroup Y = ⊥ := fitting_quot_eq_bot hRp hRmax
  have hZ : ∀ C : ComponentIndex Y, center C.1 = ⊥ := fun C =>
    component_center_eq_bot hF C.2
  -- the action of `H` on `Y`
  let σ : H →* MulAut Y := (quotAut R).comp (MulAut.conjNormal (H := X))
  have hσ : ∀ (g : H) (x : X), σ g (QuotientGroup.mk' R x) =
      QuotientGroup.mk' R (MulAut.conjNormal (H := X) g x) := fun g x =>
    quotAut_apply R _ x
  -- Lemma 4(i): `σ((tq)^(p^a))` normalises every component
  have hkey : ∀ q0 ∈ Q, ∀ C : ComponentIndex Y,
      C.1.map (σ ((t * (q0 : H)) ^ (p ^ a))).toMonoidHom = C.1 := by
    intro q0 hq0 C
    set u := t * (q0 : H)
    have hσu : σ u ^ (p ^ (a + 1)) = 1 := by rw [← map_pow, hexp q0 hq0, map_one]
    -- a nontrivial `p`-element of `Q ∩ X` with image in `C`
    have hQK : ABGLocalTools.IsSylowOf p ((Q : Subgroup K).map K.subtype) K := ⟨Q, rfl⟩
    have hKX : K ≤ normalizer (X : Set H) := fun k _ =>
      (Subgroup.normalizer_eq_top_iff.mpr hXn) ▸ mem_top k
    obtain ⟨P', hP'⟩ := hQK.inf_of_le_normalizer (inf_le_left : X ≤ K) hKX
    set SY : Sylow p Y := P'.mapSurjective (QuotientGroup.mk'_surjective R)
    have hne := sylow_inf_ne_bot_of_isSubnormal SY C.2.2
      (dvd_card_component hRp hRmax C.2)
    obtain ⟨⟨y, hyS, hyC⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
    have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
    obtain ⟨x, hxP, rfl⟩ := mem_map.mp (show y ∈ (P' : Subgroup X).map (QuotientGroup.mk' R)
      from hyS)
    have hxQ : (x : H) ∈ (Q : Subgroup K).map K.subtype ⊓ X := by
      rw [← hP']; exact ⟨x, hxP, rfl⟩
    obtain ⟨q1, hq1, hq1x⟩ := mem_map.mp hxQ.1
    set h : H := (x : H)
    -- the products `v m = (uh)^m u^{-m}`
    let v : ℕ → H := fun m => (u * h) ^ m * (u ^ m)⁻¹
    have hvs : ∀ m, v (m + 1) = v m * (u ^ (m + 1) * h * (u ^ (m + 1))⁻¹) := by
      intro m
      simp only [v, pow_succ]
      group
    have hconjX : ∀ g : H, g * h * g⁻¹ ∈ X := fun g => hXn.conj_mem h x.2 g
    have hvX : ∀ m, v m ∈ X := by
      intro m
      induction m with
      | zero => simp [v]
      | succ m ih => rw [hvs]; exact X.mul_mem ih (hconjX _)
    let w : ℕ → Y := fun m => QuotientGroup.mk' R ⟨v m, hvX m⟩
    have hw0 : w 0 = 1 := by
      show QuotientGroup.mk' R ⟨v 0, hvX 0⟩ = 1
      have : (⟨v 0, hvX 0⟩ : X) = 1 := Subtype.ext (by simp [v])
      rw [this, map_one]
    have hws : ∀ m, w (m + 1) = w m * (σ u ^ (m + 1)) (QuotientGroup.mk' R x) := by
      intro m
      rw [← map_pow, hσ]
      show QuotientGroup.mk' R ⟨v (m + 1), hvX (m + 1)⟩ = _
      rw [← map_mul]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, MulAut.conjNormal_apply]
      exact hvs m
    have hwn : w (p ^ (a + 1)) = 1 := by
      show QuotientGroup.mk' R ⟨v (p ^ (a + 1)), hvX _⟩ = 1
      have h1 : (u * h) ^ (p ^ (a + 1)) = 1 := by
        have := hexp (q0 * q1) (Q.mul_mem hq0 hq1)
        rw [Subgroup.coe_mul, ← mul_assoc, show (q1 : H) = (x : H) from hq1x] at this
        exact this
      have h2 : u ^ (p ^ (a + 1)) = 1 := hexp q0 hq0
      have : (⟨v (p ^ (a + 1)), hvX _⟩ : X) = 1 := Subtype.ext (by simp [v, h1, h2])
      rw [this, map_one]
    have := map_pow_eq_of_prod hZ hp.out (σ u) hσu C hyC hy1' w hw0 hws hwn
    rwa [map_pow]
  -- the stabiliser of all components is a normal subgroup of `H` containing `N`
  let G0 : Subgroup H :=
    { carrier := {g | ∀ C : ComponentIndex Y, C.1.map (σ g).toMonoidHom = C.1}
      mul_mem' := by
        intro g g' hg hg' C
        have : (σ (g * g')).toMonoidHom = (σ g).toMonoidHom.comp (σ g').toMonoidHom := by
          rw [map_mul]; rfl
        rw [this, ← Subgroup.map_map, hg' C, hg C]
      one_mem' := by
        intro C
        rw [map_one]; ext; simp
      inv_mem' := by
        intro g hg C
        have : (σ g⁻¹).toMonoidHom.comp (σ g).toMonoidHom = MonoidHom.id Y :=
          MonoidHom.ext fun y => by
            show σ g⁻¹ (σ g y) = y
            rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
        calc C.1.map (σ g⁻¹).toMonoidHom
            = (C.1.map (σ g).toMonoidHom).map (σ g⁻¹).toMonoidHom := by rw [hg C]
          _ = C.1 := by rw [Subgroup.map_map, this, Subgroup.map_id] }
  have hG0n : G0.Normal := by
    refine ⟨fun g hg k C => ?_⟩
    set C' : ComponentIndex Y := ⟨C.1.map (σ k⁻¹).toMonoidHom,
      isComponent_map_mulEquiv (σ k⁻¹) C.2⟩
    have h1 := hg C'
    have : (σ (k * g * k⁻¹)).toMonoidHom = (σ k).toMonoidHom.comp
        ((σ g).toMonoidHom.comp (σ k⁻¹).toMonoidHom) := by
      rw [map_mul, map_mul]; rfl
    rw [this, ← Subgroup.map_map, ← Subgroup.map_map]
    change (C'.1.map (σ g).toMonoidHom).map (σ k).toMonoidHom = C.1
    rw [h1, Subgroup.map_map]
    have : (σ k).toMonoidHom.comp (σ k⁻¹).toMonoidHom = MonoidHom.id Y :=
      MonoidHom.ext fun y => by
        show σ k (σ k⁻¹ y) = y
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
    rw [this, Subgroup.map_id]
  have hNG0 : N ≤ G0 := by
    refine normalClosure_le_normal ?_
    rintro _ ⟨q, hq, rfl⟩ C
    exact hkey q hq C
  -- hence `Y` normalises each of its components
  have hker : kernelOf (components Y) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    rw [mem_kernelOf]
    intro C hC
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective R y
    apply mem_normalizer_of_map_conj_eq
    have hσx : σ (x : H) = MulAut.conj (QuotientGroup.mk' R x) := by
      ext z
      obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective R z
      rw [hσ, MulAut.conj_apply, ← map_mul, ← map_inv, ← map_mul]
      congr 1
    rw [← hσx]
    exact hNG0 x.2.2 ⟨C, hC⟩
  -- Schreier: `Y/E(Y)` is soluble
  obtain ⟨k, hk⟩ := dA_kernel_le_layer hF hCFSG
  rw [hker, dA_top] at hk
  have hLn : (layer Y).Normal := inferInstance
  have hYsol : Group.IsSolvable (Y ⧸ layer Y) := by
    rw [isSolvable_def]
    refine ⟨k, ?_⟩
    rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective (layer Y)) k, eq_bot_iff]
    rintro _ ⟨z, hz, rfl⟩
    exact (QuotientGroup.eq_one_iff z).mpr (hk hz)
  -- the subgroups `K₁ = R` and `K₂ = preimage of E(Y)`
  set E' : Subgroup X := (layer Y).comap (QuotientGroup.mk' R)
  have hE'c : E'.Characteristic := by
    rw [Subgroup.characteristic_iff_map_le]
    intro φ
    rintro _ ⟨z, hz, rfl⟩
    show QuotientGroup.mk' R (φ z) ∈ layer Y
    rw [← quotEquiv_apply R φ z]
    have hlc : (layer Y).Characteristic := layer_characteristic
    exact (Subgroup.characteristic_iff_le_comap.mp hlc (quotEquiv R φ)) hz
  have hRE' : R ≤ E' := fun r hr => by
    show QuotientGroup.mk' R r ∈ layer Y
    rw [show QuotientGroup.mk' R r = 1 from (QuotientGroup.eq_one_iff r).mpr hr]
    exact one_mem _
  set K₁ := R.map X.subtype
  set K₂ := E'.map X.subtype
  have hK₁n : K₁.Normal := normal_map_of_char X R
  have hK₂n : K₂.Normal := normal_map_of_char X E'
  have hK₂X : K₂ ≤ X := map_subtype_le E'
  have hmemK₂ : ∀ z : X, (z : H) ∈ K₂ ↔ z ∈ E' := fun z =>
    ⟨fun ⟨e, he, hez⟩ => (Subtype.ext hez : e = z) ▸ he, fun hz => ⟨z, hz, rfl⟩⟩
  have hmemK₁ : ∀ z : X, (z : H) ∈ K₁ ↔ z ∈ R := fun z =>
    ⟨fun ⟨e, he, hez⟩ => (Subtype.ext hez : e = z) ▸ he, fun hz => ⟨z, hz, rfl⟩⟩
  refine ⟨K₁, K₂, hK₁n, hK₂n, map_mono hRE', hK₂X,
    isPSolvable_of_mulEquiv (R.equivMapOfInjective X.subtype X.subtype_injective) hRp, ?_, ?_⟩
  · -- `K₂/K₁ ≅ E(Y)`
    let f : K₂ →* layer Y := ((QuotientGroup.mk' R).comp (Subgroup.inclusion hK₂X)).codRestrict
      (layer Y) (fun k => (hmemK₂ (Subgroup.inclusion hK₂X k)).mp k.2)
    have hf : Function.Surjective f := by
      rintro ⟨l, hl⟩
      obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective R l
      exact ⟨⟨z, (hmemK₂ z).mpr hl⟩, rfl⟩
    have hfk : f.ker = K₁.subgroupOf K₂ := by
      ext k
      simp only [f, MonoidHom.mem_ker, mem_subgroupOf]
      rw [Subtype.ext_iff]
      show QuotientGroup.mk' R (Subgroup.inclusion hK₂X k) = 1 ↔ _
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

      exact (hmemK₁ (Subgroup.inclusion hK₂X k)).symm

    obtain ⟨e⟩ := quot_equiv_of_surj f hf hfk
    refine ⟨inferInstance, IsSpProd.of_equiv e ?_⟩
    have : Finite (Subgroup Y) :=
      Finite.of_injective (fun K : Subgroup Y => (K : Set Y)) SetLike.coe_injective
    refine ⟨ComponentIndex Y, fun C => C.1, fun C => inferInstance, inferInstance,
      fun C => component_isSimple hF C.2,
      nonab_component hF, fun C => dvd_card_component hRp hRmax C.2,
      ⟨(layerEquiv hZ).symm⟩⟩
  · -- `(K ∩ N)/K₂ ≅ Y/E(Y)`
    let f : X →* Y ⧸ layer Y := (QuotientGroup.mk' (layer Y)).comp (QuotientGroup.mk' R)
    have hf : Function.Surjective f :=
      (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective R)
    have hfk : f.ker = K₂.subgroupOf X := by
      ext z
      simp only [f, MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, mem_subgroupOf]
      exact (hmemK₂ z).symm
    obtain ⟨e⟩ := quot_equiv_of_surj f hf hfk
    exact ⟨inferInstance, Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective⟩

end CFSGOutside.Wilson
