import Mathlib

/-!
# Andersen–Oliver–Ventura: fusion systems

The objects in the statement of Theorem 3.8 of K. K. S. Andersen, B. Oliver and J. Ventura,
*Reduced, tame and exotic fusion systems*, Proc. London Math. Soc. (3) 105 (2012), 87–152,
DOI 10.1112/plms/pdr065 (arXiv:1009.0622, whose §1.1, Definitions 1.1, 1.2, 1.18, 1.21 and 2.1
and the first paragraph of §3 we follow).

A fusion system over `S` is a category whose objects are the subgroups of `S`; we record it by its
morphism sets `hom P Q ⊆ (P →* Q)`. Statements about a morphism of a fusion system over a subgroup
`S₀ ≤ S` and a morphism of a fusion system over `S` are made elementwise in `S`, so that no
subgroup has to be transported along an equality.
-/

namespace AndersenOliverVentura

open Subgroup

universe u v

/-- A fusion system over a group `S` (AOV §1.1): a category whose objects are the subgroups of `S`
such that `Hom_S(P,Q) ⊆ Hom_F(P,Q) ⊆ Inj(P,Q)` for all `P, Q ≤ S`, and in which each morphism is
the composite of an isomorphism of `F` followed by an inclusion. Identities are the conjugations
by `1`; composition is composition of homomorphisms. -/
structure FusionSystem (S : Type u) [Group S] where
  /-- The morphism set `Hom_F(P,Q)`. -/
  hom : (P Q : Subgroup S) → Set (P →* Q)
  /-- `Hom_S(P,Q) ⊆ Hom_F(P,Q)`: every conjugation `c_s` with `sPs⁻¹ ≤ Q` is a morphism. -/
  conj_mem : ∀ {P Q : Subgroup S} (φ : P →* Q) (s : S),
    (∀ x : P, (φ x : S) = s * x * s⁻¹) → φ ∈ hom P Q
  /-- `Hom_F(P,Q) ⊆ Inj(P,Q)`. -/
  injective : ∀ {P Q : Subgroup S} {φ : P →* Q}, φ ∈ hom P Q → Function.Injective φ
  /-- Morphisms compose. -/
  comp_mem : ∀ {P Q R : Subgroup S} {ψ : Q →* R} {φ : P →* Q},
    ψ ∈ hom Q R → φ ∈ hom P Q → ψ.comp φ ∈ hom P R
  /-- Each morphism `φ : P → Q` is an isomorphism `ψ : P → R` of `F` (with inverse `χ` in `F`)
  followed by the inclusion of `R ≤ Q`. -/
  factor : ∀ {P Q : Subgroup S} {φ : P →* Q}, φ ∈ hom P Q →
    ∃ R : Subgroup S, R ≤ Q ∧ ∃ ψ ∈ hom P R, ∃ χ ∈ hom R P,
      χ.comp ψ = MonoidHom.id P ∧ ψ.comp χ = MonoidHom.id R ∧ ∀ x : P, (φ x : S) = ψ x

variable {S : Type u} [Group S]

/-- The image `φ(P) ≤ S` of a homomorphism `φ : P → Q` between subgroups of `S`. -/
def img {P Q : Subgroup S} (φ : P →* Q) : Subgroup S := φ.range.map Q.subtype

namespace FusionSystem

variable (F : FusionSystem S)

/-- `P` and `P'` are `F`-conjugate: isomorphic as objects of the category `F`. -/
def Conj (P P' : Subgroup S) : Prop :=
  ∃ φ ∈ F.hom P P', ∃ ψ ∈ F.hom P' P, ψ.comp φ = MonoidHom.id P ∧ φ.comp ψ = MonoidHom.id P'

/-- Elements `x, y ∈ S` are `F`-conjugate: some morphism of `F` sends `x` to `y`. -/
def ElemConj (x y : S) : Prop :=
  ∃ (Q R : Subgroup S) (φ : Q →* R) (hx : x ∈ Q), φ ∈ F.hom Q R ∧ (φ ⟨x, hx⟩ : S) = y

/-- `P ≤ S` is fully centralized in `F` (AOV Definition 1.1). -/
def FullyCentralized (P : Subgroup S) : Prop :=
  ∀ P' : Subgroup S, F.Conj P P' →
    Nat.card (centralizer (P' : Set S)) ≤ Nat.card (centralizer (P : Set S))

/-- `P ≤ S` is fully normalized in `F` (AOV Definition 1.1). -/
def FullyNormalized (P : Subgroup S) : Prop :=
  ∀ P' : Subgroup S, F.Conj P P' →
    Nat.card (normalizer (P' : Set S)) ≤ Nat.card (normalizer (P : Set S))

lemma comp_pow_mem {P : Subgroup S} {α : MulAut P} (hα : α.toMonoidHom ∈ F.hom P P) (n : ℕ) :
    (α ^ n).toMonoidHom ∈ F.hom P P := by
  induction n with
  | zero => exact F.conj_mem _ 1 fun x => by simp
  | succ n ih =>
    have h := F.comp_mem ih hα
    have he : (α ^ (n + 1)).toMonoidHom = (α ^ n).toMonoidHom.comp α.toMonoidHom := by
      ext x; simp [pow_succ, MulAut.mul_apply]
    rw [he]; exact h

/-- `Aut_F(P)`, the automorphisms of `P` in `F`, as a subgroup of `Aut(P)`. -/
def autF [Finite S] (P : Subgroup S) : Subgroup (MulAut P) where
  carrier := {α | α.toMonoidHom ∈ F.hom P P}
  one_mem' := F.conj_mem _ 1 fun x => by simp
  mul_mem' := by
    intro a b ha hb
    have h := F.comp_mem ha hb
    have he : (a * b).toMonoidHom = a.toMonoidHom.comp b.toMonoidHom := by
      ext x; simp [MulAut.mul_apply]
    show (a * b).toMonoidHom ∈ F.hom P P
    rw [he]; exact h
  inv_mem' := by
    intro a ha
    have hfin : 0 < orderOf a := orderOf_pos a
    have hinv : a⁻¹ = a ^ (orderOf a - 1) := by
      apply inv_eq_of_mul_eq_one_right
      rw [← pow_succ', Nat.sub_add_cancel hfin, pow_orderOf_eq_one]
    show a⁻¹.toMonoidHom ∈ F.hom P P
    rw [hinv]; exact F.comp_pow_mem ha _

end FusionSystem

/-- `Aut_S(P) = {c_s | s ∈ N_S(P)}` as a subgroup of `Aut(P)`. -/
def autS (P : Subgroup S) : Subgroup (MulAut P) where
  carrier := {α | ∃ s ∈ normalizer (P : Set S), ∀ x : P, (α x : S) = s * x * s⁻¹}
  one_mem' := ⟨1, one_mem _, fun x => by simp⟩
  mul_mem' := by
    rintro a b ⟨s, hs, ha⟩ ⟨t, ht, hb⟩
    refine ⟨s * t, mul_mem hs ht, fun x => ?_⟩
    simp only [MulAut.mul_apply, ha, hb]; group
  inv_mem' := by
    rintro a ⟨s, hs, ha⟩
    refine ⟨s⁻¹, inv_mem hs, fun x => ?_⟩
    have h := ha (a⁻¹ x)
    simp only [MulAut.apply_inv_self] at h
    rw [h]; group

namespace FusionSystem

variable (p : ℕ) (F : FusionSystem S)

/-- `F` is saturated (Puig; AOV Definition 1.1, in the form of [BLO2, Definition 1.2]).

(I) Each fully normalized `P` is fully centralized and `Aut_S(P)` is a Sylow `p`-subgroup of
`Aut_F(P)`. (II) If `φ ∈ Hom_F(P,S)` and `φ(P)` is fully centralized, then `φ` extends to a
morphism of `F` defined on `N_φ = {g ∈ N_S(P) | φ c_g φ⁻¹ ∈ Aut_S(φ(P))}`; the subgroup `N` below
is `N_φ`, described by its elements. -/
def Saturated [Finite S] : Prop :=
  (∀ P : Subgroup S, F.FullyNormalized P →
    F.FullyCentralized P ∧ autS P ≤ F.autF P ∧ IsPGroup p (autS P) ∧
      ¬ p ∣ (autS P).relIndex (F.autF P)) ∧
  (∀ (P : Subgroup S) (φ : P →* (⊤ : Subgroup S)), φ ∈ F.hom P ⊤ → F.FullyCentralized (img φ) →
    ∀ N : Subgroup S, (N : Set S) = {g | g ∈ normalizer (P : Set S) ∧
        ∃ s ∈ normalizer (img φ : Set S), ∀ (x : P) (hx : g * x * g⁻¹ ∈ P),
          (φ ⟨g * x * g⁻¹, hx⟩ : S) = s * φ x * s⁻¹} →
      ∃ φbar ∈ F.hom N ⊤, ∀ (x : P) (hx : (x : S) ∈ N), (φbar ⟨x, hx⟩ : S) = φ x)

/-- `D` is normal in `F` (AOV Definition 1.2): `D ⊴ S`, and every `φ ∈ Hom_F(Q,R)` extends to some
`φbar ∈ Hom_F(DQ, DR)` with `φbar(D) = D`. -/
def IsNormalSubgroup (D : Subgroup S) : Prop :=
  D.Normal ∧ ∀ (Q R : Subgroup S) (φ : Q →* R), φ ∈ F.hom Q R →
    ∃ φbar ∈ F.hom (D ⊔ Q) (D ⊔ R), (∀ x : Q, (φbar ⟨x, mem_sup_right x.2⟩ : S) = φ x) ∧
      (fun x : (D ⊔ Q : Subgroup S) => (φbar x : S)) '' {x | (x : S) ∈ D} = D

/-- `D` is strongly closed in `F` (AOV Definition 1.2): no element of `D` is `F`-conjugate to an
element of `S ∖ D`. -/
def StronglyClosed (D : Subgroup S) : Prop :=
  ∀ x ∈ D, ∀ y : S, F.ElemConj x y → y ∈ D

/-- `F₀`, a fusion system over `S₀ ≤ S`, is a subcategory of `F` (a fusion subsystem). -/
def IsSubsystem {S₀ : Subgroup S} (F₀ : FusionSystem S₀) : Prop :=
  ∀ (P Q : Subgroup S₀) (φ : P →* Q), φ ∈ F₀.hom P Q →
    ∃ ψ ∈ F.hom (P.map S₀.subtype) (Q.map S₀.subtype),
      ∀ x : P, (ψ ⟨(x : S₀), mem_map_of_mem _ x.2⟩ : S) = ((φ x : S₀) : S)

/-- The fusion subsystem `F₀` over `S₀` is all of `F`. -/
def IsWhole {S₀ : Subgroup S} (F₀ : FusionSystem S₀) : Prop :=
  S₀ = ⊤ ∧ ∀ (P Q : Subgroup S₀) (φ : P.map S₀.subtype →* Q.map S₀.subtype),
    φ ∈ F.hom (P.map S₀.subtype) (Q.map S₀.subtype) →
      ∃ φ₀ ∈ F₀.hom P Q, ∀ x : P, ((φ₀ x : S₀) : S) = φ ⟨(x : S₀), mem_map_of_mem _ x.2⟩

/-- `F₀` is a normal fusion subsystem of `F` (AOV Definition 1.18): a saturated fusion subsystem over
`S₀ ≤ S` such that (i) `S₀` is strongly closed in `F`; (ii) each `φ ∈ Hom_F(P,Q)` with
`P, Q ≤ S₀` is `φ₀ ∘ α|_P` for some `α ∈ Aut_F(S₀)` and `φ₀ ∈ Hom_{F₀}(α(P), Q)`; and
(iii) `β φ β⁻¹ ∈ Hom_{F₀}(β(P), β(Q))` for `φ ∈ Hom_{F₀}(P,Q)` and `β ∈ Aut_F(S₀)`. -/
def IsNormalSubsystem [Finite S] {S₀ : Subgroup S} (F₀ : FusionSystem S₀) : Prop :=
  F.IsSubsystem F₀ ∧ F₀.Saturated p ∧ F.StronglyClosed S₀ ∧
  (∀ (P Q : Subgroup S₀) (φ : P.map S₀.subtype →* Q.map S₀.subtype),
    φ ∈ F.hom (P.map S₀.subtype) (Q.map S₀.subtype) →
      ∃ α ∈ F.hom S₀ S₀, ∃ φ₀ ∈ F₀.hom (P.map α) Q, ∀ x : P,
        (φ ⟨(x : S₀), mem_map_of_mem _ x.2⟩ : S) = ((φ₀ ⟨α x, mem_map_of_mem _ x.2⟩ : S₀) : S)) ∧
  (∀ (P Q : Subgroup S₀) (φ : P →* Q), φ ∈ F₀.hom P Q → ∀ β ∈ F.hom S₀ S₀,
      ∃ ψ ∈ F₀.hom (P.map β) (Q.map β), ∀ x : P,
        ((ψ ⟨β x, mem_map_of_mem _ x.2⟩ : S₀) : S) = (β (φ x) : S))

/-- `O^p(Γ)`: the smallest normal subgroup of `p`-power index. -/
def oP (Γ : Type v) [Group Γ] : Subgroup Γ :=
  sInf {N | N.Normal ∧ ∃ k : ℕ, N.index = p ^ k}

/-- `O^{p'}(Γ)`: the smallest normal subgroup of index prime to `p`. -/
def oP' (Γ : Type v) [Group Γ] : Subgroup Γ :=
  sInf {N | N.Normal ∧ Nat.Coprime N.index p}

/-- The hyperfocal subgroup `hyp(F) = ⟨s⁻¹ α(s) | s ∈ P ≤ S, α ∈ O^p(Aut_F(P))⟩` (AOV §1.3, before Definition 1.21). -/
def hyp [Finite S] : Subgroup S :=
  closure {y | ∃ (P : Subgroup S) (α : F.autF P), α ∈ oP p (F.autF P) ∧
    ∃ s : P, y = (s : S)⁻¹ * ((α : MulAut P) s : S)}

/-- `F₀ ⊆ F` has `p`-power index (AOV Definition 1.21(a)): `hyp(F) ≤ S₀` and
`Aut_{F₀}(P) ≥ O^p(Aut_F(P))` for all `P ≤ S₀`. -/
def HasPPowerIndex [Finite S] {S₀ : Subgroup S} (F₀ : FusionSystem S₀) : Prop :=
  F.hyp p ≤ S₀ ∧ ∀ (P : Subgroup S₀) (α : F.autF (P.map S₀.subtype)),
    α ∈ oP p (F.autF (P.map S₀.subtype)) →
      ∃ α₀ ∈ F₀.hom P P, ∀ x : P,
        ((α₀ x : S₀) : S) = ((α : MulAut (P.map S₀.subtype)) ⟨(x : S₀), mem_map_of_mem _ x.2⟩ : S)

/-- `F₀ ⊆ F` has index prime to `p` (AOV Definition 1.21(b)): `S₀ = S` and
`Aut_{F₀}(P) ≥ O^{p'}(Aut_F(P))` for all `P ≤ S`. -/
def HasIndexPrimeTo [Finite S] {S₀ : Subgroup S} (F₀ : FusionSystem S₀) : Prop :=
  S₀ = ⊤ ∧ ∀ (P : Subgroup S₀) (α : F.autF (P.map S₀.subtype)),
    α ∈ oP' p (F.autF (P.map S₀.subtype)) →
      ∃ α₀ ∈ F₀.hom P P, ∀ x : P,
        ((α₀ x : S₀) : S) = ((α : MulAut (P.map S₀.subtype)) ⟨(x : S₀), mem_map_of_mem _ x.2⟩ : S)

/-- `F` is reduced (AOV Definition 2.1): `F` is saturated, has no nontrivial normal `p`-subgroups,
no proper normal subsystem of `p`-power index, and no proper normal subsystem of index prime
to `p`. (Every subgroup of `S` is a `p`-group when `S` is.) -/
def Reduced [Finite S] : Prop :=
  F.Saturated p ∧
  (∀ D : Subgroup S, F.IsNormalSubgroup D → D = ⊥) ∧
  (∀ (S₀ : Subgroup S) (F₀ : FusionSystem S₀), F.IsNormalSubsystem p F₀ →
    F.HasPPowerIndex p F₀ → F.IsWhole F₀) ∧
  (∀ (S₀ : Subgroup S) (F₀ : FusionSystem S₀), F.IsNormalSubsystem p F₀ →
    F.HasIndexPrimeTo p F₀ → F.IsWhole F₀)

end FusionSystem

/-- The conjugations `c_g : P → Q` with `g ∈ G` and `gPg⁻¹ ≤ Q`, for subgroups `P, Q ≤ T ≤ G`. -/
def conjHoms {G : Type v} [Group G] (T : Subgroup G) (P Q : Subgroup T) : Set (P →* Q) :=
  {φ | ∃ g : G, ∀ x : P, ((φ x : T) : G) = g * x * g⁻¹}

/-- An injective `φ : P → Q` is an isomorphism `P ≃ φ(P)` followed by the inclusion. -/
noncomputable def equivImg {P Q : Subgroup S} {φ : P →* Q} (hφ : Function.Injective φ) :
    P ≃* img φ :=
  (MonoidHom.ofInjective hφ).trans (equivMapOfInjective φ.range Q.subtype Q.subtype_injective)

@[simp] lemma coe_equivImg {P Q : Subgroup S} {φ : P →* Q} (hφ : Function.Injective φ) (x : P) :
    (equivImg hφ x : S) = φ x := by
  change (((MonoidHom.ofInjective hφ x : φ.range) : Q) : S) = φ x
  rw [MonoidHom.ofInjective_apply]

lemma img_le {P Q : Subgroup S} (φ : P →* Q) : img φ ≤ Q := by
  rintro _ ⟨y, -, rfl⟩; exact y.2

/-- The fusion system `F_T(G)` of a group `G` over a subgroup `T` (AOV §1.1): its morphisms
`P → Q` are the conjugations `c_g` with `g ∈ G` and `gPg⁻¹ ≤ Q`. -/
def ofGroup (G : Type v) [Group G] (T : Subgroup G) : FusionSystem T where
  hom := conjHoms T
  conj_mem := by
    intro P Q φ s h
    exact ⟨s, fun x => by rw [h x]; simp⟩
  injective := by
    rintro P Q φ ⟨g, hg⟩ x y hxy
    have h1 := hg x
    have h2 := hg y
    rw [hxy, h2] at h1
    exact Subtype.ext (Subtype.ext (by simpa using h1.symm))
  comp_mem := by
    rintro P Q R ψ φ ⟨g, hg⟩ ⟨h, hh⟩
    exact ⟨g * h, fun x => by simp only [MonoidHom.comp_apply, hg, hh]; group⟩
  factor := by
    rintro P Q φ ⟨g, hg⟩
    have hφ : Function.Injective φ := by
      intro x y hxy
      have h1 := hg x
      have h2 := hg y
      rw [hxy, h2] at h1
      exact Subtype.ext (Subtype.ext (by simpa using h1.symm))
    refine ⟨img φ, img_le φ, (equivImg hφ).toMonoidHom, ⟨g, fun x => ?_⟩,
      (equivImg hφ).symm.toMonoidHom, ⟨g⁻¹, fun y => ?_⟩, ?_, ?_, fun x => ?_⟩
    · simp [hg x]
    · have h := hg ((equivImg hφ).symm y)
      have hy : ((equivImg hφ ((equivImg hφ).symm y) : T) : G) = ((y : T) : G) := by simp
      rw [coe_equivImg] at hy
      rw [hy] at h
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, inv_inv]
      rw [h]; group
    · ext x; simp
    · ext x; simp
    · simp

/-- An isomorphism of fusion systems: a group isomorphism `e : S ≃* S'` such that
`φ ↦ e φ e⁻¹` is a bijection `Hom_F(P,Q) ≃ Hom_{F'}(eP, eQ)`. -/
structure FusionIso {S' : Type v} [Group S'] (F : FusionSystem S) (F' : FusionSystem S') where
  /-- The underlying isomorphism of groups. -/
  toMulEquiv : S ≃* S'
  /-- `φ ∈ Hom_F(P,Q)` iff `e φ e⁻¹ ∈ Hom_{F'}(eP, eQ)`. -/
  hom_iff : ∀ (P Q : Subgroup S) (φ : P →* Q), φ ∈ F.hom P Q ↔
    ∃ ψ ∈ F'.hom (P.map toMulEquiv.toMonoidHom) (Q.map toMulEquiv.toMonoidHom),
      ∀ x : P, (ψ ⟨toMulEquiv x, mem_map_of_mem _ x.2⟩ : S') = toMulEquiv (φ x)

/-- `F` is realizable (AOV §1): isomorphic to the fusion system `F_T(G)` of a finite group `G` over
a Sylow `p`-subgroup `T`. -/
def Realizable (p : ℕ) (F : FusionSystem S) : Prop :=
  ∃ (G : Type) (_ : Group G) (_ : Finite G) (T : Sylow p G),
    Nonempty (FusionIso F (ofGroup G (T : Subgroup G)))

/-- The product `F₁ × F₂` over `S₁ × S₂` (AOV §3): `Hom_{F₁×F₂}(P,Q)` consists of the restrictions
`(φ₁, φ₂)|_P` with `φᵢ ∈ Hom_{Fᵢ}(Pᵢ, Qᵢ)` and `(φ₁,φ₂)(P) ≤ Q`, where `Pᵢ, Qᵢ` are the projections.
`IsProduct F F₁ F₂` says `F = F₁ × F₂`. -/
def IsProduct {S₁ S₂ : Type*} [Group S₁] [Group S₂] (F : FusionSystem (S₁ × S₂))
    (F₁ : FusionSystem S₁) (F₂ : FusionSystem S₂) : Prop :=
  ∀ (P Q : Subgroup (S₁ × S₂)) (ψ : P →* Q), ψ ∈ F.hom P Q ↔
    ∃ φ₁ ∈ F₁.hom (P.map (MonoidHom.fst S₁ S₂)) (Q.map (MonoidHom.fst S₁ S₂)),
    ∃ φ₂ ∈ F₂.hom (P.map (MonoidHom.snd S₁ S₂)) (Q.map (MonoidHom.snd S₁ S₂)),
      ∀ x : P, (ψ x : S₁ × S₂) =
        ((φ₁ ⟨(x : S₁ × S₂).1, mem_map_of_mem _ x.2⟩ : S₁),
          (φ₂ ⟨(x : S₁ × S₂).2, mem_map_of_mem _ x.2⟩ : S₂))

end AndersenOliverVentura
