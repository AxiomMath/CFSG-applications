import CFSGOutside.AOVTame.Realize

/-!
# AOV tameness: isomorphisms of fusion systems and realizations

Inverses and composites of isomorphisms of fusion systems, and how realizations `E : S → G`
compose with them, with group isomorphisms of the target, and with restriction to subgroups.
-/

namespace AndersenOliverVentura.Tame

open Subgroup

section Iso
variable {S S' S'' : Type*} [Group S] [Group S'] [Group S'']

lemma val_congr_hom {P Q : Subgroup S} (ψ : P →* Q) {a b : P} (h : (a : S) = b) :
    (ψ a : S) = ψ b := by rw [Subtype.ext h]

/-- Pull a homomorphism `ψ : P' → Q'` back along `e`, when `e(P) ≤ P'` and `Q' ≤ e(Q)`. -/
def pullHom (e : S ≃* S') {P Q : Subgroup S} {P' Q' : Subgroup S'}
    (hP : P.map e.toMonoidHom ≤ P') (hQ : Q' ≤ Q.map e.toMonoidHom) (ψ : P' →* Q') : P →* Q :=
  MonoidHom.mk' (fun x => ⟨e.symm (ψ ⟨e x, hP (mem_map_of_mem _ x.2)⟩), by
      obtain ⟨y, hy, hy'⟩ := hQ (ψ ⟨e x, hP (mem_map_of_mem _ x.2)⟩).2
      have : e.symm (ψ ⟨e x, hP (mem_map_of_mem _ x.2)⟩ : S') = y := by
        rw [← hy']; simp
      rw [this]; exact hy⟩)
    (fun a b => by
      apply Subtype.ext
      change e.symm (ψ ⟨e ((a * b : P) : S), _⟩ : S') =
        e.symm (ψ ⟨e (a : S), _⟩ : S') * e.symm (ψ ⟨e (b : S), _⟩ : S')
      rw [← map_mul e.symm, ← MulMemClass.coe_mul, ← map_mul ψ]
      exact congrArg e.symm (val_congr_hom ψ (by simp)))

lemma map_symm_map_eq (e : S ≃* S') (P : Subgroup S') :
    (P.map e.symm.toMonoidHom).map e.toMonoidHom = P := by
  ext y; simp [mem_map_equiv]

lemma map_map_trans (e : S ≃* S') (e' : S' ≃* S'') (P : Subgroup S) :
    (P.map e.toMonoidHom).map e'.toMonoidHom = P.map (e.trans e').toMonoidHom := by
  rw [map_map]; rfl

variable {F : FusionSystem S} {F' : FusionSystem S'} {F'' : FusionSystem S''}

/-- The inverse of an isomorphism of fusion systems. -/
def _root_.AndersenOliverVentura.FusionIso.symm (f : FusionIso F F') : FusionIso F' F where
  toMulEquiv := f.toMulEquiv.symm
  hom_iff P' Q' ψ := by
    have hP := map_symm_map_eq f.toMulEquiv P'
    have hQ := map_symm_map_eq f.toMulEquiv Q'
    constructor
    · intro hψ
      refine ⟨pullHom f.toMulEquiv hP.le hQ.ge ψ, ?_, fun y => ?_⟩
      · refine (f.hom_iff _ _ _).2 ⟨(inclusion hQ.ge).comp (ψ.comp (inclusion hP.le)),
          F'.comp_mem (F'.inclusion_mem _) (F'.comp_mem hψ (F'.inclusion_mem _)), fun x => ?_⟩
        change (ψ ⟨f.toMulEquiv x, _⟩ : S') =
          f.toMulEquiv (f.toMulEquiv.symm (ψ ⟨f.toMulEquiv x, _⟩ : S'))
        rw [MulEquiv.apply_symm_apply]
      · change f.toMulEquiv.symm (ψ ⟨f.toMulEquiv (f.toMulEquiv.symm y), _⟩ : S') = _
        exact congrArg _ (val_congr_hom ψ (by simp))
    · rintro ⟨φ, hφ, hφψ⟩
      obtain ⟨ψ₁, hψ₁, h₁⟩ := (f.hom_iff _ _ φ).1 hφ
      refine F'.mem_of_eq_on hψ₁ hP.ge ψ (fun y => ?_)
      have h2 := h₁ ⟨f.toMulEquiv.symm y, mem_map_of_mem _ y.2⟩
      have h3 := hφψ y
      calc (ψ y : S') = f.toMulEquiv (f.toMulEquiv.symm (ψ y : S')) := by simp
        _ = f.toMulEquiv (φ ⟨f.toMulEquiv.symm y, mem_map_of_mem _ y.2⟩ : S) :=
            congrArg _ h3.symm
        _ = ψ₁ ⟨f.toMulEquiv (f.toMulEquiv.symm y), _⟩ := h2.symm
        _ = ψ₁ ⟨y, hP.ge y.2⟩ := val_congr_hom ψ₁ (by simp)

/-- The composite of isomorphisms of fusion systems. -/
def _root_.AndersenOliverVentura.FusionIso.trans (f : FusionIso F F') (f' : FusionIso F' F'') : FusionIso F F'' where
  toMulEquiv := f.toMulEquiv.trans f'.toMulEquiv
  hom_iff P Q φ := by
    have hP := map_map_trans f.toMulEquiv f'.toMulEquiv P
    have hQ := map_map_trans f.toMulEquiv f'.toMulEquiv Q
    rw [f.hom_iff]
    constructor
    · rintro ⟨ψ, hψ, h⟩
      obtain ⟨χ, hχ, h'⟩ := (f'.hom_iff _ _ ψ).1 hψ
      refine ⟨(inclusion hQ.le).comp (χ.comp (inclusion hP.ge)),
        F''.comp_mem (F''.inclusion_mem _) (F''.comp_mem hχ (F''.inclusion_mem _)), fun x => ?_⟩
      have h2 := h' ⟨f.toMulEquiv x, mem_map_of_mem _ x.2⟩
      change (χ ⟨f'.toMulEquiv (f.toMulEquiv x), _⟩ : S'') = f'.toMulEquiv (f.toMulEquiv (φ x))
      exact h2.trans (congrArg _ (h x))
    · rintro ⟨χ, hχ, h⟩
      refine ⟨pullHom f'.toMulEquiv hP.le hQ.ge χ,
        (f'.hom_iff _ _ _).2 ⟨(inclusion hQ.ge).comp (χ.comp (inclusion hP.le)),
          F''.comp_mem (F''.inclusion_mem _) (F''.comp_mem hχ (F''.inclusion_mem _)), fun y => ?_⟩,
        fun x => ?_⟩
      · change (χ ⟨f'.toMulEquiv y, _⟩ : S'') =
          f'.toMulEquiv (f'.toMulEquiv.symm (χ ⟨f'.toMulEquiv y, _⟩ : S''))
        rw [MulEquiv.apply_symm_apply]
      · change f'.toMulEquiv.symm (χ ⟨f'.toMulEquiv (f.toMulEquiv x), _⟩ : S'') = _
        have h2 := h x
        calc f'.toMulEquiv.symm (χ ⟨f'.toMulEquiv (f.toMulEquiv x), _⟩ : S'') =
            f'.toMulEquiv.symm ((f.toMulEquiv.trans f'.toMulEquiv) (φ x)) := congrArg _ h2
          _ = f.toMulEquiv (φ x) := by simp

end Iso

section Realize
variable {S S' : Type*} [Group S] [Group S'] {F : FusionSystem S} {F' : FusionSystem S'}
  {G G' : Type*} [Group G] [Group G']

/-- A realization of `F'` composed with an isomorphism `F ≅ F'` realizes `F`. -/
lemma realizedBy_comp (f : FusionIso F F') {E : S' →* G} (hE : Function.Injective E)
    (hR : RealizedBy F' E) : RealizedBy F (E.comp f.toMulEquiv.toMonoidHom) := by
  intro P Q φ
  rw [f.hom_iff]
  constructor
  · rintro ⟨ψ, hψ, h⟩
    obtain ⟨g, hg⟩ := (hR _ _ ψ).1 hψ
    refine ⟨g, fun x => ?_⟩
    have := hg ⟨f.toMulEquiv x, mem_map_of_mem _ x.2⟩
    rw [h x] at this
    exact this
  · rintro ⟨g, hg⟩
    obtain ⟨ψ, hψ, hψe⟩ := hR.exists_mem hE (P := P.map f.toMulEquiv.toMonoidHom)
      (Q := Q.map f.toMulEquiv.toMonoidHom) g (by
        rintro ⟨_, x, hx, rfl⟩
        exact ⟨_, mem_map_of_mem _ (φ ⟨x, hx⟩).2, (hg ⟨x, hx⟩)⟩)
    refine ⟨ψ, hψ, fun x => hE ?_⟩
    rw [hψe]; exact (hg x).symm

/-- A realization followed by a group isomorphism is a realization. -/
lemma realizedBy_mulEquiv {E : S →* G} (hR : RealizedBy F E) (e : G ≃* G') :
    RealizedBy F (e.toMonoidHom.comp E) := by
  intro P Q φ
  rw [hR]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨e g, fun x => by simp [hg x]⟩
  · rintro ⟨g, hg⟩
    exact ⟨e.symm g, fun x => e.injective (by simpa using hg x)⟩

/-- A realization of `F_T(G)` restricts to a realization of `F_X(G)` for `X ≤ T`. -/
lemma realizedBy_restrict {T X : Subgroup G} (hXT : X ≤ T) {E : T →* G'}
    (hE : Function.Injective E) (hR : RealizedBy (ofGroup G T) E) :
    RealizedBy (ofGroup G X) (E.comp (inclusion hXT)) := by
  intro P Q φ
  constructor
  · rintro ⟨g, hg⟩
    have h : ∀ y : P.map (inclusion hXT), g * ((y : T) : G) * g⁻¹ ∈
        (Q.map (inclusion hXT)).map T.subtype := by
      rintro ⟨_, x, hx, rfl⟩
      refine ⟨inclusion hXT (φ ⟨x, hx⟩), mem_map_of_mem _ (φ ⟨x, hx⟩).2, ?_⟩
      simp [hg ⟨x, hx⟩]
    obtain ⟨g', hg'⟩ := (hR _ _ (conjMap _ _ g h)).1 ⟨g, fun y => rfl⟩
    refine ⟨g', fun x => ?_⟩
    have := hg' ⟨inclusion hXT x, mem_map_of_mem _ x.2⟩
    change E (inclusion hXT (φ x)) = g' * E (inclusion hXT x) * g'⁻¹
    refine (congrArg E ?_).trans this
    apply Subtype.ext
    simp [hg x]
  · rintro ⟨g', hg'⟩
    obtain ⟨ψ, hψ, hψe⟩ := hR.exists_mem hE (P := P.map (inclusion hXT))
      (Q := Q.map (inclusion hXT)) g' (by
        rintro ⟨_, x, hx, rfl⟩
        exact ⟨inclusion hXT (φ ⟨x, hx⟩), mem_map_of_mem _ (φ ⟨x, hx⟩).2, hg' ⟨x, hx⟩⟩)
    obtain ⟨g, hg⟩ := hψ
    refine ⟨g, fun x => ?_⟩
    have e1 := hψe ⟨inclusion hXT x, mem_map_of_mem _ x.2⟩
    have e1' := hg' x
    simp only [MonoidHom.comp_apply] at e1'
    rw [← e1'] at e1
    have e2 := hE e1
    have e3 := hg ⟨inclusion hXT x, mem_map_of_mem _ x.2⟩
    rw [e2] at e3
    simpa using e3

end Realize

end AndersenOliverVentura.Tame
