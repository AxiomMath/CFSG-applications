import CFSGOutside.AOVTame.Perm
import CFSGOutside.AOVTame.TameFactor

/-!
# AOV tameness: a direct decomposition `T = X × Y` splits `F_T(G) = F_X(G) × F_Y(G)`

(AOV Proposition 3.2 for `p = 2`, via Goldschmidt's theorem instead of Alperin's.) Consequently the
"only if" construction applies: if `G` tamely realizes `F_T(G)`, then `F_X(G)` is tame.
-/

namespace AndersenOliverVentura.Tame

open Subgroup CategoryTheory CFSGOutside.Corpus

attribute [local instance] Nat.fact_prime_two

variable {G : Type} [Group G] [Finite G] {T : Sylow 2 G} {X Y : Subgroup G}

lemma realizedBy_subtype (K : Subgroup G) : RealizedBy (ofGroup G K) K.subtype :=
  fun _ _ _ => Iff.rfl

section
variable (h : Decomp T X Y)

/-- `X × Y → T`, `(x, y) ↦ x y`. -/
def Decomp.mulHom : X × Y →* (T : Subgroup G) :=
  ((inclusion h.leX).noncommCoprod (inclusion h.leY) (fun x y => by
    apply Subtype.ext
    exact h.comm x x.2 y y.2))

@[simp] lemma Decomp.mulHom_apply (z : X × Y) : (h.mulHom z : G) = (z.1 : G) * z.2 := rfl

lemma Decomp.mulHom_bijective : Function.Bijective h.mulHom := by
  refine ⟨fun z w e => ?_, fun t => ?_⟩
  · have e' : (z.1 : G) * z.2 = (w.1 : G) * w.2 := congrArg Subtype.val e
    obtain ⟨e1, e2⟩ := h.unique z.1.2 w.1.2 z.2.2 w.2.2 e'
    exact Prod.ext (Subtype.ext e1) (Subtype.ext e2)
  · obtain ⟨x, hx, y, hy, e⟩ := h.sup t t.2
    exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), Subtype.ext e.symm⟩

/-- `X × Y ≃ T`. -/
noncomputable def Decomp.mulEquiv : X × Y ≃* (T : Subgroup G) :=
  MulEquiv.ofBijective h.mulHom h.mulHom_bijective

/-- The internal product data of the decomposition. -/
noncomputable def Decomp.prodData : ProdData (T : Subgroup G) X Y where
  π₁ := (MonoidHom.fst X Y).comp h.mulEquiv.symm.toMonoidHom
  π₂ := (MonoidHom.snd X Y).comp h.mulEquiv.symm.toMonoidHom
  ι₁ := inclusion h.leX
  ι₂ := inclusion h.leY
  π₁ι₁ a := by
    have : h.mulEquiv.symm (inclusion h.leX a) = (a, 1) := by
      rw [MulEquiv.symm_apply_eq]; apply Subtype.ext; simp [Decomp.mulEquiv]
    simp [this]
  π₂ι₁ a := by
    have : h.mulEquiv.symm (inclusion h.leX a) = (a, 1) := by
      rw [MulEquiv.symm_apply_eq]; apply Subtype.ext; simp [Decomp.mulEquiv]
    simp [this]
  π₁ι₂ b := by
    have : h.mulEquiv.symm (inclusion h.leY b) = (1, b) := by
      rw [MulEquiv.symm_apply_eq]; apply Subtype.ext; simp [Decomp.mulEquiv]
    simp [this]
  π₂ι₂ b := by
    have : h.mulEquiv.symm (inclusion h.leY b) = (1, b) := by
      rw [MulEquiv.symm_apply_eq]; apply Subtype.ext; simp [Decomp.mulEquiv]
    simp [this]
  decomp t := by
    apply Subtype.ext
    have := congrArg Subtype.val (h.mulEquiv.apply_symm_apply t)
    simp only [Decomp.mulEquiv, MulEquiv.ofBijective_apply, Decomp.mulHom_apply] at this
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, coe_mul, coe_inclusion]
    exact this.symm

lemma Decomp.prodData_decomp (t : (T : Subgroup G)) :
    (t : G) = ((h.prodData.π₁ t : X) : G) * ((h.prodData.π₂ t : Y) : G) := by
  have := congrArg Subtype.val (h.prodData.decomp t)
  simpa [Decomp.prodData] using this

end

lemma map_conj_le {K L : Subgroup G} {c : G} :
    K.map (MulAut.conj c).toMonoidHom ≤ L ↔ ∀ x ∈ K, c * x * c⁻¹ ∈ L := by
  constructor
  · intro h x hx; exact h ⟨x, hx, rfl⟩
  · rintro h _ ⟨x, hx, rfl⟩; exact h x hx

section Prod
variable [GoldschmidtTheoremA] (hG : Good T) (h : Decomp T X Y)
include hG h

/-- Conjugation by `a b ∈ N_X N_Y` on an element of `X`. -/
lemma Decomp.conj_X {a b y : G} (ha : a ∈ normalClosure (X : Set G))
    (hb : b ∈ normalClosure (Y : Set G)) (hy : y ∈ X) :
    (a * b)⁻¹ * y * (a * b) = a⁻¹ * y * a := by
  have := h.conj_components hG ha hb hy (one_mem Y)
  simpa using this

lemma Decomp.conj_Y {a b y : G} (ha : a ∈ normalClosure (X : Set G))
    (hb : b ∈ normalClosure (Y : Set G)) (hy : y ∈ Y) :
    (a * b)⁻¹ * y * (a * b) = b⁻¹ * y * b := by
  have := h.conj_components hG ha hb (one_mem X) hy
  simpa using this

/-- `F_T(G) = F_X(G) × F_Y(G)` along the decomposition. -/
theorem Decomp.isProdVia : IsProdVia (ofGroup G T) (ofGroup G X) (ofGroup G Y) h.prodData := by
  intro P Q ψ
  constructor
  · rintro ⟨g, hg⟩
    set P' := P.map (T : Subgroup G).subtype
    have hP' : P' ≤ T := by rintro _ ⟨x, -, rfl⟩; exact x.2
    have hPg : P'.map (MulAut.conj (g⁻¹)⁻¹).toMonoidHom ≤ T := by
      rw [map_conj_le]
      rintro _ ⟨x, hx, rfl⟩
      have := (ψ ⟨x, hx⟩ : (T : Subgroup G)).2
      rw [hg ⟨x, hx⟩] at this
      simpa only [inv_inv, coe_subtype] using this
    obtain ⟨a, ha, b, hb, hab⟩ := h.realize hG hP' hPg
    have key : ∀ x : P, ((h.prodData.π₁ (ψ x) : X) : G) =
        a⁻¹ * ((h.prodData.π₁ x : X) : G) * a ∧
        ((h.prodData.π₂ (ψ x) : Y) : G) = b⁻¹ * ((h.prodData.π₂ x : Y) : G) * b := by
      intro x
      have e1 := hab (x : T) ⟨x, x.2, rfl⟩
      rw [inv_inv] at e1
      have hdx := h.prodData_decomp (x : T)
      have hT : (a * b)⁻¹ * (((h.prodData.π₁ x : X) : G) * ((h.prodData.π₂ x : Y) : G)) *
          (a * b) ∈ (T : Subgroup G) := by
        rw [← hdx, e1, ← hg x]; exact (ψ x : T).2
      obtain ⟨m1, m2⟩ := h.conj_mem_X hG ha hb (h.prodData.π₁ x).2 (h.prodData.π₂ x).2 hT
      have e' : (((ψ x : T) : G)) = (a⁻¹ * ((h.prodData.π₁ x : X) : G) * a) *
          (b⁻¹ * ((h.prodData.π₂ x : Y) : G) * b) := by
        rw [hg x, ← e1, hdx, h.conj_components hG ha hb (h.prodData.π₁ x).2 (h.prodData.π₂ x).2]
      have hd := h.prodData_decomp (ψ x)
      exact h.unique (h.prodData.π₁ (ψ x)).2 m1 (h.prodData.π₂ (ψ x)).2 m2 (hd.symm.trans e')
    obtain ⟨φ₁, hφ₁, hφ₁e⟩ := (realizedBy_subtype X).exists_mem Subtype.val_injective
      (P := P.map h.prodData.π₁) (Q := Q.map h.prodData.π₁) a⁻¹ (by
        rintro ⟨_, x, hx, rfl⟩
        refine ⟨h.prodData.π₁ (ψ ⟨x, hx⟩), mem_map_of_mem _ (ψ ⟨x, hx⟩).2, ?_⟩
        simp only [coe_subtype, inv_inv]
        exact (key ⟨x, hx⟩).1)
    obtain ⟨φ₂, hφ₂, hφ₂e⟩ := (realizedBy_subtype Y).exists_mem Subtype.val_injective
      (P := P.map h.prodData.π₂) (Q := Q.map h.prodData.π₂) b⁻¹ (by
        rintro ⟨_, x, hx, rfl⟩
        refine ⟨h.prodData.π₂ (ψ ⟨x, hx⟩), mem_map_of_mem _ (ψ ⟨x, hx⟩).2, ?_⟩
        simp only [coe_subtype, inv_inv]
        exact (key ⟨x, hx⟩).2)
    refine ⟨φ₁, hφ₁, φ₂, hφ₂, fun x => ⟨Subtype.ext ?_, Subtype.ext ?_⟩⟩
    · have := hφ₁e ⟨h.prodData.π₁ x, mem_map_of_mem _ x.2⟩
      simp only [coe_subtype, inv_inv] at this
      rw [this]; exact (key x).1
    · have := hφ₂e ⟨h.prodData.π₂ x, mem_map_of_mem _ x.2⟩
      simp only [coe_subtype, inv_inv] at this
      rw [this]; exact (key x).2
  · rintro ⟨φ₁, ⟨g₁, hg₁⟩, φ₂, ⟨g₂, hg₂⟩, hx⟩
    set R₁ : Subgroup G := (P.map h.prodData.π₁).map X.subtype
    set R₂ : Subgroup G := (P.map h.prodData.π₂).map Y.subtype
    have hR₁ : R₁ ≤ T := by rintro _ ⟨y, -, rfl⟩; exact h.leX y.2
    have hR₂ : R₂ ≤ T := by rintro _ ⟨y, -, rfl⟩; exact h.leY y.2
    have hR₁g : R₁.map (MulAut.conj (g₁⁻¹)⁻¹).toMonoidHom ≤ T := by
      rw [map_conj_le]
      rintro _ ⟨y, hy, rfl⟩
      have := (φ₁ ⟨y, hy⟩ : X).2
      rw [hg₁ ⟨y, hy⟩] at this
      simpa only [inv_inv, coe_subtype] using h.leX this
    have hR₂g : R₂.map (MulAut.conj (g₂⁻¹)⁻¹).toMonoidHom ≤ T := by
      rw [map_conj_le]
      rintro _ ⟨y, hy, rfl⟩
      have := (φ₂ ⟨y, hy⟩ : Y).2
      rw [hg₂ ⟨y, hy⟩] at this
      simpa only [inv_inv, coe_subtype] using h.leY this
    obtain ⟨a₁, ha₁, b₁, hb₁, h₁⟩ := h.realize hG hR₁ hR₁g
    obtain ⟨a₂, ha₂, b₂, hb₂, h₂⟩ := h.realize hG hR₂ hR₂g
    refine ⟨(a₁ * b₂)⁻¹, fun x => ?_⟩
    have hdx := h.prodData_decomp (x : T)
    have hdψ := h.prodData_decomp (ψ x)
    have e1 : ((h.prodData.π₁ (ψ x) : X) : G) = g₁ * ((h.prodData.π₁ x : X) : G) * g₁⁻¹ := by
      rw [(hx x).1]; exact hg₁ ⟨_, mem_map_of_mem _ x.2⟩
    have e2 : ((h.prodData.π₂ (ψ x) : Y) : G) = g₂ * ((h.prodData.π₂ x : Y) : G) * g₂⁻¹ := by
      rw [(hx x).2]; exact hg₂ ⟨_, mem_map_of_mem _ x.2⟩
    have f1 := h₁ _ ⟨_, mem_map_of_mem _ x.2, rfl⟩
    have f2 := h₂ _ ⟨_, mem_map_of_mem _ x.2, rfl⟩
    simp only [coe_subtype, inv_inv] at f1 f2
    rw [h.conj_X hG ha₁ hb₁ (h.prodData.π₁ x).2] at f1
    rw [h.conj_Y hG ha₂ hb₂ (h.prodData.π₂ x).2] at f2
    rw [hdψ, e1, e2, ← f1, ← f2, inv_inv, hdx,
      h.conj_components hG ha₁ hb₂ (h.prodData.π₁ x).2 (h.prodData.π₂ x).2]

end Prod

end AndersenOliverVentura.Tame

