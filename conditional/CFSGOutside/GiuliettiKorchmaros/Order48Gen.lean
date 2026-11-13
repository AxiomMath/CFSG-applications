import Mathlib
import CFSGOutside.GiuliettiKorchmaros.Order48Ext

/-!
# Generic machinery: automorphisms of `SL(2,3)`-like groups and the core outer-element argument
-/

namespace CFSGOutside.GiuliettiKorchmaros.Order48

/-- A relation on pairs of elements that is preserved by injective homomorphisms. -/
def PRel {G : Type*} [Group G] (a b : G) : Prop :=
  a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ (a * b) ^ 4 = 1 ∧ (a * b) ^ 2 ≠ 1 ∧ a ≠ 1 ∧ b ≠ 1

theorem PRel.map {G H : Type*} [Group G] [Group H] (φ : G →* H) (hφ : Function.Injective φ)
    {a b : G} (h : PRel a b) : PRel (φ a) (φ b) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, h1, map_one]
  · rw [← map_pow, h2, map_one]
  · rw [← map_mul, ← map_pow, h3, map_one]
  · rw [← map_mul, ← map_pow]; intro h; exact h4 (hφ (h.trans (map_one φ).symm))
  · intro h; exact h5 (hφ (h.trans (map_one φ).symm))
  · intro h; exact h6 (hφ (h.trans (map_one φ).symm))

theorem hAut_of_pairs {S Y : Type*} [Group S] [Group Y] (f : S →* Y) (s t : S)
    (hgen : Subgroup.closure ({s, t} : Set S) = ⊤) (hP : PRel s t)
    (hpairs : ∀ a b : S, PRel a b →
      ∃ Y₀ : Y, f a = Y₀ * f s * Y₀⁻¹ ∧ f b = Y₀ * f t * Y₀⁻¹)
    (β : S ≃* S) : ∃ Y₀ : Y, ∀ a, f (β a) = Y₀ * f a * Y₀⁻¹ := by
  obtain ⟨Y₀, h1, h2⟩ := hpairs (β s) (β t) (hP.map β.toMonoidHom β.injective)
  refine ⟨Y₀, fun a => ?_⟩
  have key : Set.EqOn (f.comp β.toMonoidHom) ((MulAut.conj Y₀).toMonoidHom.comp f)
      (Subgroup.closure ({s, t} : Set S)) := by
    apply MonoidHom.eqOn_closure
    intro x hx
    rcases hx with rfl | hx
    · simpa using h1
    · rw [Set.mem_singleton_iff] at hx; subst hx; simpa using h2
  have ha : a ∈ Subgroup.closure ({s, t} : Set S) := hgen ▸ Subgroup.mem_top a
  simpa using key ha

theorem core {X Y S : Type*} [Group X] [Group Y] [Group S]
    (J : Subgroup X) (hJ : J.index = 2) (eJ : J ≃* S)
    (hC : Subgroup.centralizer (J : Set X) ≤ J)
    (f : S →* Y) (hf : Function.Injective f)
    (hAut : ∀ β : S ≃* S, ∃ Y₀ : Y, ∀ a, f (β a) = Y₀ * f a * Y₀⁻¹)
    (e : Y) (hCY : ∀ c : Y, (∀ a : S, c * f a = f a * c) → c = 1 ∨ c = e)
    (y : X) (hy : y ∉ J) :
    ∃ Y₀ : Y, Y₀ ∉ f.range ∧
      (∀ j : J, f (eJ ⟨y * j * y⁻¹, (Subgroup.normal_of_index_eq_two hJ).conj_mem _ j.2 y⟩)
        = Y₀ * f (eJ j) * Y₀⁻¹) ∧
      ∃ c : Y, (c = 1 ∨ c = e) ∧ (∀ a : S, c * f a = f a * c) ∧
        f (eJ ⟨y ^ 2, Subgroup.sq_mem_of_index_two hJ y⟩) = Y₀ ^ 2 * c ∧
        ∀ j : J, f (eJ ⟨(y * j) ^ 2, Subgroup.sq_mem_of_index_two hJ _⟩)
          = (Y₀ * f (eJ j)) ^ 2 * c := by
  have hn := Subgroup.normal_of_index_eq_two hJ
  let cy : J ≃* J :=
    { toFun := fun j => ⟨y * j * y⁻¹, hn.conj_mem _ j.2 y⟩
      invFun := fun j => ⟨y⁻¹ * j * y, by simpa using hn.conj_mem _ j.2 y⁻¹⟩
      left_inv := fun j => Subtype.ext (by simp [mul_assoc])
      right_inv := fun j => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  let β : S ≃* S := eJ.symm.trans (cy.trans eJ)
  obtain ⟨Y₀, hY⟩ := hAut β
  have hH : ∀ j : J, f (eJ (cy j)) = Y₀ * f (eJ j) * Y₀⁻¹ := by
    intro j; simpa [β] using hY (eJ j)
  have hcy : ∀ j : J, ((cy j : J) : X) = y * j * y⁻¹ := fun j => rfl
  -- Y₀ is outside the range
  have hout : Y₀ ∉ f.range := by
    rintro ⟨s₀, hs₀⟩
    set j₀ : J := eJ.symm s₀ with hj₀
    have hall : ∀ h : J, y * h * y⁻¹ = j₀ * h * j₀⁻¹ := by
      intro h
      have h1 : cy h = j₀ * h * j₀⁻¹ := by
        apply eJ.injective; apply hf
        rw [hH, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hj₀]
        simp [hs₀]
      exact congrArg Subtype.val h1
    apply hy
    have hmem : (j₀ : X)⁻¹ * y ∈ Subgroup.centralizer (J : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have this : y * h * y⁻¹ = (j₀ : X) * h * (j₀ : X)⁻¹ := hall ⟨h, hh⟩
      have h3 : (j₀ : X) * h * (j₀ : X)⁻¹ * y = y * h := by
        rw [← this]; group
      calc h * ((j₀ : X)⁻¹ * y) = (j₀ : X)⁻¹ * ((j₀ : X) * h * (j₀ : X)⁻¹ * y) := by group
        _ = (j₀ : X)⁻¹ * (y * h) := by rw [h3]
        _ = _ := by group
    have := hC hmem
    have h4 := J.mul_mem j₀.2 this
    simpa using h4
  refine ⟨Y₀, hout, fun j => hH j, ?_⟩
  set z : J := ⟨y ^ 2, Subgroup.sq_mem_of_index_two hJ y⟩ with hz
  set Z : Y := f (eJ z) with hZdef
  have hZ : ∀ j : J, Z * f (eJ j) * Z⁻¹ = Y₀ * Y₀ * f (eJ j) * Y₀⁻¹ * Y₀⁻¹ := by
    intro j
    have e1 : z * j * z⁻¹ = cy (cy j) := Subtype.ext (by simp [hz, hcy, pow_two, mul_assoc])
    have := congrArg (fun w => f (eJ w)) e1
    simp only [map_mul, map_inv] at this
    rw [this, hH, hH]; group
  have hcomm : ∀ a : S, (Y₀ ^ 2)⁻¹ * Z * f a = f a * ((Y₀ ^ 2)⁻¹ * Z) := by
    intro a
    obtain ⟨j, rfl⟩ := eJ.surjective a
    have h1 := hZ j
    have : Z * f (eJ j) = Y₀ * Y₀ * f (eJ j) * Y₀⁻¹ * Y₀⁻¹ * Z := by
      rw [← h1]; group
    rw [mul_assoc, this]; group
  have hc := hCY _ hcomm
  refine ⟨(Y₀ ^ 2)⁻¹ * Z, hc, hcomm, by group, ?_⟩
  intro j
  have e1 : (⟨(y * j) ^ 2, Subgroup.sq_mem_of_index_two hJ _⟩ : J) = cy j * z * j :=
    Subtype.ext (by simp [hz, hcy, pow_two, mul_assoc])
  rw [e1]
  simp only [map_mul]
  rw [hH]
  have hZc : Z = Y₀ ^ 2 * ((Y₀ ^ 2)⁻¹ * Z) := by group
  set c := (Y₀ ^ 2)⁻¹ * Z with hcdef
  have hcj := hcomm (eJ j)
  rw [show f (eJ z) = Y₀ ^ 2 * c from hZc]
  calc Y₀ * f (eJ j) * Y₀⁻¹ * (Y₀ ^ 2 * c) * f (eJ j)
      = Y₀ * f (eJ j) * Y₀⁻¹ * Y₀ ^ 2 * (c * f (eJ j)) := by group
    _ = Y₀ * f (eJ j) * Y₀⁻¹ * Y₀ ^ 2 * (f (eJ j) * c) := by rw [hcj]
    _ = Y₀ * f (eJ j) * Y₀ * f (eJ j) * c := by group
    _ = _ := by rw [pow_two]; simp only [mul_assoc]


/-- Evaluation of a word in two generators. -/
def evalW {G : Type*} [Group G] (s t : G) (w : List Bool) : G :=
  (w.map fun b => if b then s else t).prod

theorem closure_eq_top_of_words {G : Type*} [Group G] (s t : G) (words : List (List Bool))
    (h : ∀ g : G, ∃ w ∈ words, g = evalW s t w) : Subgroup.closure ({s, t} : Set G) = ⊤ := by
  rw [eq_top_iff]
  intro g _
  obtain ⟨w, _, rfl⟩ := h g
  apply Subgroup.list_prod_mem
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨b, _, rfl⟩ := hx
  apply Subgroup.subset_closure
  cases b <;> simp

theorem apply_ext {X Y S : Type*} [Group X] [Group Y] [Group S] [Finite X] [Finite Y]
    (J : Subgroup X) (hJ : J.index = 2) (eJ : J ≃* S)
    (f : S →* Y) (hf : Function.Injective f) (hfi : f.range.index = 2)
    (y : X) (hy : y ∉ J) (Y₀ : Y) (hY₀ : Y₀ ∉ f.range)
    (hconj : ∀ j : J, f (eJ ⟨y * j * y⁻¹, (Subgroup.normal_of_index_eq_two hJ).conj_mem _ j.2 y⟩)
        = Y₀ * f (eJ j) * Y₀⁻¹)
    (hsq : f (eJ ⟨y ^ 2, Subgroup.sq_mem_of_index_two hJ y⟩) = Y₀ ^ 2) :
    Nonempty (X ≃* Y) := by
  refine nonempty_mulEquiv_of_index_two J f.range hJ hfi (eJ.trans (MonoidHom.ofInjective hf))
    y hy Y₀ hY₀ ?_ ?_
  · intro j
    simp only [MulEquiv.trans_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [MonoidHom.ofInjective_apply, MonoidHom.ofInjective_apply]
    exact hconj j
  · simp only [MulEquiv.trans_apply]
    rw [MonoidHom.ofInjective_apply]
    simpa using hsq

end CFSGOutside.GiuliettiKorchmaros.Order48
