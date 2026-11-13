import CFSGOutside.Common.Components

/-!
# Wilson, compact torsion groups: the orbit argument of Lemma 4(i)

**Paper.** J. S. Wilson, *On the structure of compact torsion groups*, Monatsh. Math. **96** (1983), 57–66,
Lemma 4(i) (p. 63) and its proof (p. 64).

For a finite group `Y` with trivial Fitting subgroup, the layer `E(Y)` is the direct product of the components of
`Y` (`layerEquiv`), and `proj C` is the projection of `E(Y)` onto the component `C`. `map_pow_eq_of_prod` is the
heart of Lemma 4(i): if an automorphism `σ` with `σ ^ (p ^ (a + 1)) = 1` moves a component `C` under `σ ^ (p ^ a)`,
the `⟨σ⟩`-orbit of `C` has length `p ^ (a + 1)`, and a product `σ(h) σ²(h) ⋯ σ^{p^{a+1}}(h) = 1` with
`1 ≠ h ∈ C` projects to `h` in the `C`-coordinate, a contradiction.
-/

namespace CFSGOutside.Wilson

open Subgroup CFSGOutside.Corpus CFSGOutside.Corpus.LocalCores

section Coordinates

variable {Y : Type} [Group Y] [Finite Y]

/-- The projection of the layer `E(Y)`, identified with the product of the components, onto the component `C`,
as a homomorphism. -/
noncomputable def coord (hZ : ∀ C : ComponentIndex Y, center C.1 = ⊥) (C : ComponentIndex Y) :
    layer Y →* C.1 :=
  (Pi.evalMonoidHom (fun C : ComponentIndex Y => C.1) C).comp (layerEquiv hZ).symm.toMonoidHom

variable (hZ : ∀ C : ComponentIndex Y, center C.1 = ⊥)

/-- The `C`-coordinate of an element `x` of the layer, as an element of `Y`. -/
noncomputable def proj (C : ComponentIndex Y) (x : Y) (hx : x ∈ layer Y) : Y :=
  ((coord hZ C ⟨x, hx⟩ : C.1) : Y)

variable {hZ}

theorem coord_layerMulOnto (C : ComponentIndex Y) (x : ∀ C : ComponentIndex Y, C.1) :
    coord hZ C (layerMulOnto Y x) = x C := by
  have h : layerEquiv hZ x = layerMulOnto Y x := rfl
  have h2 : (layerEquiv hZ).symm (layerMulOnto Y x) = x := by
    rw [← h]
    exact (layerEquiv hZ).symm_apply_apply x
  show ((layerEquiv hZ).symm (layerMulOnto Y x)) C = x C
  rw [h2]

theorem proj_mul (C : ComponentIndex Y) {x y : Y} (hx : x ∈ layer Y) (hy : y ∈ layer Y) :
    proj hZ C (x * y) (mul_mem hx hy) = proj hZ C x hx * proj hZ C y hy := by
  have := map_mul (coord hZ C) ⟨x, hx⟩ ⟨y, hy⟩
  exact congrArg Subtype.val this

theorem proj_one (C : ComponentIndex Y) : proj hZ C 1 (one_mem _) = 1 := by
  have := map_one (coord hZ C)
  exact congrArg Subtype.val this

theorem proj_of_mem (C : ComponentIndex Y) {c : Y} (hc : c ∈ C.1) :
    proj hZ C c (component_le_layer C.2 hc) = c := by
  have h1 : layerMulOnto Y (Pi.mulSingle C ⟨c, hc⟩) = ⟨c, component_le_layer C.2 hc⟩ :=
    Subtype.ext (layerMul_mulSingle C ⟨c, hc⟩)
  have := coord_layerMulOnto (hZ := hZ) C (Pi.mulSingle C ⟨c, hc⟩)
  rw [h1] at this
  have h2 := congrArg Subtype.val this
  rw [Pi.mulSingle_eq_same] at h2
  unfold proj
  exact h2

theorem proj_of_mem_of_ne {C C' : ComponentIndex Y} (hne : C' ≠ C) {c : Y} (hc : c ∈ C'.1) :
    proj hZ C c (component_le_layer C'.2 hc) = 1 := by
  have h1 : layerMulOnto Y (Pi.mulSingle C' ⟨c, hc⟩) = ⟨c, component_le_layer C'.2 hc⟩ :=
    Subtype.ext (layerMul_mulSingle C' ⟨c, hc⟩)
  have := coord_layerMulOnto (hZ := hZ) C (Pi.mulSingle C' ⟨c, hc⟩)
  rw [h1] at this
  have h2 := congrArg Subtype.val this
  rw [Pi.mulSingle_eq_of_ne (Ne.symm hne)] at h2
  unfold proj
  exact h2

end Coordinates

section Orbit

variable {Y : Type} [Group Y] [Finite Y]

theorem iterate_map_eq (σ : MulAut Y) (j : ℕ) (D : Subgroup Y) :
    (fun D : Subgroup Y => D.map σ.toMonoidHom)^[j] D = D.map (σ ^ j).toMonoidHom := by
  induction j generalizing D with
  | zero => ext x; simp
  | succ j ih =>
    rw [Function.iterate_succ_apply, ih, Subgroup.map_map, pow_succ]
    rfl

/-- **The orbit argument of Lemma 4(i).** Let `σ` be an automorphism of `Y` with
`σ^(p^(a+1)) = 1`, let `C` be a component and `1 ≠ h ∈ C`. If the products
`w m = σ(h) σ²(h) ⋯ σ^m(h)` satisfy `w (p^(a+1)) = 1`, then `σ^(p^a)` normalises `C`. -/
theorem map_pow_eq_of_prod (hZ : ∀ C : ComponentIndex Y, center C.1 = ⊥)
    {p : ℕ} (hp : p.Prime) {a : ℕ} (σ : MulAut Y) (hσ : σ ^ (p ^ (a + 1)) = 1)
    (C : ComponentIndex Y) {h : Y} (hhC : h ∈ C.1) (hh1 : h ≠ 1) (w : ℕ → Y) (hw0 : w 0 = 1)
    (hws : ∀ m, w (m + 1) = w m * (σ ^ (m + 1)) h) (hwn : w (p ^ (a + 1)) = 1) :
    C.1.map (σ ^ (p ^ a)).toMonoidHom = C.1 := by
  set n := p ^ (a + 1) with hn
  set f : Subgroup Y → Subgroup Y := fun D => D.map σ.toMonoidHom
  by_contra hne
  have hper : Function.IsPeriodicPt f n C.1 := by
    show f^[n] C.1 = C.1
    rw [iterate_map_eq, hσ]
    ext x; simp
  have hmp := hper.minimalPeriod_dvd
  obtain ⟨b, hb, hbeq⟩ := (Nat.dvd_prime_pow hp).mp hmp
  have hba : b = a + 1 := by
    by_contra hba
    have hb' : b ≤ a := by omega
    apply hne
    have : Function.IsPeriodicPt f (p ^ a) C.1 := by
      rw [Function.isPeriodicPt_iff_minimalPeriod_dvd, hbeq]
      exact Nat.pow_dvd_pow p hb'
    have h2 : f^[p ^ a] C.1 = C.1 := this
    rwa [iterate_map_eq] at h2
  have hnot : ∀ j, 0 < j → j < n → C.1.map (σ ^ j).toMonoidHom ≠ C.1 := by
    intro j hj0 hjn hj
    have : Function.IsPeriodicPt f j C.1 := by
      show f^[j] C.1 = C.1
      rw [iterate_map_eq]; exact hj
    exact Function.not_isPeriodicPt_of_pos_of_lt_minimalPeriod hj0.ne'
      (by rw [hbeq, hba]; exact hjn) this
  -- components `σ^j(C)`
  let Cj : ℕ → ComponentIndex Y := fun j =>
    ⟨C.1.map (σ ^ j).toMonoidHom, isComponent_map_mulEquiv (σ ^ j) C.2⟩
  have hgC : ∀ j, (σ ^ j) h ∈ (Cj j).1 := fun j => mem_map_of_mem _ hhC
  have hgL : ∀ j, (σ ^ j) h ∈ layer Y := fun j => component_le_layer (Cj j).2 (hgC j)
  have hnpos : 0 < n := Nat.pow_pos hp.pos
  have hclaim : ∀ m, m < n → ∃ hm : w m ∈ layer Y, proj hZ C (w m) hm = 1 := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨by rw [hw0]; exact one_mem _, ?_⟩
      have := proj_one (hZ := hZ) C
      convert this using 2
    | succ m ih =>
      intro hm
      obtain ⟨hm1, hm2⟩ := ih (by omega)
      have hmem : w (m + 1) ∈ layer Y := by rw [hws]; exact mul_mem hm1 (hgL _)
      refine ⟨hmem, ?_⟩
      have hne' : Cj (m + 1) ≠ C := by
        intro h'
        exact hnot (m + 1) (by omega) hm (congrArg Subtype.val h')
      have h1 := proj_mul (hZ := hZ) C hm1 (hgL (m + 1))
      have h2 := proj_of_mem_of_ne (hZ := hZ) hne' (hgC (m + 1))
      have h3 : proj hZ C (w (m + 1)) hmem = proj hZ C (w m * (σ ^ (m + 1)) h)
          (mul_mem hm1 (hgL (m + 1))) := by
        congr 1; exact hws m
      rw [h3, h1, hm2, h2, one_mul]
  obtain ⟨hm1, hm2⟩ := hclaim (n - 1) (by omega)
  have hσn : (σ ^ n) h = h := by rw [hσ]; rfl
  have hhL : h ∈ layer Y := component_le_layer C.2 hhC
  have hnn : n - 1 + 1 = n := by omega
  have hmemn : w n ∈ layer Y := by rw [hwn]; exact one_mem _
  have h4 : proj hZ C (w n) hmemn = proj hZ C (w (n - 1) * h) (mul_mem hm1 hhL) := by
    congr 1
    rw [← hnn, hws, hnn, hσn]
  rw [proj_mul (hZ := hZ) C hm1 hhL, hm2, one_mul, proj_of_mem (hZ := hZ) C hhC] at h4
  have h5 : proj hZ C (w n) hmemn = 1 := by
    have := proj_one (hZ := hZ) C
    convert this using 2
  exact hh1 (h4.symm.trans h5)

end Orbit

end CFSGOutside.Wilson
