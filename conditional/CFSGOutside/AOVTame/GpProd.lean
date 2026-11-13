import CFSGOutside.AOVTame.StrongTame

/-!
# AOV tameness: `𝔊(p)` is closed under finite products (AOV Lemma 2.11(b))

A nonabelian composition factor `K/H` of `A × B` (with `K` subnormal) is a composition factor of
`A` or of `B`: the image of `K ∩ (A × 1)` in the simple group `K/H` is either everything, and then
`K/H ≅ K_A/H_A` for the preimages under `A → A × B`, or trivial, and then `K/H ≅ K_B/H_B` for the
images under `A × B → B`.
-/

namespace AndersenOliverVentura.Tame

open Subgroup

variable {p : ℕ}

/-- `K/H ≅ Q` for a surjection `K → Q` with kernel `H`. -/
noncomputable def quotEquivOfSurj {G Q : Type*} [Group G] [Group Q] {K H : Subgroup G}
    [(H.subgroupOf K).Normal] (φ : K →* Q) (hs : Function.Surjective φ)
    (hk : φ.ker = H.subgroupOf K) : K ⧸ H.subgroupOf K ≃* Q :=
  (QuotientGroup.quotientMulEquivOfEq hk.symm).trans (QuotientGroup.quotientKerEquivOfSurjective φ hs)

/-- A group isomorphic to a nonabelian composition factor of a group in `𝔊(p)` lies in `𝔏̂(p)`. -/
lemma inLhat_of_section {A : Type} [Group A] (h : InGp p A) {K H : Subgroup A} (hK : K.IsSubnormal)
    (hHK : H ≤ K) [hN : (H.subgroupOf K).Normal] {Q : Type} [Group Q]
    (e : K ⧸ H.subgroupOf K ≃* Q) (hsimple : IsSimpleGroup Q) (hnc : ∃ a b : Q, a * b ≠ b * a) :
    InLhat p Q := by
  have h1 : IsSimpleGroup (K ⧸ H.subgroupOf K) := e.isSimpleGroup
  have h2 : ∃ a b : K ⧸ H.subgroupOf K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnc
    exact ⟨e.symm a, e.symm b, fun hc => hab (e.symm.injective (by simpa using hc))⟩
  exact (h K H hK hHK hN h1 h2).of_equiv e

/-- `𝔊(p)` is invariant under isomorphism. -/
lemma InGp.of_mulEquiv {G G' : Type} [Group G] [Group G'] (h : InGp p G) (e : G ≃* G') :
    InGp p G' := by
  intro K' H' hK' hHK hN hsimple hnc
  let K := K'.comap e.toMonoidHom
  let H := H'.comap e.toMonoidHom
  let φ : K →* K' ⧸ H'.subgroupOf K' := (QuotientGroup.mk' _).comp
    ((e.toMonoidHom.comp K.subtype).codRestrict K' (fun x => x.2))
  have hs : Function.Surjective φ := by
    intro q
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk'_surjective _ q
    exact ⟨⟨e.symm y, by simpa [K] using hy⟩, by simp [φ]⟩
  have hk : φ.ker = H.subgroupOf K := by
    ext x
    simp only [φ, MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, mem_subgroupOf, mem_comap]
    rfl
  haveI : (H.subgroupOf K).Normal := hk ▸ φ.normal_ker
  exact inLhat_of_section h (hK'.comap _) (comap_mono hHK) (quotEquivOfSurj φ hs hk) hsimple hnc

/-- **`𝔊(p)` is closed under binary products.** -/
lemma InGp.prod {A B : Type} [Group A] [Group B] (hA : InGp p A) (hB : InGp p B) :
    InGp p (A × B) := by
  intro K H hK hHK hN hsimple hnc
  let Q := K ⧸ H.subgroupOf K
  let Ka : Subgroup (A × B) := K ⊓ (MonoidHom.snd A B).ker
  have memKa : ∀ z : A × B, z ∈ Ka ↔ z ∈ K ∧ z.2 = 1 := fun z => Iff.rfl
  haveI : (Ka.subgroupOf K).Normal := by
    constructor
    intro x hx g
    rw [mem_subgroupOf, memKa] at hx ⊢
    refine ⟨(g * x * g⁻¹).2, ?_⟩
    simp [hx.2]
  let M : Subgroup Q := (Ka.subgroupOf K).map (QuotientGroup.mk' _)
  have hM : M.Normal := Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  haveI := hM
  haveI := hsimple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M with hbot | htop
  · -- `K ∩ (A × 1) ≤ H`: use the images in `B`
    have hKa : Ka ≤ H := by
      intro k hk
      have hkK := ((memKa k).1 hk).1
      have : (QuotientGroup.mk' (H.subgroupOf K) ⟨k, hkK⟩ : Q) ∈ M := ⟨⟨k, hkK⟩, hk, rfl⟩
      rw [hbot, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
      exact this
    let K' := K.map (MonoidHom.snd A B)
    let H' := H.map (MonoidHom.snd A B)
    haveI hN' : (H'.subgroupOf K').Normal := by
      constructor
      rintro ⟨_, k₁, hk₁, rfl⟩ ⟨h, hh, e⟩ ⟨_, k, hk, rfl⟩
      refine ⟨k * h * k⁻¹, ?_, ?_⟩
      · have := hN.conj_mem ⟨h, hHK hh⟩ hh ⟨k, hk⟩
        exact this
      · have e' : h.2 = k₁.2 := e
        change (k * h * k⁻¹).2 = k.2 * k₁.2 * k.2⁻¹
        rw [Prod.snd_mul, Prod.snd_mul, Prod.snd_inv, e']
    let φ : K →* K' ⧸ H'.subgroupOf K' := (QuotientGroup.mk' _).comp
      (((MonoidHom.snd A B).comp K.subtype).codRestrict K' (fun x => ⟨x, x.2, rfl⟩))
    have hs : Function.Surjective φ := by
      intro q
      obtain ⟨⟨_, k, hk, rfl⟩, rfl⟩ := QuotientGroup.mk'_surjective _ q
      exact ⟨⟨k, hk⟩, rfl⟩
    have hk : φ.ker = H.subgroupOf K := by
      ext k
      rw [MonoidHom.mem_ker, mem_subgroupOf]
      change (QuotientGroup.mk (_ : K') : K' ⧸ H'.subgroupOf K') = 1 ↔ _
      rw [QuotientGroup.eq_one_iff, mem_subgroupOf]
      constructor
      · rintro ⟨h, hh, e⟩
        have e' : h.2 = (k : A × B).2 := e
        have h1 : (k : A × B) * h⁻¹ ∈ Ka := (memKa _).2 ⟨mul_mem k.2 (inv_mem (hHK hh)), by
          rw [Prod.snd_mul, Prod.snd_inv, e', mul_inv_cancel]⟩
        have := mul_mem (hKa h1) hh
        simpa using this
      · intro hk
        exact ⟨k, hk, rfl⟩
    exact inLhat_of_section hB (hK.map Prod.snd_surjective) (map_mono hHK)
      ((quotEquivOfSurj φ hs hk).symm) hsimple hnc
  · -- `K = (K ∩ (A × 1)) H`: use the preimages in `A`
    let K' := K.comap (MonoidHom.inl A B)
    let H' := H.comap (MonoidHom.inl A B)
    let φ : K' →* Q := (QuotientGroup.mk' _).comp
      (((MonoidHom.inl A B).comp K'.subtype).codRestrict K (fun x => x.2))
    have hs : Function.Surjective φ := by
      intro q
      have : q ∈ M := htop ▸ mem_top q
      obtain ⟨⟨k, hkK⟩, hk, rfl⟩ := this
      have hk' : k ∈ Ka := hk
      rw [memKa] at hk'
      have hk1 : k = (k.1, 1) := Prod.ext rfl hk'.2
      refine ⟨⟨k.1, ?_⟩, ?_⟩
      · show ((k.1, 1) : A × B) ∈ K
        rw [← hk1]; exact hkK
      · exact congrArg (QuotientGroup.mk' (H.subgroupOf K))
          (Subtype.ext hk1.symm : (⟨(k.1, 1), by rw [← hk1]; exact hkK⟩ : K) = ⟨k, hkK⟩)
    have hk : φ.ker = H'.subgroupOf K' := by
      ext x
      rw [MonoidHom.mem_ker, mem_subgroupOf]
      change (QuotientGroup.mk (_ : K) : Q) = 1 ↔ _
      rw [QuotientGroup.eq_one_iff, mem_subgroupOf]
      rfl
    haveI : (H'.subgroupOf K').Normal := hk ▸ φ.normal_ker
    exact inLhat_of_section hA (hK.comap _) (comap_mono hHK) (quotEquivOfSurj φ hs hk) hsimple hnc

/-- The trivial group lies in `𝔊(p)`. -/
lemma inGp_of_subsingleton {G : Type} [Group G] [Subsingleton G] : InGp p G := by
  intro K H _ _ _ hsimple _
  exfalso
  haveI : Subsingleton (K ⧸ H.subgroupOf K) := by
    constructor
    intro a b
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    rw [Subsingleton.elim a b]
  exact (not_subsingleton _) (inferInstance : Subsingleton (K ⧸ H.subgroupOf K))

/-- `K_0 × ∏_{i ≥ 1} K_i ≃ ∏_i K_i`. -/
def consMulEquiv {n : ℕ} (K : Fin (n + 1) → Type) [∀ i, Group (K i)] :
    K 0 × (∀ i : Fin n, K i.succ) ≃* ∀ i, K i where
  toEquiv := Fin.consEquiv K
  map_mul' x y := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [Fin.consEquiv]
    · simp [Fin.consEquiv]

/-- **`𝔊(p)` is closed under finite products.** -/
theorem inGp_pi_fin : ∀ (n : ℕ) (K : Fin n → Type) [∀ i, Group (K i)],
    (∀ i, InGp p (K i)) → InGp p (∀ i, K i)
  | 0, K, _, _ => inGp_of_subsingleton
  | n + 1, K, _, h =>
    ((h 0).prod (inGp_pi_fin n (fun i => K i.succ) (fun i => h i.succ))).of_mulEquiv
      (consMulEquiv K)

/-- `(ι → H) ≃ (ι' → H)` along `ι ≃ ι'`. -/
def arrowCongrMul {ι ι' : Type} (e : ι ≃ ι') (H : Type) [Group H] : (ι → H) ≃* (ι' → H) where
  toFun f := f ∘ e.symm
  invFun g := g ∘ e
  left_inv f := by funext i; simp
  right_inv g := by funext i; simp
  map_mul' _ _ := rfl

lemma InGp.pow {H : Type} [Group H] (h : InGp p H) (ι : Type) [Fintype ι] : InGp p (ι → H) :=
  (inGp_pi_fin (Fintype.card ι) (fun _ => H) (fun _ => h)).of_mulEquiv
    (arrowCongrMul (Fintype.equivFin ι).symm H)

end AndersenOliverVentura.Tame
