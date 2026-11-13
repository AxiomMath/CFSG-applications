import CFSGOutside.Baddeley.Centralizer
import CFSGOutside.Common.NonsolubleLength

/-!
# A minimal normal subgroup of `H` meeting `M C_G(M)` trivially

In the proof of Lemma 6.2 (p. 232), Baddeley treats the case `M' ∩ (M × C_G(M)) = 1`, where `M'` is a regular
nonabelian minimal normal subgroup of `H ≤ G`. Then `M'` embeds in `G/(M × C_G(M)) ≤ Out(T) ≀ S_k`, and the paper
uses Teague's theorem and the Schreier conjecture to reach a contradiction with `|M'| = |M| = |T|^k`.

We avoid Teague's theorem. Put `Y = G/C_G(M)`, which contains `M̄ ≅ M` with `C_Y(M̄) = 1`. Then `F(Y) = 1`, every
component of `Y` lies in `M̄`, and the kernel `K` of the action of `Y` on its components is soluble modulo the layer
`E(Y)`: this is the Schreier conjecture, through `dA_kernel_le_layer`. The image `M̄'` of `M'` meets `M̄` trivially,
so `M̄' ∩ K` is soluble and normalized by `H`; by minimality it is trivial. Hence `M'` embeds in the symmetric group
on the `k ≥ 1` components and `|M'|` divides `k!`. Each component has even order by Feit–Thompson, so `2^k` divides
`|E(Y)|`, which divides `|M̄| = |M|`. If `|M'| = |M|` then `2^k` divides `k!`, which is false.
-/

namespace CFSGOutside.Baddeley

open Subgroup CFSGOutside.Corpus CFSGOutside.Corpus.LocalCores CFSGOutside.NonsolubleLength

section Lemmas

variable {X : Type*} [Group X]

/-- A subgroup normalized by `H`, intersected with a normal subgroup, is normalized by `H`. -/
theorem le_normalizer_inf {A B H : Subgroup X} (hA : H ≤ normalizer (A : Set X)) (hB : B.Normal) :
    H ≤ normalizer ((A ⊓ B : Subgroup X) : Set X) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro x
  have h1 := mem_normalizer_iff.1 (hA hg) x
  have h2 : x ∈ B ↔ g * x * g⁻¹ ∈ B :=
    ⟨fun hx => hB.conj_mem x hx g, fun hx => by simpa [mul_assoc] using hB.conj_mem _ hx g⁻¹⟩
  simp only [mem_inf]
  exact and_congr h1 h2

theorem not_isSolvable_of_isMinimalNormalIn [Finite X] {N K : Subgroup X}
    (hN : IsMinimalNormalIn N K) (hna : IsNonabelian N) : ¬ Group.IsSolvable N := by
  intro hs
  have hle : ⁅N, N⁆ ≤ N := dA_le 1 N
  have hnorm : K ≤ normalizer ((⁅N, N⁆ : Subgroup X) : Set X) := by
    intro k hk
    apply mem_normalizer_of_map_conj_eq
    rw [map_commutator, map_conj_eq_of_mem_normalizer (hN.2.1 hk)]
  rcases hN.2.2.2 _ hle hnorm with h | h
  · obtain ⟨a, ha, b, hb, hab⟩ := hna
    apply hab
    have := commutator_mem_commutator ha hb
    rwa [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
  · obtain ⟨k, hk⟩ := (isSolvable_subgroup_iff N).1 hs
    have hd : ∀ n, dA n N = N := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [dA, ih, h]
    exact hN.2.2.1 (by rw [← hd k, hk])

/-- The restriction of a homomorphism to a subgroup on which it is injective. -/
theorem card_map_of_injOn {Y : Type*} [Group Y] (f : X →* Y) {S : Subgroup X}
    (h : ∀ a ∈ S, f a = 1 → a = 1) : Nat.card (S.map f) = Nat.card S := by
  symm
  refine Nat.card_eq_of_bijective (fun s : S => (⟨f s, mem_map_of_mem f s.2⟩ : S.map f)) ⟨?_, ?_⟩
  · intro a b hab
    have hab' : f a = f b := congrArg Subtype.val hab
    have h1 : f ((a : X)⁻¹ * b) = 1 := by rw [map_mul, map_inv, hab', inv_mul_cancel]
    exact Subtype.ext (inv_mul_eq_one.1 (h _ (mul_mem (inv_mem a.2) b.2) h1))
  · rintro ⟨_, s, hs, rfl⟩
    exact ⟨⟨s, hs⟩, rfl⟩

theorem isSolvable_of_map {Y : Type*} [Group Y] (f : X →* Y) {S : Subgroup X}
    (h : ∀ a ∈ S, f a = 1 → a = 1) (hs : Group.IsSolvable (S.map f)) : Group.IsSolvable S := by
  let g : S →* S.map f := (f.comp S.subtype).codRestrict (S.map f) fun s => mem_map_of_mem f s.2
  refine solvable_of_solvable_injective (f := g) fun a b hab => ?_
  have hab' : f a = f b := congrArg Subtype.val hab
  have h1 : f ((a : X)⁻¹ * b) = 1 := by rw [map_mul, map_inv, hab', inv_mul_cancel]
  exact Subtype.ext (inv_mul_eq_one.1 (h _ (mul_mem (inv_mem a.2) b.2) h1))

end Lemmas

section Perm

variable {Y : Type} [Group Y] [Finite Y]

/-- Conjugation by `y`, permuting the components of `Y`. -/
noncomputable def componentPerm : Y →* Equiv.Perm (ComponentIndex Y) where
  toFun y :=
    { toFun := fun C => ⟨C.1.map (MulAut.conj y).toMonoidHom, isComponent_conj C.2 y⟩
      invFun := fun C => ⟨C.1.map (MulAut.conj y⁻¹).toMonoidHom, isComponent_conj C.2 y⁻¹⟩
      left_inv := fun C => Subtype.ext (by
        simp only [map_map, conj_comp_conj, inv_mul_cancel]
        ext x; simp)
      right_inv := fun C => Subtype.ext (by
        simp only [map_map, conj_comp_conj, mul_inv_cancel]
        ext x; simp) }
  map_one' := by
    ext C x
    simp
  map_mul' a b := by
    ext C x
    simp only [Equiv.coe_fn_mk, Equiv.Perm.coe_mul, Function.comp_apply, map_map, conj_comp_conj]

theorem mem_kernelOf_of_componentPerm_eq_one {y : Y} (hy : componentPerm y = 1) :
    y ∈ kernelOf (components Y) := by
  refine mem_kernelOf.2 fun S hS => mem_normalizer_of_map_conj_eq ?_
  have := congrArg Subtype.val (Equiv.ext_iff.1 hy ⟨S, hS⟩)
  exact this

end Perm

section Main

variable {X : Type} [Group X] [Finite X]

theorem card_ne_of_inf_sup_centralizer_eq_bot [Schreier] [OddOrder.{0}]
    (hCFSG : TauCeti.ClassificationStatement.{0}) {M H M' : Subgroup X}
    (hM : IsMinimalNormalIn M ⊤) (hMna : IsNonabelian M)
    (hM' : IsMinimalNormalIn M' H) (hM'na : IsNonabelian M')
    (hdisj : M' ⊓ (M ⊔ centralizer (M : Set X)) = ⊥) : Nat.card M' ≠ Nat.card M := by
  intro hcard
  haveI hMn : M.Normal := normal_of_top_le hM.2.1
  set C := centralizer (M : Set X) with hC
  have hZ : M ⊓ C = ⊥ := inf_centralizer_eq_bot hM hMna
  set π : X →* X ⧸ C := QuotientGroup.mk' C
  set M₁ := M.map π
  set M₁' := M'.map π
  have hπM : ∀ a ∈ M, π a = 1 → a = 1 := fun a ha h1 => by
    have : a ∈ M ⊓ C := ⟨ha, (QuotientGroup.eq_one_iff a).1 h1⟩
    rwa [hZ, mem_bot] at this
  have hπM' : ∀ a ∈ M', π a = 1 → a = 1 := fun a ha h1 => by
    have : a ∈ M' ⊓ (M ⊔ C) := ⟨ha, mem_sup_right ((QuotientGroup.eq_one_iff a).1 h1)⟩
    rwa [hdisj, mem_bot] at this
  have hcardM := card_map_of_injOn π hπM
  have hcardM' := card_map_of_injOn π hπM'
  have hM₁n : M₁.Normal := hMn.map π (QuotientGroup.mk'_surjective C)
  -- `C_Y(M̄) = 1`.
  have hCY : centralizer (M₁ : Set (X ⧸ C)) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective C y
    rw [mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hC, mem_centralizer_iff]
    intro m hm
    have h1 : π m * π g = π g * π m := mem_centralizer_iff.1 hy (π m) (mem_map_of_mem π hm)
    rw [← map_mul, ← map_mul] at h1
    have h2 : (m * g)⁻¹ * (g * m) ∈ C := QuotientGroup.eq.1 h1
    have h3 : (m * g)⁻¹ * (g * m) ∈ M := by
      have : (m * g)⁻¹ * (g * m) = g⁻¹ * m⁻¹ * g⁻¹⁻¹ * m := by group
      rw [this]
      exact mul_mem (hMn.conj_mem _ (inv_mem hm) g⁻¹) hm
    have h4 : (m * g)⁻¹ * (g * m) ∈ M ⊓ C := ⟨h3, h2⟩
    rw [hZ, mem_bot] at h4
    exact inv_mul_eq_one.1 h4
  -- `M̄` is a minimal normal subgroup of `Y`.
  have hM₁min : ∀ N : Subgroup (X ⧸ C), N.Normal → N ≤ M₁ → N = ⊥ ∨ N = M₁ := by
    intro N hN hNM
    haveI := hN
    rcases hM.2.2.2 (M ⊓ N.comap π) inf_le_left (top_le_normalizer inferInstance) with h | h
    · left
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨m, hm, rfl⟩ := hNM hx
      have : m ∈ M ⊓ N.comap π := ⟨hm, hx⟩
      rw [h, mem_bot] at this
      rw [this, map_one]
      exact one_mem _
    · right
      refine le_antisymm hNM ?_
      rintro _ ⟨m, hm, rfl⟩
      have : m ∈ M ⊓ N.comap π := by rw [h]; exact hm
      exact this.2
  have hMns : ¬ Group.IsSolvable M := not_isSolvable_of_isMinimalNormalIn hM hMna
  -- `F(Y) = 1`.
  have hF : fittingSubgroup (X ⧸ C) = ⊥ := by
    refine sSup_eq_bot.2 fun N ⟨hN, hNnil⟩ => ?_
    haveI := hN
    rcases hM₁min (N ⊓ M₁) inferInstance inf_le_right with h | h
    · rw [eq_bot_iff, ← hCY]
      intro x hx
      rw [mem_centralizer_iff]
      intro m hm
      have hc1 : x * m * x⁻¹ * m⁻¹ ∈ N := by
        have := mul_mem hx (hN.conj_mem x⁻¹ (inv_mem hx) m)
        simpa [mul_assoc] using this
      have hc : x * m * x⁻¹ * m⁻¹ ∈ N ⊓ M₁ :=
        mem_inf.2 ⟨hc1, M₁.mul_mem (hM₁n.conj_mem m hm x) (M₁.inv_mem hm)⟩
      rw [h, mem_bot] at hc
      have h1 : x * m * x⁻¹ = m := mul_inv_eq_one.1 hc
      calc m * x = x * m * x⁻¹ * x := by rw [h1]
        _ = x * m := by group
    · exfalso
      apply hMns
      refine isSolvable_of_map π hπM ?_
      have hle : M₁ ≤ N := by rw [← h]; exact inf_le_left
      exact isSolvable_of_le hle inferInstance
  -- Every component lies in `M̄`.
  have hcompM : ∀ L : Subgroup (X ⧸ C), IsComponent L → L ≤ M₁ := by
    intro L hL
    rcases component_normal_subgroup hL hM₁n with h | h
    · exact h
    · exfalso
      have hLC := commutator_eq_bot_iff_le_centralizer.1 h
      rw [hCY] at hLC
      haveI := isQuasisimple_nontrivial hL.1
      exact (Subgroup.nontrivial_iff_ne_bot L).1 inferInstance (le_bot_iff.1 hLC)
  have hlayer : layer (X ⧸ C) ≤ M₁ := sSup_le fun L hL => hcompM L hL
  -- The kernel of the action on components.
  set K := kernelOf (components (X ⧸ C))
  haveI hKn : K.Normal := kernelOf_normal fun S hS g => isComponent_conj hS g
  obtain ⟨j, hj⟩ := dA_kernel_le_layer hF hCFSG
  have hM₁M₁' : M₁' ⊓ M₁ = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨m', hm', rfl⟩, ⟨m, hm, hmm⟩⟩
    have h1 : m'⁻¹ * m ∈ C := QuotientGroup.eq.1 hmm.symm
    have h2 : m' ∈ M' ⊓ (M ⊔ C) := by
      refine ⟨hm', ?_⟩
      have : m' = m * (m'⁻¹ * m)⁻¹ := by group
      rw [this]
      exact mul_mem (mem_sup_left hm) (mem_sup_right (inv_mem h1))
    rw [hdisj, mem_bot] at h2
    rw [h2, map_one]
    exact one_mem _
  have hKM₁' : M₁' ⊓ K = ⊥ := by
    rcases hM'.2.2.2 (M' ⊓ K.comap π) inf_le_left (le_normalizer_inf hM'.2.1 inferInstance) with h | h
    · rw [eq_bot_iff]
      rintro _ ⟨⟨m', hm', rfl⟩, hk⟩
      have : m' ∈ M' ⊓ K.comap π := ⟨hm', hk⟩
      rw [h, mem_bot] at this
      rw [this, map_one]
      exact one_mem _
    · exfalso
      apply not_isSolvable_of_isMinimalNormalIn hM' hM'na
      refine isSolvable_of_map π hπM' ((isSolvable_subgroup_iff _).2 ⟨j, ?_⟩)
      have hle : M₁' ≤ K := by
        rintro _ ⟨m', hm', rfl⟩
        have : m' ∈ M' ⊓ K.comap π := by rw [h]; exact hm'
        exact this.2
      rw [eq_bot_iff, ← hM₁M₁']
      exact le_inf (dA_le j _) ((dA_mono j hle).trans (hj.trans hlayer))
  -- `M̄'` permutes the components faithfully.
  have hinj : Function.Injective ((componentPerm (Y := X ⧸ C)).comp M₁'.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hxK : (x : X ⧸ C) ∈ M₁' ⊓ K := ⟨x.2, mem_kernelOf_of_componentPerm_eq_one hx⟩
    rw [hKM₁', mem_bot] at hxK
    exact mem_bot.2 (Subtype.ext hxK)
  have hdvd1 : Nat.card M₁' ∣ (Nat.card (ComponentIndex (X ⧸ C))).factorial := by
    rw [← Nat.card_perm]
    exact card_dvd_of_injective _ hinj
  -- `2^k` divides `|E(Y)|`, which divides `|M̄|`.
  have hZc : ∀ L : ComponentIndex (X ⧸ C), center L.1 = ⊥ := fun L => component_center_eq_bot hF L.2
  have hcardE : Nat.card (layer (X ⧸ C)) = ∏ L : ComponentIndex (X ⧸ C), Nat.card L.1 := by
    rw [← Nat.card_congr (layerEquiv hZc).toEquiv, Nat.card_pi]
  have hdvd2 : 2 ^ Nat.card (ComponentIndex (X ⧸ C)) ∣ Nat.card M₁ := by
    refine dvd_trans ?_ (card_dvd_of_le hlayer)
    rw [hcardE, Nat.card_eq_fintype_card, ← Finset.card_univ, ← Finset.prod_const]
    refine Finset.prod_dvd_prod_of_dvd _ _ fun L _ => ?_
    haveI := component_isSimple hF L.2
    exact two_dvd_card_of_not_isSolvable (not_isSolvable_of_simple_nonab (nonab_component hF L))
  -- At least one component.
  have hk : Nat.card (ComponentIndex (X ⧸ C)) ≠ 0 := by
    intro h0
    haveI : IsEmpty (ComponentIndex (X ⧸ C)) := (Nat.card_eq_zero.1 h0).resolve_right (not_infinite_iff_finite.2 inferInstance)
    have hl : layer (X ⧸ C) = ⊥ := layer_eq_bot_of_forall fun L hL => isEmptyElim (⟨L, hL⟩ : ComponentIndex (X ⧸ C))
    have hc := centralizer_layer_eq_bot hF
    rw [hl] at hc
    obtain ⟨a, ha, b, hb, hab⟩ := hMna
    have hπa : π a = 1 := by
      have : π a ∈ centralizer ((⊥ : Subgroup (X ⧸ C)) : Set (X ⧸ C)) := by
        rw [mem_centralizer_iff]
        intro h hh
        rw [SetLike.mem_coe, mem_bot] at hh
        rw [hh, one_mul, mul_one]
      rwa [hc, mem_bot] at this
    rw [hπM a ha hπa, one_mul, mul_one] at hab
    exact hab rfl
  have hdvd : 2 ^ Nat.card (ComponentIndex (X ⧸ C)) ∣ (Nat.card (ComponentIndex (X ⧸ C))).factorial := by
    rw [hcardM', hcard, ← hcardM] at hdvd1
    exact hdvd2.trans hdvd1
  have := Nat.emultiplicity_two_factorial_lt hk
  rw [← not_le] at this
  exact this (pow_dvd_iff_le_emultiplicity.1 hdvd)

end Main

end CFSGOutside.Baddeley
