import CFSGOutside.Wilson.Defs

/-!
# Wilson, compact torsion groups: sections of finite groups

**Paper.** J. S. Wilson, *On the structure of compact torsion groups*, Monatsh. Math. **96** (1983), 57–66,
proof of Theorem 2\* (pp. 63–64).

The induction on `a` in the proof of Theorem 2\* pulls the series of `KN/N` back along `H → H/N`
(`section_comap`: `(K ∩ π⁻¹B)/(K ∩ π⁻¹A) ≅ B/A`) and merges two consecutive `p`-soluble sections
(`pSolFactor_trans`).
-/

namespace CFSGOutside.Wilson

open Subgroup CFSGOutside.Corpus

variable {H : Type} [Group H]

/-- The section `B/A` is `p`-soluble. -/
def PSolFactor (p : ℕ) (A B : Subgroup H) : Prop :=
  ∃ _ : (A.subgroupOf B).Normal, IsPSolvable p (B ⧸ A.subgroupOf B)

/-- `𝔖_p`-groups are closed under isomorphism. -/
theorem IsSpProd.of_equiv {p : ℕ} {Y Z : Type} [Group Y] [Group Z] (e : Y ≃* Z)
    (h : IsSpProd p Z) : IsSpProd p Y := by
  obtain ⟨ι, S, _, h1, h2, h3, h4, ⟨f⟩⟩ := h
  exact ⟨ι, S, _, h1, h2, h3, h4, ⟨e.trans f⟩⟩

/-- A surjection `B → Z` with kernel `A ∩ B` identifies `B/A` with `Z`. -/
theorem quot_equiv_of_surj {A B : Subgroup H} [(A.subgroupOf B).Normal] {Z : Type} [Group Z]
    (f : B →* Z) (hf : Function.Surjective f) (hker : f.ker = A.subgroupOf B) :
    Nonempty ((B ⧸ A.subgroupOf B) ≃* Z) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩

/-- **Transport along a surjection.** If `π : H → H'` is surjective, `K ≤ H` and `A ≤ B ≤ π(K)`,
then `(K ∩ π⁻¹B)/(K ∩ π⁻¹A) ≅ B/A`. -/
theorem section_comap {H' : Type} [Group H'] (π : H →* H') (K : Subgroup H)
    {A B : Subgroup H'} (hAB : A ≤ B) (hBK : B ≤ K.map π) [hn : (A.subgroupOf B).Normal] :
    ∃ _ : ((K ⊓ A.comap π).subgroupOf (K ⊓ B.comap π)).Normal,
      Nonempty ((↥(K ⊓ B.comap π) ⧸ (K ⊓ A.comap π).subgroupOf (K ⊓ B.comap π)) ≃*
        (↥B ⧸ A.subgroupOf B)) := by
  set L := K ⊓ B.comap π
  let g : L →* B := (π.comp L.subtype).codRestrict B (fun x => x.2.2)
  let f : L →* B ⧸ A.subgroupOf B := (QuotientGroup.mk' (A.subgroupOf B)).comp g
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk, hkb⟩ := mem_map.mp (hBK b.2)
    refine ⟨⟨k, hk, show π k ∈ B from hkb ▸ b.2⟩, ?_⟩
    show QuotientGroup.mk (g _) = _
    congr 1
    exact Subtype.ext hkb
  have hker : f.ker = (K ⊓ A.comap π).subgroupOf L := by
    ext x
    simp only [f, MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, mem_subgroupOf]
    constructor
    · intro h
      exact ⟨x.2.1, h⟩
    · intro h
      exact h.2
  have hn' : ((K ⊓ A.comap π).subgroupOf L).Normal := hker ▸ f.normal_ker
  exact ⟨hn', quot_equiv_of_surj f hf hker⟩

variable {p : ℕ} [Fact p.Prime]

/-- Composite of two `p`-soluble sections is `p`-soluble. -/
theorem pSolFactor_trans [Finite H] {A B C : Subgroup H} [hA : A.Normal] [hB : B.Normal]
    (hAB : A ≤ B) (hBC : B ≤ C) (h1 : PSolFactor p A B) (h2 : PSolFactor p B C) :
    PSolFactor p A C := by
  obtain ⟨_, h1⟩ := h1
  obtain ⟨_, h2⟩ := h2
  refine ⟨inferInstance, ?_⟩
  set A' := A.subgroupOf C
  set B' := B.subgroupOf C
  have hA'B' : A' ≤ B' := fun x hx => hAB hx
  set Nb := B'.map (QuotientGroup.mk' A')
  have hNb : Nb.Normal := Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective A')
  -- `Nb ≅ B/A`
  let g : B →* Nb := ((QuotientGroup.mk' A').comp (Subgroup.inclusion hBC)).codRestrict Nb
    (fun b => mem_map_of_mem _ (show Subgroup.inclusion hBC b ∈ B' from b.2))
  have hg : Function.Surjective g := by
    rintro ⟨_, ⟨c, hc, rfl⟩⟩
    exact ⟨⟨c, hc⟩, Subtype.ext rfl⟩
  have hgk : g.ker = A.subgroupOf B := by
    ext b
    simp only [g, MonoidHom.mem_ker, mem_subgroupOf]
    rw [Subtype.ext_iff]
    simp only [MonoidHom.codRestrict_apply, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      OneMemClass.coe_one, QuotientGroup.eq_one_iff, A', mem_subgroupOf]
    rfl
  obtain ⟨e1⟩ := quot_equiv_of_surj g hg hgk
  have hNbp : IsPSolvable p Nb := isPSolvable_of_mulEquiv e1 h1
  have hQp : IsPSolvable p ((C ⧸ A') ⧸ Nb) :=
    isPSolvable_of_mulEquiv (QuotientGroup.quotientQuotientEquivQuotient A' B' hA'B').symm h2
  exact isPSolvable_of_normal Nb hNbp hQp

end CFSGOutside.Wilson
