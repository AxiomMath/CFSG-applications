import CFSGOutside.AOVTame.Orbit
import CFSGOutside.AOVTame.Defs

/-!
# Strongly tame fusion systems (AOV Definition 2.10)

* `LhatCond p L`: for every finite group `G`, every pair `H ≤ K` of normal subgroups of `G` with
  `K/H ≅ L^m` (`m ≥ 1`), and every `S ∈ Syl_p(G)`, with `F = F_S(G)`,
  `lim^i_{O(F^c)} (Z^K_F / Z^H_F) = 0` for all `i ≥ 2`.
* `InLhat p L`: `L` is a nonabelian finite simple group satisfying `LhatCond p L`
  (the class `𝔏̂(p)`).
* `InGp p G`: all nonabelian composition factors of `G` lie in `𝔏̂(p)` (the class `𝔊(p)`).
  A simple group is a composition factor of `G` iff it is isomorphic to `K/H` for some subnormal
  `K ≤ G` and `H ⊴ K` (Jordan–Hölder: such a chain `H ⊴ K ⊴⊴ G` refines to a composition series),
  which is the form used here.
* `IsStronglyTame p F`: `F` is saturated and tamely realized by some `G ∈ 𝔊(p)`.
-/

namespace AndersenOliverVentura.Tame

open Subgroup CategoryTheory

/-- The vanishing condition defining `𝔏̂(p)`. -/
def LhatCond (p : ℕ) (L : Type) [Group L] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H K : Subgroup G) [H.Normal] [K.Normal], H ≤ K →
    ∀ m : ℕ, 0 < m → Nonempty (K ⧸ H.subgroupOf K ≃* (Fin m → L)) →
      ∀ (S : Sylow p G) (i : ℕ), 2 ≤ i →
        Limits.IsZero (HigherLim.lim (zFunctor (p := p) (S := (S : Subgroup G)) K H) i)

/-- `L ∈ 𝔏̂(p)`. -/
def InLhat (p : ℕ) (L : Type) [Group L] : Prop :=
  Finite L ∧ IsSimpleGroup L ∧ (∃ a b : L, a * b ≠ b * a) ∧ LhatCond p L

/-- `G ∈ 𝔊(p)`: every nonabelian composition factor of `G` lies in `𝔏̂(p)`. -/
def InGp (p : ℕ) (G : Type) [Group G] : Prop :=
  ∀ (K H : Subgroup G), K.IsSubnormal → H ≤ K → ∀ (hN : (H.subgroupOf K).Normal),
    IsSimpleGroup (K ⧸ H.subgroupOf K) → (∃ a b : K ⧸ H.subgroupOf K, a * b ≠ b * a) →
      InLhat p (K ⧸ H.subgroupOf K)

/-- `F` is strongly tame (AOV Definition 2.10(c)). -/
def IsStronglyTame {S : Type} [Group S] [Finite S] (p : ℕ) [Fact p.Prime] (F : FusionSystem S) :
    Prop :=
  F.Saturated p ∧ ∃ (G : Type) (_ : Group G) (_ : Finite G) (T : Sylow p G), InGp p G ∧
    TamelyRealizes p F G T

lemma nontrivial_of_noncomm {L : Type} [Group L] (h : ∃ a b : L, a * b ≠ b * a) : Nontrivial L := by
  obtain ⟨a, b, hab⟩ := h
  exact nontrivial_of_ne a 1 (by rintro rfl; simp at hab)

section Iso
variable {p : ℕ} {L L' : Type} [Group L] [Group L']

lemma LhatCond.of_equiv (h : LhatCond p L) (e : L ≃* L') : LhatCond p L' := by
  intro G _ _ H K _ _ hHK m hm ⟨f⟩ S i hi
  exact h G H K hHK m hm ⟨f.trans (MulEquiv.piCongrRight fun _ => e.symm)⟩ S i hi

lemma InLhat.of_equiv (h : InLhat p L) (e : L ≃* L') : InLhat p L' := by
  obtain ⟨h1, h2, ⟨a, b, hab⟩, h4⟩ := h
  have hne : ∃ a b : L', a * b ≠ b * a :=
    ⟨e a, e b, fun h => hab (e.injective (by simpa using h))⟩
  haveI := nontrivial_of_noncomm hne
  exact ⟨Finite.of_equiv _ e.toEquiv,
    IsSimpleGroup.isSimpleGroup_of_surjective e.toMonoidHom e.surjective, hne, h4.of_equiv e⟩

end Iso

section Quotient
variable {p : ℕ} {G : Type} [Group G] (N : Subgroup G) [N.Normal]

/-- For `H̄ ⊴ K̄ ≤ G/N`, `K/H ≅ K̄/H̄` where `K, H` are the preimages. -/
noncomputable def quotSectionEquiv (K' H' : Subgroup (G ⧸ N)) (hHK : H' ≤ K')
    [(H'.subgroupOf K').Normal] [((H'.comap (QuotientGroup.mk' N)).subgroupOf
      (K'.comap (QuotientGroup.mk' N))).Normal] :
    (K'.comap (QuotientGroup.mk' N)) ⧸ (H'.comap (QuotientGroup.mk' N)).subgroupOf
      (K'.comap (QuotientGroup.mk' N)) ≃* K' ⧸ H'.subgroupOf K' := by
  let π := QuotientGroup.mk' N
  let r : K'.comap π →* K' := (π.comp (K'.comap π).subtype).codRestrict K' (fun x => x.2)
  have hr : Function.Surjective r := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y
    exact ⟨⟨x, hy⟩, rfl⟩
  let f : K'.comap π →* K' ⧸ H'.subgroupOf K' := (QuotientGroup.mk' _).comp r
  have hf : Function.Surjective f := (QuotientGroup.mk'_surjective _).comp hr
  have hker : f.ker = (H'.comap π).subgroupOf (K'.comap π) := by
    ext x
    simp only [f, MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, mem_subgroupOf, mem_comap]
    rfl
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)

/-- `𝔊(p)` is closed under quotients (composition factors of `G/N` are composition factors of
`G`). -/
lemma InGp.quotient (h : InGp p G) : InGp p (G ⧸ N) := by
  intro K' H' hK' hHK hN hsimp hnab
  let π := QuotientGroup.mk' N
  have hK : (K'.comap π).IsSubnormal := hK'.comap π
  have hHK' : H'.comap π ≤ K'.comap π := comap_mono hHK
  have hN' : ((H'.comap π).subgroupOf (K'.comap π)).Normal := by
    constructor
    intro x hx y
    have := hN.conj_mem ⟨π x, x.2⟩ hx ⟨π y, y.2⟩
    simpa [mem_subgroupOf] using this
  let e := quotSectionEquiv N K' H' hHK
  have hna : ∃ a b : (K'.comap π) ⧸ (H'.comap π).subgroupOf (K'.comap π), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    apply e.symm.injective; simpa using h
  haveI := nontrivial_of_noncomm hna
  have hs : IsSimpleGroup ((K'.comap π) ⧸ (H'.comap π).subgroupOf (K'.comap π)) :=
    IsSimpleGroup.isSimpleGroup_of_surjective e.symm.toMonoidHom e.symm.surjective
  exact (h _ _ hK hHK' hN' hs hna).of_equiv e

end Quotient

end AndersenOliverVentura.Tame
